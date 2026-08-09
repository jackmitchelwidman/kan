(* ============================================================================
   Kan type-theory surface — a readable syntax for lib/core.ml.
   ----------------------------------------------------------------------------
   Lets you WRITE dependent types and proofs (instead of hand-building de Bruijn
   ASTs) and check them:  `kan check file.ktt`.

   Grammar (whitespace-insensitive; -- comments), tokens shown bare:
     program ::= decl*
     decl    ::= def name (: term)? = term        a checked definition
               | check term                        infer & print type + normal form
               | eval  term                        print the normal form
     term    ::= \ name+ . term                    lambda
               | ( name : term ) -> term           dependent function type
               | ( name : term ) *  term           dependent pair type (Sigma)
               | app ( -> term )?                   non-dependent function type
               | app ( *  term )?                   non-dependent pair type
     app     ::= atom atom*                         application (left assoc)
               | Id atom atom atom                  identity type
               | transp atom atom atom atom atom atom   transport
               | fst atom  |  snd atom
     atom    ::= U | Type | refl | name
               | ( term ) | ( term , term )         grouping / pair
   ========================================================================== *)

open Core

(* -------- tokens -------- *)
type tok = LP | RP | ARR | STAR | COMMA | COLON | DOT | LAM | EQ | FATARROW | BAR | LBRACE | RBRACE | ID of string | NUM of int | INTLIT of string | STR of string | EOF

let tokenize (s : string) : tok array =
  let n = String.length s in
  let out = ref [] in
  let i = ref 0 in
  let push t = out := t :: !out in
  let is_a c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_' || (c >= '0' && c <= '9') in
  while !i < n do
    let c = s.[!i] in
    if c = ' ' || c = '\t' || c = '\r' || c = '\n' then incr i
    else if c = '-' && !i + 1 < n && s.[!i + 1] = '-' then (while !i < n && s.[!i] <> '\n' do incr i done)
    else if c = '-' && !i + 1 < n && s.[!i + 1] = '>' then (push ARR; i := !i + 2)
    else if c = '(' then (push LP; incr i)
    else if c = ')' then (push RP; incr i)
    else if c = '*' then (push STAR; incr i)
    else if c = ',' then (push COMMA; incr i)
    else if c = ':' then (push COLON; incr i)
    else if c = '.' then (push DOT; incr i)
    else if c = '\\' then (push LAM; incr i)
    (* the literal λ (U+03BB, UTF-8 bytes CE BB) is another spelling of the lambda *)
    else if Char.code c = 0xCE && !i + 1 < n && Char.code s.[!i + 1] = 0xBB then (push LAM; i := !i + 2)
    else if c = '{' then (push LBRACE; incr i)
    else if c = '}' then (push RBRACE; incr i)
    else if c = '|' then (push BAR; incr i)
    else if c = '=' && !i + 1 < n && s.[!i + 1] = '>' then (push FATARROW; i := !i + 2)
    else if c = '=' then (push EQ; incr i)
    else if c = '"' then begin
      let j = ref (!i + 1) in
      while !j < n && s.[!j] <> '"' do incr j done;
      push (STR (String.sub s (!i + 1) (!j - !i - 1)));
      i := !j + 1
    end
    else if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_' then begin
      let j = ref !i in
      let is_start k = (s.[k] >= 'a' && s.[k] <= 'z') || (s.[k] >= 'A' && s.[k] <= 'Z') || s.[k] = '_' in
      let read_seg () = while !j < n && is_a s.[!j] do incr j done in
      read_seg ();
      (* glue a qualified name `M::add` (or `A::B::c`) into one identifier token,
         but only when contiguous — `::` is the namespace separator; `.` remains
         the lambda separator, and a single `:` is still the annotation colon. *)
      while !j + 2 < n && s.[!j] = ':' && s.[!j + 1] = ':' && is_start (!j + 2) do
        j := !j + 2; read_seg ()
      done;
      push (ID (String.sub s !i (!j - !i))); i := !j
    end
    else if c >= '0' && c <= '9' then begin
      let j = ref !i in
      while !j < n && s.[!j] >= '0' && s.[!j] <= '9' do incr j done;
      let digits = String.sub s !i (!j - !i) in
      (* an Integer literal is written with a trailing `z` (for ℤ): 120z.
         The suffix binds only when it is not the start of an identifier. *)
      if !j < n && s.[!j] = 'z' && not (!j + 1 < n && is_a s.[!j + 1]) then
        (push (INTLIT digits); i := !j + 1)
      else begin
        (match int_of_string_opt digits with
         | Some k -> push (NUM k)
         | None -> failwith (digits ^ ": Nat literal too large; write it as an Integer with a 'z' suffix (" ^ digits ^ "z)"));
        i := !j
      end
    end
    else failwith (Printf.sprintf "type-theory lexer: unexpected character '%c'" c)
  done;
  push EOF;
  Array.of_list (List.rev !out)

(* -------- parser: names -> de Bruijn core terms -------- *)

let reserved_head = [ "Id"; "transp"; "fst"; "snd"; "if"; "suc"; "natElim"; "strcat"; "streq";
                      "iadd"; "isub"; "imul"; "ieq"; "ilt"; "fromNat" ]
let decl_kw = [ "def"; "check"; "eval"; "data"; "import"; "match"; "return"; "lambda"; "private"; "open"; "record" ]

let index_of (x : string) (ns : string list) : int option =
  let rec go i = function [] -> None | y :: _ when y = x -> Some i | _ :: t -> go (i + 1) t in
  go 0 ns

type decl =
  | Def of string * tm option * tm
  | Check of tm
  | Eval of tm
  | Data_decl of string * (string * tm) list * (string * arg_ty list) list  (* name, params, [ctor, arg types] *)
  | Import of string
  | Open of string   (* `open M`: bring an already-aliased module's names in unqualified *)

(* how an unqualified import filters which of a module's names enter bare scope:
   `import "x"` = FAll, `... exposing (a,b)` = FOnly, `... hiding (a,b)` = FExcept *)
type imp_filter = FAll | FOnly of string list | FExcept of string list

(* datatypes/constructors/eliminators known to the parser. These are MODULE-level
   and shared across `parse` calls so that, when a program is assembled from several
   files (via `import`), a file can use datatypes declared in files parsed before it.
   `reset_tables` clears them at the start of loading a program. *)
let datatypes : (string, unit) Hashtbl.t = Hashtbl.create 16
let ctors : (string, int) Hashtbl.t = Hashtbl.create 32           (* ctor -> arity (params + args) *)
let elims : (string, string * int) Hashtbl.t = Hashtbl.create 16  (* elim -> (datatype, #methods) *)
(* for `match` elaboration: datatype -> (#params, [ctor, arg classifications in order]).
   Populated at parse time (before run_decls), which is the only source available then. *)
let data_info : (string, int * (string * arg_ty list) list) Hashtbl.t = Hashtbl.create 16
let ctor_owner : (string, string) Hashtbl.t = Hashtbl.create 32   (* ctor -> its datatype *)
(* MODULES. Every file is loaded under a unique tag ("basename#k"); each declared
   name is stored internally as "<tag>::<name>". `short_index` maps a bare name to
   the full (tagged) names that declare it, so a bare reference resolves to its
   module's definition — preferring the current module, then the unique other one,
   erroring if two modules would both answer. `#` cannot appear in surface syntax,
   so a written `A::x` is always an alias reference, never a raw tag. *)
let short_index : (string, string list) Hashtbl.t = Hashtbl.create 256
(* names marked `private`: declared and usable inside their own module, but not
   visible to importers (Stage 3 export control). Keyed by full (tagged) name. *)
let private_names : (string, unit) Hashtbl.t = Hashtbl.create 64
(* record fields: full field name -> (position, field count). A `record` desugars
   to a Σ type; `field r` elaborates to fst/snd projections, so the checker's
   Fst/Snd rules recover the (dependent) field type. Fields resolve through the
   module resolver like any other name. *)
let field_info : (string, int * int) Hashtbl.t = Hashtbl.create 64
let reset_tables () =
  Hashtbl.reset datatypes; Hashtbl.reset ctors; Hashtbl.reset elims;
  Hashtbl.reset data_info; Hashtbl.reset ctor_owner; Hashtbl.reset short_index;
  Hashtbl.reset private_names; Hashtbl.reset field_info
(* record that full name `full` (= tag::short) is declared, for bare resolution *)
let index_add full =
  match String.rindex_opt full ':' with
  | Some i ->
      let short = String.sub full (i + 1) (String.length full - i - 1) in
      let prev = try Hashtbl.find short_index short with Not_found -> [] in
      if not (List.mem full prev) then Hashtbl.replace short_index short (full :: prev)
  | None -> ()

(* `ns0` seeds the name scope with globals from files parsed earlier (imports),
   so a file can reference definitions imported before it. *)
let parse ?(ns0 = []) ?(self = "") ?(opened = ([] : (string * imp_filter) list)) ?(aliases = []) (toks : tok array) : decl list =
  (* MODULE RESOLUTION. This file is parsed under tag `self`; its declarations are
     stored as "self::name" (via `qual`). `opened` is the tags of the modules it
     imports UNQUALIFIED (their names are visible bare); `aliases` maps a surface
     alias (from `import "x" as M`) to that module's tag (visible only as M::x).
       • qual s    — the full internal name for a declaration in this file.
       • resolve s — a surface reference → its full internal name (or None):
           - "M::x": M is an alias → "<tag>::x".
           - bare "x": this module's own "self::x", else the unique imported module
             that declares x. A name that exists only in a NON-imported module is
             an error naming the module to import (this is what makes imports
             explicit — no transitive leak). Builtins are dispatched before resolve. *)
  let qual s = if self = "" then s else self ^ "::" ^ s in
  let base f = try String.sub f 0 (String.index f '#') with Not_found -> (try String.sub f 0 (String.index f ':') with Not_found -> f) in
  let tagof f = try String.sub f 0 (String.index f ':') with Not_found -> f in
  let shortof f = match String.rindex_opt f ':' with Some i -> String.sub f (i + 1) (String.length f - i - 1) | None -> f in
  let passes filt s = match filt with FAll -> true | FOnly l -> List.mem s l | FExcept l -> not (List.mem s l) in
  (* is full name f reachable bare in this file: from self, or an opened module whose filter admits it *)
  let f_visible f =
    let t = tagof f in
    t = self || List.exists (fun (tg, filt) -> tg = t && passes filt (shortof f)) opened
  in
  (* a name in another module is off-limits if marked private there *)
  let is_priv full = Hashtbl.mem private_names full && tagof full <> self in
  let resolve s =
    match String.index_opt s ':' with
    | Some i ->
        let m = String.sub s 0 i and x = String.sub s (i + 2) (String.length s - i - 2) in
        (match List.assoc_opt m aliases with
         | Some tag ->
             let full = tag ^ "::" ^ x in
             if is_priv full then failwith (Printf.sprintf "name '%s' is private to module %s" x (base full)) else Some full
         | None -> None)
    | None ->
        let mine = self ^ "::" ^ s in
        let all = try Hashtbl.find short_index s with Not_found -> [] in
        if self <> "" && List.mem mine all then Some mine     (* own names win, even private ones *)
        else
          let in_scope = List.filter f_visible all in
          let vis = List.filter (fun f -> not (is_priv f)) in_scope in
          (match vis with
           | [ f ] -> Some f
           | f :: _ :: _ ->
               ignore f;
               failwith (Printf.sprintf "ambiguous name '%s' — imported from %s; qualify it (M::%s)"
                           s (String.concat ", " (List.map base vis)) s)
           | [] ->
               if in_scope <> [] then    (* imported, but private there *)
                 failwith (Printf.sprintf "name '%s' is private to module %s" s (String.concat " / " (List.sort_uniq compare (List.map base in_scope))))
               else (match all with
                | [] -> None                                   (* truly unbound *)
                | owners ->                                     (* exists, but not imported here *)
                    let mods = List.sort_uniq compare (List.map base owners) in
                    failwith (Printf.sprintf "name '%s' is declared in module %s but not imported here — add an `import` for %s"
                                s (String.concat " / " mods) (String.concat " or " (List.map (fun m -> "\"" ^ m ^ ".kan\"") mods)))))
  in
  let find_key tbl s = match resolve s with Some f when Hashtbl.mem tbl f -> Some f | _ -> None in
  (* a bare local binder (lambda/match) is in `ns` unqualified; a global is tagged.
     So try the raw name first (locals shadow), then the module-resolved name. *)
  let var_key ns s =
    match index_of s ns with
    | Some i -> Some i
    | None -> (match resolve s with Some f -> index_of f ns | None -> None)
  in
  (* a record field, if `s` resolves to one: returns (position, field count) *)
  let field_key s = match resolve s with Some f -> (match Hashtbl.find_opt field_info f with Some kn -> Some kn | None -> None) | None -> None in
  (* project field k of an n-field record value `m` (right-nested Σ, last field
     is the bare tail): fst (snd^k m), or snd^(n-1) m for the last field. *)
  let proj_field k n m =
    let rec sndc j t = if j <= 0 then t else sndc (j - 1) (Snd t) in
    if k = n - 1 then sndc (n - 1) m else Fst (sndc k m)
  in
  let pos = ref 0 in
  let peek () = toks.(!pos) in
  let peek2 () = if !pos + 1 < Array.length toks then toks.(!pos + 1) else EOF in
  let peek3 () = if !pos + 2 < Array.length toks then toks.(!pos + 2) else EOF in
  let adv () = incr pos in
  let fail m = failwith ("type-theory parse error: " ^ m) in
  let eat t m = if peek () = t then adv () else fail ("expected " ^ m) in
  let ident () = match peek () with ID x -> adv (); x | _ -> fail "expected a name" in
  let starts_atom = function LP | NUM _ | INTLIT _ | STR _ -> true | ID x -> not (List.mem x decl_kw) | _ -> false in
  (* recursion state for `match`-defined functions: while parsing the body of a
     recursive def, `rec_fname` is its name, `rec_binders` its lambda-binder names
     (in order), `rec_annot` its type annotation, `rec_decarg` the matched
     (decreasing) binder, and `rec_ihmap` maps the current arm's recursive-position
     pattern binders to their induction hypotheses. `rec_at_top` is true while
     parsing in TAIL position of the def body — only a tail-position match on a
     binder may claim the recursion (otherwise a nested match would misfire).
     A recursive call [f pre.. r acc..] elaborates to [(hypothesis for r) acc..]. *)
  let rec_fname = ref None and rec_binders = ref [] and rec_decarg = ref "" and rec_ihmap = ref [] in
  let rec_annot = ref None and rec_at_top = ref false in
  (* globally-unique induction-hypothesis binder names, so a nested match's
     hypothesis never shadows an enclosing one *)
  let ih_ctr = ref 0 in
  let fresh_ih () = incr ih_ctr; "#ih" ^ string_of_int !ih_ctr in
  let peel_pi k t = let rec go k t = if k <= 0 then t else (match t with Pi (_, _, b) -> go (k - 1) b | _ -> t) in go k t in
  let rec term ?(expected = None) ns =
    match peek () with
    | LAM | ID "lambda" ->
        (* a lambda: any of `\`, `lambda`, or `λ` to introduce it, and either `.`
           or `:` to separate the binders from the body. Any number of binders. *)
        adv ();
        let rec names acc = match peek () with ID x -> adv (); names (x :: acc) | DOT | COLON -> adv (); List.rev acc | _ -> fail "expected lambda binders then '.' or ':'" in
        let bs = names [] in
        let ns' = List.fold_left (fun a x -> x :: a) ns bs in
        (* peel one Pi of the expected type per binder, so a `match` in the body
           can recover its result type (the motive) from the def's annotation *)
        let rec peel n exp = if n <= 0 then exp else (match exp with Some (Pi (_, _, b)) -> peel (n - 1) (Some b) | _ -> None) in
        let body = term ~expected:(peel (List.length bs) expected) ns' in
        List.fold_right (fun x b -> Lam (x, b)) bs body
    | ID "match" -> parse_match ns expected
    | LP when (match peek2 () with ID _ -> true | _ -> false) && peek3 () = COLON ->
        rec_at_top := false;
        adv (); let x = ident () in eat COLON ":"; let a = term ns in eat RP ")";
        let ns' = x :: ns in
        (match peek () with
         | ARR -> adv (); Pi (x, a, term ns')
         | STAR -> adv (); Sig (x, a, term ns')
         | _ -> fail "expected '->' or '*' after (x : A)")
    | _ ->
        rec_at_top := false;         (* below here is not tail position of the def body *)
        let lhs = app ns in
        (match peek () with
         (* codomain is under a fresh binder, so shift its scope with "_" *)
         | ARR -> adv (); Pi ("_", lhs, term ("_" :: ns))
         | STAR -> adv (); Sig ("_", lhs, term ("_" :: ns))
         | _ -> lhs)
  and app ns =
    let take_atoms k = let rec go i = if i <= 0 then [] else let a = atom ns in a :: go (i - 1) in go k in
    let base =
      match peek () with
      | ID x when !rec_fname = Some x && !rec_decarg <> "" ->
          (* a recursive call: the argument BEFORE the decreasing one must be passed
             unchanged; the decreasing one must be a structurally-smaller pattern
             variable; the arguments AFTER it (the moved/accumulator args) may be
             anything and are applied to the induction hypothesis. *)
          adv ();
          let bnds = !rec_binders in
          let args = take_atoms (List.length bnds) in
          let dpos = (let rec idx i = function [] -> -1 | y :: _ when y = !rec_decarg -> i | _ :: t -> idx (i + 1) t in idx 0 bnds) in
          let name_of = function Var i -> List.nth_opt ns i | _ -> None in
          List.iteri (fun j a ->
            if j < dpos then
              match name_of a with
              | Some nm when nm = List.nth bnds j -> ()
              | _ -> fail (Printf.sprintf "recursive call to '%s': argument %d (before the decreasing one) must be passed unchanged. In a fold the parameters left of the recursion argument are fixed — they parameterize the algebra; only the recursion argument shrinks. Pass it unchanged, or move a genuinely-varying parameter to the right of the decreasing one." x (j + 1)))
            args;
          let ih =
            match name_of (List.nth args dpos) with
            | Some nm -> (match List.assoc_opt nm !rec_ihmap with
                          | Some ih -> ih
                          | None -> fail (Printf.sprintf "recursive call to '%s' must decrease on a structurally-smaller argument, but '%s' is not one. A total function is the fold (catamorphism) out of the initial algebra — the unique Kan extension of its cases — so each recursive call must be on a constructor sub-part the match exposes (e.g. the k in `suc k`), never the whole value. To reach a deeper predecessor (like n-2), carry the extra state in the result (an accumulator / pair) so it stays one fold — cf. examples/cookbook.kan `fibPair`." x nm))
            | None -> fail (Printf.sprintf "recursive call to '%s': the decreasing argument must be a pattern variable — recurse on the sub-structure the match binds (e.g. k from `suc k`), not a computed expression. That is what makes the definition the fold, the unique map out of the initial algebra." x)
          in
          let ihv = (match index_of ih ns with Some i -> Var i | None -> fail "internal error: induction hypothesis not in scope") in
          let moved_vals = List.filteri (fun j _ -> j > dpos) args in
          List.fold_left (fun acc v -> App (acc, v)) ihv moved_vals
      | ID "Id" -> adv (); let a = atom ns in let b = atom ns in let c = atom ns in Id (a, b, c)
      | ID "transp" ->
          adv (); let a = atom ns in let p = atom ns in let x = atom ns in
          let y = atom ns in let pe = atom ns in let d = atom ns in Transp (a, p, x, y, pe, d)
      | ID "fst" -> adv (); Fst (atom ns)
      | ID "snd" -> adv (); Snd (atom ns)
      | ID "if" -> adv (); let c = atom ns in let t = atom ns in let e = atom ns in If (c, t, e)
      | ID "suc" -> adv (); Suc (atom ns)
      | ID "natElim" ->
          adv (); let p = atom ns in let z = atom ns in let s = atom ns in let nt = atom ns in
          NatElim (p, z, s, nt)
      | ID "strcat" -> adv (); let a = atom ns in let b = atom ns in StrApp (a, b)
      | ID "streq" -> adv (); let a = atom ns in let b = atom ns in StrEq (a, b)
      | ID "iadd" -> adv (); let a = atom ns in let b = atom ns in IntAdd (a, b)
      | ID "isub" -> adv (); let a = atom ns in let b = atom ns in IntSub (a, b)
      | ID "imul" -> adv (); let a = atom ns in let b = atom ns in IntMul (a, b)
      | ID "idiv" -> adv (); let a = atom ns in let b = atom ns in IntDiv (a, b)
      | ID "igcd" -> adv (); let a = atom ns in let b = atom ns in IntGcd (a, b)
      | ID "nadd" -> adv (); let a = atom ns in let b = atom ns in NatAdd (a, b)
      | ID "nmul" -> adv (); let a = atom ns in let b = atom ns in NatMul (a, b)
      | ID "ngcd" -> adv (); let a = atom ns in let b = atom ns in NatGcd (a, b)
      | ID "ndiv" -> adv (); let a = atom ns in let b = atom ns in NatDiv (a, b)
      | ID "npred" -> adv (); NatPred (atom ns)
      | ID "ieq" -> adv (); let a = atom ns in let b = atom ns in IntEq (a, b)
      | ID "ilt" -> adv (); let a = atom ns in let b = atom ns in IntLt (a, b)
      | ID "fromNat" -> adv (); IntFromNat (atom ns)
      | ID x when (match find_key ctors x with Some k -> Hashtbl.find ctors k > 0 | None -> false) ->
          adv (); let k = Option.get (find_key ctors x) in
          List.fold_left (fun acc a -> App (acc, a)) (Con k) (take_atoms (Hashtbl.find ctors k))
      | ID x when find_key elims x <> None ->
          adv (); let e = Option.get (find_key elims x) in let _, k = Hashtbl.find elims e in
          List.fold_left (fun acc a -> App (acc, a)) (Elim e) (take_atoms k)
      | ID x when field_key x <> None ->
          (* a record field: `f r` projects; bare `f` is the accessor `\r. f r` *)
          adv (); let (k, n) = Option.get (field_key x) in
          if starts_atom (peek ()) then proj_field k n (atom ns)
          else Lam ("r", proj_field k n (Var 0))
      | _ -> atom ns
    in
    let rec spine b = if starts_atom (peek ()) then spine (App (b, atom ns)) else b in
    spine base
  and atom ns =
    match peek () with
    | ID ("U" | "Type") -> adv (); U 0
    (* a universe literal Ui (i >= 1); matches how the printer shows U i *)
    | ID x when String.length x >= 2 && x.[0] = 'U'
                && String.for_all (fun c -> c >= '0' && c <= '9') (String.sub x 1 (String.length x - 1)) ->
        adv (); U (int_of_string (String.sub x 1 (String.length x - 1)))
    | ID "Bool" -> adv (); Bool
    | ID "true" -> adv (); True
    | ID "false" -> adv (); False
    | ID "Nat" -> adv (); Nat
    | ID "zero" -> adv (); Zero
    | NUM k -> adv (); NatLit (Bigint.of_int k)   (* canonical literal — no Suc-tower built at parse time *)
    | ID "String" -> adv (); StringT
    | STR s -> adv (); Str s
    | ID "Integer" -> adv (); IntT
    | INTLIT s -> adv (); IntLit (Bigint.of_string s)
    | ID "refl" -> adv (); Refl
    | ID x when List.mem x reserved_head -> fail (x ^ " must be applied to its arguments")
    | ID x when List.mem x decl_kw -> fail ("unexpected '" ^ x ^ "'")
    | ID x when find_key datatypes x <> None -> adv (); Data (Option.get (find_key datatypes x))
    | ID x when (match find_key ctors x with Some k -> Hashtbl.find ctors k = 0 | None -> false) -> adv (); Con (Option.get (find_key ctors x))
    | ID x when find_key ctors x <> None -> fail (x ^ " needs arguments")
    | ID x when find_key elims x <> None -> fail (x ^ " needs arguments (parameters, a motive, methods, and a target)")
    | ID x when field_key x <> None -> adv (); let (k, n) = Option.get (field_key x) in Lam ("r", proj_field k n (Var 0))
    | ID x -> adv (); (match var_key ns x with
        | Some i -> Var i
        | None ->
            if !rec_fname = Some x then
              fail (Printf.sprintf "recursive call to '%s' is not in a position Kan reads as structural recursion. The recursive `match` on the decreasing argument must be in tail position — the body itself (optionally applied to further arguments), not wrapped inside a constructor or other expression — so the definition presents the fold, the unique map out of the initial algebra. Lift the recursion out of its wrapper." x)
            else fail ("unbound name '" ^ x ^ "'"))
    | LP ->
        adv ();
        let t = term ns in
        (match peek () with COMMA -> adv (); let u = term ns in eat RP ")"; Pair (t, u) | _ -> eat RP ")"; t)
    | _ -> fail "expected a term"
  (* Elaborate `match scrut { | C x.. => e | ... }` to the datatype's eliminator.
     The result type R (the motive) comes from `return T` or the threaded
     annotation; parameterized scrutinees are written `match (x : D a..) { .. }`.
     Recursive constructor arguments get a (Stage-1-unused) induction-hypothesis
     binder in scope, so the elaboration is already the eliminator's method. *)
  and parse_match ns expected =
    adv ();  (* 'match' *)
    let was_top = !rec_at_top in rec_at_top := false;   (* capture before parsing the scrutinee consumes it *)
    let scrut, scrut_ty =
      if peek () = LP then begin
        adv ();
        let e = term ns in
        (match peek () with
         | COLON -> adv (); let t = term ns in eat RP ")"; (e, Some t)
         | RP -> adv (); (e, None)
         | _ -> fail "match scrutinee: expected ')' or ' : type'")
      end else (atom ns, None)
    in
    (* `match e as x return T { .. }` — an EXPLICIT dependent motive `\x. T`
       (T may mention the scrutinee value x). This is what lets a nested / non-
       leading match refine its scrutinee — the gap plain `return T` (which gives
       the non-dependent `\_. T`) and the annotation-derived motive both leave. *)
    let mot =
      if peek () = ID "as" then begin
        adv ();
        let x = ident () in
        if peek () <> ID "return" then fail "match: `as x` must be followed by `return <motive>`";
        adv ();
        Some (Lam (x, term (x :: ns)))
      end else None
    in
    let rty = match mot with
      | Some _ -> None
      | None -> if peek () = ID "return" then (adv (); Some (term ns)) else expected in
    (* Only a TAIL-POSITION match on one of the def's binders may claim the
       recursion (its decreasing argument). Consume the tail flag either way. *)
    let scrut_binder = (match scrut with Var i -> (match List.nth_opt ns i with Some nm when List.mem nm !rec_binders -> Some nm | _ -> None) | _ -> None) in
    let claim = was_top && !rec_fname <> None && scrut_binder <> None in
    eat LBRACE "{";
    (* classify the datatype from the first constructor (without consuming), so we
       know before parsing arm bodies whether this is a recursive elimination
       (Nat / user datatype) — a Bool `match` has no hypothesis and never claims *)
    let first_ctor = let saved = !pos in
      let c = if peek () = BAR then (adv (); match peek () with ID x -> Some x | _ -> None) else None in
      pos := saved; c in
    let is_bool = (match first_ctor with Some ("true" | "false") -> true | _ -> false) in
    let decreasing = claim && not is_bool in
    let dpos, moved_names =
      if decreasing then begin
        let nm = (match scrut_binder with Some nm -> nm | None -> "") in
        rec_decarg := nm;
        let rec idx i = function [] -> -1 | y :: _ when y = nm -> i | _ :: t -> idx (i + 1) t in
        let d = idx 0 !rec_binders in (d, drop (d + 1) !rec_binders)
      end else (-1, [])
    in
    let num_moved = List.length moved_names in
    let arms = ref [] in
    while peek () = BAR do
      adv ();
      let cname_raw = ident () in
      (* resolve a user constructor through the module resolver; a bare arm name
         finds its module's "tag::ctor". Nat/Bool builtins are never tagged.
         Constructors are stored resolved so they match `data_info`. *)
      let cname = (match cname_raw with
        | "zero" | "suc" | "true" | "false" -> cname_raw
        | _ -> (match find_key ctor_owner cname_raw with Some ck -> ck | None -> cname_raw)) in
      let rec pbs acc = match peek () with ID x -> adv (); pbs (x :: acc) | FATARROW -> adv (); List.rev acc | _ -> fail "expected pattern binders then '=>'" in
      let bs = pbs [] in
      let nargs, ih_names, rec_pairs =
        match cname with
        | "zero" | "true" | "false" -> (0, [], [])
        | "suc" -> (match bs with [ k ] -> let ih = fresh_ih () in (1, [ ih ], [ (k, ih) ]) | _ -> (1, [ fresh_ih () ], []))
        | _ ->
            (match Hashtbl.find_opt ctor_owner cname with
             | None -> fail ("match: '" ^ cname ^ "' is not a constructor")
             | Some d ->
                 let _, cs = Hashtbl.find data_info d in
                 let argtys = List.assoc cname cs in
                 if List.length bs <> List.length argtys then
                   fail (Printf.sprintf "match: pattern '%s' expects %d argument(s), got %d" cname (List.length argtys) (List.length bs));
                 let pairs = List.filter_map (fun (b, aty) -> match aty with ARec -> Some (b, fresh_ih ()) | _ -> None) (List.combine bs argtys) in
                 (List.length argtys, List.map snd pairs, pairs))
      in
      if List.length bs <> nargs then
        fail (Printf.sprintf "match: pattern '%s' expects %d argument(s), got %d" cname nargs (List.length bs));
      (* post-decreasing (moved) args are re-abstracted after the method's own
         binders, so the induction hypothesis becomes a function of them *)
      let meth_binders = bs @ ih_names @ moved_names in
      let ns_body = List.rev meth_binders @ ns in
      if decreasing then rec_ihmap := rec_pairs;   (* only the decreasing match drives recursion *)
      (* the result type is valid in the match's scope; lift it over the method's
         own binders so a NESTED match in the body reads a correctly-indexed motive *)
      let body_expected = (match rty with Some r -> Some (lift (List.length meth_binders) 0 r) | None -> None) in
      let body = term ~expected:body_expected ns_body in
      let meth = List.fold_right (fun x b -> Lam (x, b)) meth_binders body in
      arms := (cname, meth) :: !arms
    done;
    eat RBRACE "}";
    let arms = List.rev !arms in
    let names_of = List.map fst arms in
    let find c = try List.assoc c arms with Not_found -> fail ("match: missing case for '" ^ c ^ "' — a fold must handle every constructor (the cocone out of the initial algebra must be total, or the universal map is undefined). Add the missing case.") in
    (* the motive: for the decreasing match it is the def's return type as a
       function of the moved arguments (read off the annotation, lifted into
       scope); otherwise the plain result type R *)
    let motive () =
      match mot with
      | Some m ->
          if decreasing then
            fail "match: an explicit `as … return` motive on a recursive/decreasing match is not yet supported (the def annotation already supplies its motive)"
          else m
      | None ->
      if decreasing then
        (* DEPENDENT motive: the annotation's Pi over the scrutinee, as a lambda
           (so the result type may mention the scrutinee — this is what lets a
           `match` prove things by induction), lifted into the eliminator's scope.
           When the result type doesn't mention the scrutinee it is the plain
           `\_. R` up to the unused binder, so ordinary functions are unchanged. *)
        (match !rec_annot with
         | Some t -> (match peel_pi dpos t with
                      | Pi (x, _, r) -> lift (num_moved + 1) 0 (Lam (x, r))
                      | _ -> fail "a recursive `match` needs a function-typed def annotation")
         | None -> fail "a recursive `match` needs its def to carry a type annotation")
      else match rty with
        | Some r -> Lam ("_", lift 1 0 r)
        | None -> fail "match needs a result type: use a typed `def`, or write `match e return T { .. }`"
    in
    (* apply the eliminator's result to the moved arguments' outer binders *)
    let apply_moved t = List.fold_left (fun acc nm -> match index_of nm ns with Some i -> App (acc, Var i) | None -> acc) t moved_names in
    if List.mem "zero" names_of || List.mem "suc" names_of then
      apply_moved (NatElim (motive (), find "zero", find "suc", scrut))
    else if is_bool || List.mem "true" names_of || List.mem "false" names_of then
      If (scrut, find "true", find "false")            (* Bool: no motive, no moved machinery *)
    else begin
      (* user datatype: identified from an arm, or — for an empty match, e.g. on
         Void — from the scrutinee's type annotation *)
      let d = match names_of with
        | c :: _ -> (match Hashtbl.find_opt ctor_owner c with Some d -> d | None -> fail ("match: '" ^ c ^ "' is not a constructor"))
        | [] -> (match scrut_ty with
                 | Some t -> let rec sp = function App (f, _) -> sp f | h -> h in
                             (match sp t with Data d -> d | _ -> fail "match: cannot tell which type this is; annotate `(x : D ..)`")
                 | None -> fail "empty match needs the scrutinee's type: `match (x : D ..) return R { }`")
      in
      let k, cs = (try Hashtbl.find data_info d with Not_found -> fail ("match: unknown datatype " ^ d)) in
      let ctor_set = List.map fst cs in
      List.iter (fun c -> if not (List.mem c ctor_set) then fail ("match: '" ^ c ^ "' is not a constructor of " ^ d)) names_of;
      let params =
        if k = 0 then []
        else match scrut_ty with
          | None -> fail (Printf.sprintf "match on %s needs the scrutinee's type: write `match (x : %s ..) { .. }`" d d)
          | Some t ->
              let rec sp acc = function App (f, a) -> sp (a :: acc) f | h -> (h, acc) in
              (match sp [] t with
               | Data d', args when d' = d ->
                   if List.length args <> k then fail (Printf.sprintf "match: %s takes %d type parameter(s)" d k) else args
               | _ -> fail ("match: scrutinee type must be " ^ d ^ " applied to its parameters"))
      in
      let methods = List.map (fun (cn, _) -> find cn) cs in
      let head = List.fold_left (fun acc p -> App (acc, p)) (Elim (d ^ "_elim")) params in
      let head = App (head, motive ()) in
      let head = List.fold_left (fun acc m -> App (acc, m)) head methods in
      apply_moved (App (head, scrut))
    end
  in
  let rec decl ns =
    match peek () with
    | ID "private" ->
        (* `private def`/`private data`: parse the declaration, then mark its
           name(s) module-private so importers can't see them. *)
        adv ();
        let d = decl ns in
        (match d with
         | Def (full, _, _) -> Hashtbl.replace private_names full ()
         | Data_decl (full, _, cs) ->
             Hashtbl.replace private_names full ();
             List.iter (fun (c, _) -> Hashtbl.replace private_names c ()) cs
         | _ -> fail "`private` must be followed by a `def` or `data`");
        d
    | ID "def" ->
        adv (); let name = ident () in
        let ty = (match peek () with COLON -> adv (); Some (term ns) | _ -> None) in
        eat EQ "=";
        (* capture the leading lambda binders, so the body may recurse structurally
           on one of them (elaborated to that type's eliminator) *)
        let lead =
          match peek () with
          | LAM | ID "lambda" ->
              adv ();
              let rec names acc = match peek () with ID x -> adv (); names (x :: acc) | DOT | COLON -> adv (); List.rev acc | _ -> fail "expected lambda binders then '.' or ':'" in
              names []
          | _ -> []
        in
        let ns' = List.rev lead @ ns in
        let rec peel n exp = if n <= 0 then exp else (match exp with Some (Pi (_, _, b)) -> peel (n - 1) (Some b) | _ -> None) in
        rec_fname := Some name; rec_binders := lead; rec_annot := ty; rec_decarg := ""; rec_ihmap := [];
        rec_at_top := (lead <> []);   (* the body is in tail position of the def *)
        let inner = term ~expected:(peel (List.length lead) ty) ns' in
        rec_fname := None; rec_binders := []; rec_annot := None; rec_decarg := ""; rec_ihmap := []; rec_at_top := false;
        let body = List.fold_right (fun x b -> Lam (x, b)) lead inner in
        index_add (qual name);
        Def (qual name, ty, body)
    | ID "check" -> adv (); Check (term ns)
    | ID "eval" -> adv (); Eval (term ns)
    | ID "open" -> adv (); (match peek () with ID m -> adv (); Open m | _ -> fail "expected a module alias after `open`")
    | ID "record" ->
        (* `record Name { f0 : T0, …, fn : Tn }` desugars to the Σ type
           (f0 : T0) * … * Tn (right-nested; last field is the bare tail), plus a
           field registry so `fk r` projects. Each field type is parsed with the
           earlier fields in scope, so it may depend on them. *)
        adv (); let name = ident () in eat LBRACE "{";
        let rec parse_fields ns_fields acc =
          let fn = ident () in eat COLON ":";
          let fty = term (ns_fields @ ns) in
          let acc = (fn, fty) :: acc in
          (match peek () with
           | COMMA -> adv (); (match peek () with RBRACE -> List.rev acc | _ -> parse_fields (fn :: ns_fields) acc)
           | RBRACE -> List.rev acc
           | _ -> fail "record: expected ',' or '}' after a field")
        in
        let flds = (match peek () with RBRACE -> [] | _ -> parse_fields [] []) in
        eat RBRACE "}";
        let n = List.length flds in
        if n = 0 then fail "record needs at least one field";
        let rec build = function [ (_, t) ] -> t | (fn, t) :: rest -> Sig (fn, t, build rest) | [] -> fail "record needs at least one field" in
        let sigty = build flds in
        index_add (qual name);
        List.iteri (fun k (fn, _) -> index_add (qual fn); Hashtbl.replace field_info (qual fn) (k, n)) flds;
        Def (qual name, None, sigty)
    | ID "import" ->
        adv ();
        (match peek () with
         | STR p ->
             adv ();
             (* optional `as M` and `exposing (…)` / `hiding (…)` — consumed here so
                the file parses; the loader (scan_imports) reads the same clauses to
                build the resolution context. The Import node itself is discarded. *)
             (if peek () = ID "as" then (adv (); match peek () with ID _ -> adv () | _ -> fail "expected a namespace name after `as`"));
             (match peek () with
              | ID ("exposing" | "hiding") ->
                  adv (); eat LP "(";
                  let rec names () = match peek () with
                    | ID _ -> adv (); (match peek () with COMMA -> adv (); names () | _ -> ())
                    | RP -> () | _ -> fail "expected names in exposing/hiding list" in
                  names (); eat RP ")"
              | _ -> ());
             Import p
         | _ -> fail "expected a \"path\" after import")
    | ID "data" ->
        adv (); let name = ident () in
        (* parameters:  (p : T) ... *)
        let rec parse_params acc =
          match peek () with
          | LP -> adv (); let pn = ident () in eat COLON ":"; let pty = term (List.map fst acc @ ns) in
                  eat RP ")"; parse_params ((pn, pty) :: acc)
          | _ -> List.rev acc
        in
        let ps = parse_params [] in
        let k = List.length ps in
        Hashtbl.replace datatypes (qual name) ();      (* register early so constructor types can be recursive *)
        index_add (qual name);
        let ns_ctor = List.fold_left (fun a (pn, _) -> pn :: a) ns ps in
        (* the datatype applied to all its parameters, as it appears under `depth` binders *)
        let applied_data_tm depth =
          List.fold_left (fun acc m -> App (acc, Var (k - 1 - m + depth))) (Data (qual name)) (List.init k (fun m -> m))
        in
        let rec no_vars = function
          | Var _ -> false
          | U _ | Bool | True | False | Nat | Zero | Refl | Data _ | Con _ | Elim _ | StringT | Str _
          | IntT | IntLit _ | NatLit _ -> true
          | Pi (_, a, b) | Sig (_, a, b) | App (a, b) | Pair (a, b) | Ann (a, b) | StrApp (a, b) | StrEq (a, b)
          | IntAdd (a, b) | IntSub (a, b) | IntMul (a, b) | IntEq (a, b) | IntLt (a, b) | IntDiv (a, b) | IntGcd (a, b) | NatAdd (a, b) | NatMul (a, b) | NatGcd (a, b) | NatDiv (a, b) -> no_vars a && no_vars b
          | Lam (_, b) | Suc b | Fst b | Snd b | IntFromNat b | NatPred b -> no_vars b
          | Id (a, b, c) | If (a, b, c) -> no_vars a && no_vars b && no_vars c
          | NatElim (a, b, c, d) -> no_vars a && no_vars b && no_vars c && no_vars d
          | Transp (a, b, c, d, e, f) -> List.for_all no_vars [ a; b; c; d; e; f ]
        in
        eat LBRACE "{";
        let parse_ctor () =
          let cname = ident () in
          eat COLON ":";
          let ty = term ns_ctor in
          let rec decompose depth t =
            match t with
            | Pi ("_", a, b) -> let args, ret = decompose (depth + 1) b in ((depth, a) :: args, ret)
            | Pi _ -> fail ("constructor " ^ cname ^ ": dependent argument types are not supported")
            | other -> ([], other)
          in
          let dargs, ret = decompose 0 ty in
          let n = List.length dargs in
          if ret <> applied_data_tm n then fail ("constructor " ^ cname ^ " must return " ^ name ^ " applied to its parameters");
          let classify (j, a) =
            match a with
            | Var i when i >= j && i - j < k -> AParam (k - 1 - (i - j))
            | _ when a = applied_data_tm j -> ARec
            | _ when no_vars a -> AClosed a
            | _ -> fail ("constructor " ^ cname ^ ": unsupported argument type (want a parameter, " ^ name ^ ", or a closed type)")
          in
          let argtys = List.map classify dargs in
          Hashtbl.replace ctors (qual cname) (k + n);
          index_add (qual cname);
          (qual cname, argtys)
        in
        let rec many acc =
          let c = parse_ctor () in
          match peek () with
          | COMMA -> adv (); (match peek () with RBRACE -> List.rev (c :: acc) | _ -> many (c :: acc))
          | _ -> List.rev (c :: acc)
        in
        let cs = (match peek () with RBRACE -> [] | _ -> many []) in
        eat RBRACE "}";
        Hashtbl.replace elims ((qual name) ^ "_elim") (qual name, k + 1 + List.length cs + 1);
        index_add ((qual name) ^ "_elim");   (* so an explicit `T_elim` reference resolves *)
        Hashtbl.replace data_info (qual name) (k, cs);
        List.iter (fun (cn, _) -> Hashtbl.replace ctor_owner cn (qual name)) cs;
        Data_decl (qual name, ps, cs)
    | _ -> fail "expected a declaration (import / def / check / eval / data)"
  in
  (* interleave: each def extends the name scope for later decls *)
  let rec loop ns acc =
    if peek () = EOF then List.rev acc
    else
      let d = decl ns in
      let ns' = match d with Def (name, _, _) -> name :: ns | _ -> ns in
      loop ns' (d :: acc)
  in
  loop ns0 []

(* -------- a single flat namespace: names must be unique -------- *)

(* Within a module every def, data type, and constructor share one namespace, so a
   name may not be declared twice in the same file (this catches, e.g., a
   constructor and an accessor given the same name). Names are internally tagged
   per module, so this is naturally per-module: two files may reuse a name freely. *)
let check_unique (decls : decl list) : unit =
  let seen : (string, string) Hashtbl.t = Hashtbl.create 256 in
  let shortof n = match String.rindex_opt n ':' with Some i -> String.sub n (i + 1) (String.length n - i - 1) | None -> n in
  let modof n = try String.sub n 0 (String.index n '#') with Not_found -> (try String.sub n 0 (String.index n ':') with Not_found -> "this file") in
  let claim kind n =
    match Hashtbl.find_opt seen n with
    | Some prev ->
        failwith (Printf.sprintf
          "'%s' is declared twice in module %s (as a %s and a %s) — rename one of them."
          (shortof n) (modof n) prev kind)
    | None -> Hashtbl.add seen n kind
  in
  List.iter
    (function
      | Def (n, _, _) -> claim "def" n
      | Data_decl (n, _, cs) -> claim "data type" n; List.iter (fun (c, _) -> claim "constructor" c) cs
      | Check _ | Eval _ | Import _ | Open _ -> ())
    decls

(* -------- the Kan lens: each definition as a fiber of the initial-model Kan extension --------
   A program is a presentation (its defs are generators, its equations relations);
   its meaning is the initial model — a left Kan extension of the generators along
   their inclusion. `kan explain` renders each def's fiber of that one construction:
   folds/matches are the rich fibers (genuine (co)limits / Kan extensions), a plain
   value is the trivial fiber. This describes STRUCTURE, so it inspects the elaborated
   core term rather than re-deriving anything. *)
let describe_decl (d : decl) : (string * string) option =
  let strip s = match String.rindex_opt s ':' with Some i -> String.sub s (i + 1) (String.length s - i - 1) | None -> s in
  let dtype e = let s = strip e in if Filename.check_suffix s "_elim" then Filename.chop_suffix s "_elim" else s in
  let rec peel t = match t with Lam (_, b) -> peel b | _ -> t in
  let rec head t = match t with App (f, _) -> head f | _ -> t in
  match d with
  | Data_decl (n, _, cs) ->
      Some (n, Printf.sprintf "an inductive type {%s} — the initial algebra of its constructor functor (a colimit); its recursor is the unique mediating map."
                 (String.concat " | " (List.map (fun (c, _) -> strip c) cs)))
  | Def (n, _, body) ->
      let desc =
        match head (peel body) with
        | NatElim _ -> "a fold over \xe2\x84\x95 (a catamorphism) — the left Kan extension of its zero/suc cases along {zero, suc} \xe2\x86\xaa \xe2\x84\x95."
        | Elim e -> Printf.sprintf "a fold over %s (the universal map out of its initial algebra) — the left Kan extension of its cases along the constructors \xe2\x86\xaa %s." (dtype e) (dtype e)
        | If _ -> "case analysis on Bool — a copairing out of a coproduct (a colimit; Lan along the map to 1)."
        | Sig _ -> "a signature — a dependent record type (a presented theory); its values are its models."
        | Pi _ -> "a \xce\xa0-type — right adjoint to substitution (itself a Kan extension; Lawvere)."
        | U _ | Data _ | Bool | Nat | StringT | IntT | Id _ -> "a type."
        | Var _ | Fst _ | Snd _ -> "a derived operation — built from earlier generators."
        | _ -> "a value — a generator with a defining equation; its universal completion is trivial (the terminal fiber)."
      in
      Some (n, desc)
  | Check _ | Eval _ | Import _ | Open _ -> None

(* -------- driver: elaborate, check, report -------- *)

let run_decls (decls : decl list) : unit =
  let ctx = ref empty in
  let names = ref [] in
  let sh t = show ~ns:!names t in
  let nf t = quote !ctx.lvl (eval !ctx.env t) in
  List.iter
    (fun d ->
      match d with
      | Def (name, ty, body) ->
          let vty, disp =
            match ty with
            | Some t ->
                (match infer !ctx t with VU _ -> () | _ -> failwith ("def " ^ name ^ ": the annotation is not a type"));
                (eval !ctx.env t, sh t)  (* display the written annotation, keeping defs folded *)
            | None -> let v = infer !ctx body in (v, sh (quote !ctx.lvl v))
          in
          check !ctx body vty;
          let v = eval !ctx.env body in
          Printf.printf "def %-6s : %s\n" name disp;
          ctx := { env = v :: !ctx.env; types = vty :: !ctx.types; lvl = !ctx.lvl + 1 };
          names := name :: !names
      | Check t ->
          let ty = infer !ctx t in
          Printf.printf "check    : %s\n           = %s\n" (sh (quote !ctx.lvl ty)) (sh (nf t))
      | Eval t -> Printf.printf "eval     : %s\n" (sh (nf t))
      | Data_decl (name, params, ctors_info) ->
          let specs =
            List.map
              (fun (cname, argtys) ->
                { cs_name = cname; cs_args = List.mapi (fun i aty -> (Printf.sprintf "x%d" i, aty)) argtys })
              ctors_info
          in
          declare_data name params specs;
          Printf.printf "data %s = %s\n" name (String.concat " | " (List.map fst ctors_info))
      | Import _ | Open _ -> ())   (* imports/opens are resolved before we get here *)
    decls

let run (src : string) : unit = run_decls (parse (tokenize src))
