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
      while !j < n && is_a s.[!j] do incr j done;
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
let decl_kw = [ "def"; "check"; "eval"; "data"; "import"; "match"; "return"; "lambda" ]

let index_of (x : string) (ns : string list) : int option =
  let rec go i = function [] -> None | y :: _ when y = x -> Some i | _ :: t -> go (i + 1) t in
  go 0 ns

type decl =
  | Def of string * tm option * tm
  | Check of tm
  | Eval of tm
  | Data_decl of string * (string * tm) list * (string * arg_ty list) list  (* name, params, [ctor, arg types] *)
  | Import of string

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
let reset_tables () =
  Hashtbl.reset datatypes; Hashtbl.reset ctors; Hashtbl.reset elims;
  Hashtbl.reset data_info; Hashtbl.reset ctor_owner

(* `ns0` seeds the name scope with globals from files parsed earlier (imports),
   so a file can reference definitions imported before it. *)
let parse ?(ns0 = []) (toks : tok array) : decl list =
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
              | _ -> fail (Printf.sprintf "recursive call to '%s': argument %d (before the decreasing one) must be passed unchanged" x (j + 1)))
            args;
          let ih =
            match name_of (List.nth args dpos) with
            | Some nm -> (match List.assoc_opt nm !rec_ihmap with
                          | Some ih -> ih
                          | None -> fail (Printf.sprintf "recursive call to '%s' must decrease on a structurally-smaller argument, but '%s' is not one" x nm))
            | None -> fail (Printf.sprintf "recursive call to '%s': the decreasing argument must be a pattern variable" x)
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
      | ID "ieq" -> adv (); let a = atom ns in let b = atom ns in IntEq (a, b)
      | ID "ilt" -> adv (); let a = atom ns in let b = atom ns in IntLt (a, b)
      | ID "fromNat" -> adv (); IntFromNat (atom ns)
      | ID x when (match Hashtbl.find_opt ctors x with Some k -> k > 0 | None -> false) ->
          adv (); List.fold_left (fun acc a -> App (acc, a)) (Con x) (take_atoms (Hashtbl.find ctors x))
      | ID x when Hashtbl.mem elims x ->
          adv (); let _, k = Hashtbl.find elims x in
          List.fold_left (fun acc a -> App (acc, a)) (Elim x) (take_atoms k)
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
    | NUM k -> adv (); let rec mk i = if i <= 0 then Zero else Suc (mk (i - 1)) in mk k
    | ID "String" -> adv (); StringT
    | STR s -> adv (); Str s
    | ID "Integer" -> adv (); IntT
    | INTLIT s -> adv (); IntLit (Bigint.of_string s)
    | ID "refl" -> adv (); Refl
    | ID x when List.mem x reserved_head -> fail (x ^ " must be applied to its arguments")
    | ID x when List.mem x decl_kw -> fail ("unexpected '" ^ x ^ "'")
    | ID x when Hashtbl.mem datatypes x -> adv (); Data x
    | ID x when (match Hashtbl.find_opt ctors x with Some 0 -> true | _ -> false) -> adv (); Con x
    | ID x when Hashtbl.mem ctors x -> fail (x ^ " needs arguments")
    | ID x when Hashtbl.mem elims x -> fail (x ^ " needs arguments (parameters, a motive, methods, and a target)")
    | ID x -> adv (); (match index_of x ns with Some i -> Var i | None -> fail ("unbound name '" ^ x ^ "'"))
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
    let rty = if peek () = ID "return" then (adv (); Some (term ns)) else expected in
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
      let cname = ident () in
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
      let body = term ~expected:rty ns_body in
      let meth = List.fold_right (fun x b -> Lam (x, b)) meth_binders body in
      arms := (cname, meth) :: !arms
    done;
    eat RBRACE "}";
    let arms = List.rev !arms in
    let names_of = List.map fst arms in
    let find c = try List.assoc c arms with Not_found -> fail ("match: missing case for '" ^ c ^ "'") in
    (* the motive: for the decreasing match it is the def's return type as a
       function of the moved arguments (read off the annotation, lifted into
       scope); otherwise the plain result type R *)
    let motive () =
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
  let decl ns =
    match peek () with
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
        Def (name, ty, body)
    | ID "check" -> adv (); Check (term ns)
    | ID "eval" -> adv (); Eval (term ns)
    | ID "import" -> adv (); (match peek () with STR p -> adv (); Import p | _ -> fail "expected a \"path\" after import")
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
        Hashtbl.replace datatypes name ();      (* register early so constructor types can be recursive *)
        let ns_ctor = List.fold_left (fun a (pn, _) -> pn :: a) ns ps in
        (* the datatype applied to all its parameters, as it appears under `depth` binders *)
        let applied_data_tm depth =
          List.fold_left (fun acc m -> App (acc, Var (k - 1 - m + depth))) (Data name) (List.init k (fun m -> m))
        in
        let rec no_vars = function
          | Var _ -> false
          | U _ | Bool | True | False | Nat | Zero | Refl | Data _ | Con _ | Elim _ | StringT | Str _
          | IntT | IntLit _ -> true
          | Pi (_, a, b) | Sig (_, a, b) | App (a, b) | Pair (a, b) | Ann (a, b) | StrApp (a, b) | StrEq (a, b)
          | IntAdd (a, b) | IntSub (a, b) | IntMul (a, b) | IntEq (a, b) | IntLt (a, b) -> no_vars a && no_vars b
          | Lam (_, b) | Suc b | Fst b | Snd b | IntFromNat b -> no_vars b
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
          Hashtbl.replace ctors cname (k + n);
          (cname, argtys)
        in
        let rec many acc =
          let c = parse_ctor () in
          match peek () with
          | COMMA -> adv (); (match peek () with RBRACE -> List.rev (c :: acc) | _ -> many (c :: acc))
          | _ -> List.rev (c :: acc)
        in
        let cs = (match peek () with RBRACE -> [] | _ -> many []) in
        eat RBRACE "}";
        Hashtbl.replace elims (name ^ "_elim") (name, k + 1 + List.length cs + 1);
        Hashtbl.replace data_info name (k, cs);
        List.iter (fun (cn, _) -> Hashtbl.replace ctor_owner cn name) cs;
        Data_decl (name, ps, cs)
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
      | Import _ -> ())   (* imports are expanded before we get here *)
    decls

let run (src : string) : unit = run_decls (parse (tokenize src))
