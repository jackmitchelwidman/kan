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
type tok = LP | RP | ARR | STAR | COMMA | COLON | DOT | LAM | EQ | LBRACE | RBRACE | ID of string | NUM of int | STR of string | EOF

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
    else if c = '{' then (push LBRACE; incr i)
    else if c = '}' then (push RBRACE; incr i)
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
      push (NUM (int_of_string (String.sub s !i (!j - !i)))); i := !j
    end
    else failwith (Printf.sprintf "type-theory lexer: unexpected character '%c'" c)
  done;
  push EOF;
  Array.of_list (List.rev !out)

(* -------- parser: names -> de Bruijn core terms -------- *)

let reserved_head = [ "Id"; "transp"; "fst"; "snd"; "if"; "suc"; "natElim" ]
let decl_kw = [ "def"; "check"; "eval"; "data"; "import" ]

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
let ctors : (string, int) Hashtbl.t = Hashtbl.create 32           (* ctor -> arity *)
let elims : (string, string * int) Hashtbl.t = Hashtbl.create 16  (* elim -> (datatype, #methods) *)
let reset_tables () = Hashtbl.reset datatypes; Hashtbl.reset ctors; Hashtbl.reset elims

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
  let starts_atom = function LP | NUM _ -> true | ID x -> not (List.mem x decl_kw) | _ -> false in
  let rec term ns =
    match peek () with
    | LAM ->
        adv ();
        let rec names acc = match peek () with ID x -> adv (); names (x :: acc) | DOT -> adv (); List.rev acc | _ -> fail "expected lambda binders then '.'" in
        let bs = names [] in
        let ns' = List.fold_left (fun a x -> x :: a) ns bs in
        let body = term ns' in
        List.fold_right (fun x b -> Lam (x, b)) bs body
    | LP when (match peek2 () with ID _ -> true | _ -> false) && peek3 () = COLON ->
        adv (); let x = ident () in eat COLON ":"; let a = term ns in eat RP ")";
        let ns' = x :: ns in
        (match peek () with
         | ARR -> adv (); Pi (x, a, term ns')
         | STAR -> adv (); Sig (x, a, term ns')
         | _ -> fail "expected '->' or '*' after (x : A)")
    | _ ->
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
    | ID "Bool" -> adv (); Bool
    | ID "true" -> adv (); True
    | ID "false" -> adv (); False
    | ID "Nat" -> adv (); Nat
    | ID "zero" -> adv (); Zero
    | NUM k -> adv (); let rec mk i = if i <= 0 then Zero else Suc (mk (i - 1)) in mk k
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
  in
  let decl ns =
    match peek () with
    | ID "def" ->
        adv (); let name = ident () in
        let ty = (match peek () with COLON -> adv (); Some (term ns) | _ -> None) in
        eat EQ "="; let body = term ns in Def (name, ty, body)
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
          | U _ | Bool | True | False | Nat | Zero | Refl | Data _ | Con _ | Elim _ -> true
          | Pi (_, a, b) | Sig (_, a, b) | App (a, b) | Pair (a, b) | Ann (a, b) -> no_vars a && no_vars b
          | Lam (_, b) | Suc b | Fst b | Snd b -> no_vars b
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
