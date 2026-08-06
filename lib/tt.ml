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
type tok = LP | RP | ARR | STAR | COMMA | COLON | DOT | LAM | EQ | ID of string | EOF

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
    else if c = '=' then (push EQ; incr i)
    else if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_' then begin
      let j = ref !i in
      while !j < n && is_a s.[!j] do incr j done;
      push (ID (String.sub s !i (!j - !i))); i := !j
    end
    else failwith (Printf.sprintf "type-theory lexer: unexpected character '%c'" c)
  done;
  push EOF;
  Array.of_list (List.rev !out)

(* -------- parser: names -> de Bruijn core terms -------- *)

let reserved_head = [ "Id"; "transp"; "fst"; "snd" ]
let decl_kw = [ "def"; "check"; "eval" ]

let index_of (x : string) (ns : string list) : int option =
  let rec go i = function [] -> None | y :: _ when y = x -> Some i | _ :: t -> go (i + 1) t in
  go 0 ns

type decl = Def of string * tm option * tm | Check of tm | Eval of tm

let parse (toks : tok array) : decl list =
  let pos = ref 0 in
  let peek () = toks.(!pos) in
  let peek2 () = if !pos + 1 < Array.length toks then toks.(!pos + 1) else EOF in
  let peek3 () = if !pos + 2 < Array.length toks then toks.(!pos + 2) else EOF in
  let adv () = incr pos in
  let fail m = failwith ("type-theory parse error: " ^ m) in
  let eat t m = if peek () = t then adv () else fail ("expected " ^ m) in
  let ident () = match peek () with ID x -> adv (); x | _ -> fail "expected a name" in
  let starts_atom = function LP -> true | ID x -> not (List.mem x decl_kw) | _ -> false in
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
    let base =
      match peek () with
      | ID "Id" -> adv (); let a = atom ns in let b = atom ns in let c = atom ns in Id (a, b, c)
      | ID "transp" ->
          adv (); let a = atom ns in let p = atom ns in let x = atom ns in
          let y = atom ns in let pe = atom ns in let d = atom ns in Transp (a, p, x, y, pe, d)
      | ID "fst" -> adv (); Fst (atom ns)
      | ID "snd" -> adv (); Snd (atom ns)
      | _ -> atom ns
    in
    let rec spine b = if starts_atom (peek ()) then spine (App (b, atom ns)) else b in
    spine base
  and atom ns =
    match peek () with
    | ID ("U" | "Type") -> adv (); U
    | ID "refl" -> adv (); Refl
    | ID x when List.mem x reserved_head -> fail (x ^ " must be applied to its arguments")
    | ID x when List.mem x decl_kw -> fail ("unexpected '" ^ x ^ "'")
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
    | _ -> fail "expected a declaration (def / check / eval)"
  in
  (* interleave: each def extends the name scope for later decls *)
  let rec loop ns acc =
    if peek () = EOF then List.rev acc
    else
      let d = decl ns in
      let ns' = match d with Def (name, _, _) -> name :: ns | _ -> ns in
      loop ns' (d :: acc)
  in
  loop [] []

(* -------- driver: elaborate, check, report -------- *)

let run (src : string) : unit =
  let decls = parse (tokenize src) in
  let ctx = ref empty in
  let names = ref [] in
  let sh t = show ~ns:!names t in
  let nf t = quote !ctx.lvl (eval !ctx.env t) in
  List.iter
    (fun d ->
      match d with
      | Def (name, ty, body) ->
          let vty =
            match ty with
            | Some t -> check !ctx t VU; eval !ctx.env t
            | None -> infer !ctx body
          in
          check !ctx body vty;
          let v = eval !ctx.env body in
          Printf.printf "def %-6s : %s\n" name (sh (quote !ctx.lvl vty));
          ctx := { env = v :: !ctx.env; types = vty :: !ctx.types; lvl = !ctx.lvl + 1 };
          names := name :: !names
      | Check t ->
          let ty = infer !ctx t in
          Printf.printf "check    : %s\n           = %s\n" (sh (quote !ctx.lvl ty)) (sh (nf t))
      | Eval t -> Printf.printf "eval     : %s\n" (sh (nf t)))
    decls
