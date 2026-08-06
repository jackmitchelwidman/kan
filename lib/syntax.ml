(* ============================================================================
   Kan surface syntax — lexer, AST, recursive-descent parser.
   Shared by the interpreter (Interp) and the compiler (Compile).
   Grammar is documented in docs/surface-language.md.
   ========================================================================== *)

type token =
  | TIdent of string
  | TInt of int
  | TColon | TArrow
  | TLParen | TRParen | TLBrack | TRBrack | TLBrace | TRBrace
  | TComma | TEq
  | TPlus | TMinus | TStar
  | TEOF

let tokenize (s : string) : token list =
  let n = String.length s in
  let toks = ref [] in
  let i = ref 0 in
  let push t = toks := t :: !toks in
  let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_' in
  let is_digit c = c >= '0' && c <= '9' in
  let is_alnum c = is_alpha c || is_digit c in
  while !i < n do
    let c = s.[!i] in
    if c = ' ' || c = '\t' || c = '\r' || c = '\n' then incr i
    else if c = '-' && !i + 1 < n && s.[!i + 1] = '-' then
      while !i < n && s.[!i] <> '\n' do incr i done
    else if c = '-' && !i + 1 < n && s.[!i + 1] = '>' then (push TArrow; i := !i + 2)
    else if is_alpha c then begin
      let j = ref !i in
      while !j < n && is_alnum s.[!j] do incr j done;
      push (TIdent (String.sub s !i (!j - !i)));
      i := !j
    end
    else if is_digit c then begin
      let j = ref !i in
      while !j < n && is_digit s.[!j] do incr j done;
      push (TInt (int_of_string (String.sub s !i (!j - !i))));
      i := !j
    end
    else begin
      (match c with
       | ':' -> push TColon
       | '(' -> push TLParen
       | ')' -> push TRParen
       | '[' -> push TLBrack
       | ']' -> push TRBrack
       | '{' -> push TLBrace
       | '}' -> push TRBrace
       | ',' -> push TComma
       | '=' -> push TEq
       | '+' -> push TPlus
       | '-' -> push TMinus
       | '*' -> push TStar
       | _ -> failwith (Printf.sprintf "unexpected character '%c'" c));
      incr i
    end
  done;
  push TEOF;
  List.rev !toks

(* Arithmetic expressions — the body of a fold clause. *)
type aexpr =
  | AInt of int
  | AVar of string
  | AAdd of aexpr * aexpr
  | ASub of aexpr * aexpr
  | AMul of aexpr * aexpr

type expr =
  | EVar of string
  | EInt of int
  | EApp of string * expr list          (* constructor or fold application: head(args) *)
  | EFillInner of string * string
  | EFillLimit of string
  | EFillColimit of string
  | EProduct of string list
  | ECoproduct of string list

type ctor_decl = { cd_name : string; cd_payload : bool; cd_arity : int }
type fold_clause = { fc_ctor : string; fc_vars : string list; fc_body : aexpr }

type stmt =
  | SSet of string * int
  | SMap of string * string * string * int list
  | SDiagram of string * string list * (int * int * string) list
  | SData of string * ctor_decl list
  | SFold of string * string * fold_clause list   (* name, input datatype, clauses *)
  | SLet of string * expr
  | SShow of expr

let parse (toks : token array) : stmt list =
  let pos = ref 0 in
  let peek () = toks.(!pos) in
  let adv () = incr pos in
  let fail msg = failwith ("parse error: " ^ msg) in
  let expect_ident () = match peek () with TIdent s -> adv (); s | _ -> fail "expected an identifier" in
  let expect tok name = if peek () = tok then adv () else fail ("expected '" ^ name ^ "'") in
  let expect_int () = match peek () with TInt n -> adv (); n | _ -> fail "expected an integer" in
  let eat_kw kw = match peek () with TIdent s when s = kw -> adv () | _ -> fail ("expected '" ^ kw ^ "'") in
  let rec name_list () =
    let x = expect_ident () in
    match peek () with TComma -> adv (); x :: name_list () | _ -> [ x ]
  in
  let int_list () =
    match peek () with
    | TRBrack -> []
    | _ ->
        let rec loop () =
          let x = expect_int () in
          match peek () with TComma -> adv (); x :: loop () | _ -> [ x ]
        in
        loop ()
  in
  (* categorical / value expressions *)
  let rec parse_expr () =
    match peek () with
    | TIdent "fill" ->
        adv ();
        (match expect_ident () with
         | "inner" ->
             expect TLParen "("; let f = expect_ident () in
             expect TComma ","; let g = expect_ident () in
             expect TRParen ")"; EFillInner (f, g)
         | "limit" -> EFillLimit (expect_ident ())
         | "colimit" -> EFillColimit (expect_ident ())
         | other -> fail ("unknown fill modality '" ^ other ^ "' (want inner/limit/colimit)"))
    | TIdent "product" ->
        adv (); expect TLBrack "["; let ns = name_list () in expect TRBrack "]"; EProduct ns
    | TIdent "coproduct" ->
        adv (); expect TLBrack "["; let ns = name_list () in expect TRBrack "]"; ECoproduct ns
    | _ -> parse_atom ()
  and parse_atom () =
    match peek () with
    | TInt n -> adv (); EInt n
    | TLParen -> adv (); let e = parse_expr () in expect TRParen ")"; e
    | TIdent name ->
        adv ();
        if peek () = TLParen then begin
          adv ();
          let args = arg_list () in
          expect TRParen ")";
          EApp (name, args)
        end else EVar name
    | _ -> fail "expected an expression"
  and arg_list () =
    match peek () with
    | TRParen -> []
    | _ ->
        let rec loop () =
          let e = parse_expr () in
          match peek () with TComma -> adv (); e :: loop () | _ -> [ e ]
        in
        loop ()
  in
  (* arithmetic (fold bodies): + - at one level, * higher *)
  let rec parse_aexpr () =
    let t = parse_term () in
    let rec more acc =
      match peek () with
      | TPlus -> adv (); more (AAdd (acc, parse_term ()))
      | TMinus -> adv (); more (ASub (acc, parse_term ()))
      | _ -> acc
    in
    more t
  and parse_term () =
    let f = parse_factor () in
    let rec more acc = match peek () with TStar -> adv (); more (AMul (acc, parse_factor ())) | _ -> acc in
    more f
  and parse_factor () =
    match peek () with
    | TInt n -> adv (); AInt n
    | TIdent v -> adv (); AVar v
    | TLParen -> adv (); let e = parse_aexpr () in expect TRParen ")"; e
    | _ -> fail "expected an arithmetic factor"
  in
  let parse_ctor dataname =
    let name = expect_ident () in
    let rec fields payload arity =
      match peek () with
      | TIdent "int" ->
          if payload then fail ("constructor " ^ name ^ ": at most one int payload (Phase 1)");
          adv (); fields true arity
      | TIdent s when s = dataname -> adv (); fields payload (arity + 1)
      | TIdent s -> fail ("constructor " ^ name ^ ": unknown field '" ^ s ^ "' (want int or " ^ dataname ^ ")")
      | _ -> (payload, arity)
    in
    let payload, arity = fields false 0 in
    { cd_name = name; cd_payload = payload; cd_arity = arity }
  in
  let parse_clause () =
    let ctor = expect_ident () in
    let rec vars acc = match peek () with TIdent v -> adv (); vars (v :: acc) | _ -> List.rev acc in
    let vs = vars [] in
    expect TEq "=";
    { fc_ctor = ctor; fc_vars = vs; fc_body = parse_aexpr () }
  in
  (* comma-separated list inside { }, optional trailing comma *)
  let braced_list item =
    expect TLBrace "{";
    let rec loop acc =
      let x = item () in
      match peek () with
      | TComma -> adv (); (match peek () with TRBrace -> List.rev (x :: acc) | _ -> loop (x :: acc))
      | _ -> List.rev (x :: acc)
    in
    let xs = (match peek () with TRBrace -> [] | _ -> loop []) in
    expect TRBrace "}"; xs
  in
  let parse_stmt () =
    match peek () with
    | TIdent "set" ->
        adv (); let name = expect_ident () in expect TEq "="; let n = expect_int () in SSet (name, n)
    | TIdent "map" ->
        adv (); let name = expect_ident () in expect TColon ":";
        let dom = expect_ident () in expect TArrow "->"; let cod = expect_ident () in
        expect TEq "="; expect TLBrack "["; let tbl = int_list () in expect TRBrack "]";
        SMap (name, dom, cod, tbl)
    | TIdent "diagram" ->
        adv (); let name = expect_ident () in expect TLBrace "{";
        eat_kw "vertices"; let vs = name_list () in
        let rec edges acc =
          match peek () with
          | TIdent "edge" ->
              adv (); let i = expect_int () in let j = expect_int () in let m = expect_ident () in
              edges ((i, j, m) :: acc)
          | _ -> List.rev acc
        in
        let es = edges [] in
        expect TRBrace "}"; SDiagram (name, vs, es)
    | TIdent "data" ->
        adv (); let name = expect_ident () in
        SData (name, braced_list (fun () -> parse_ctor name))
    | TIdent "fold" ->
        adv (); let name = expect_ident () in expect TColon ":";
        let ty = expect_ident () in expect TArrow "->";
        let carrier = expect_ident () in
        if carrier <> "int" then fail "Phase 1 folds must target int";
        SFold (name, ty, braced_list parse_clause)
    | TIdent "let" ->
        adv (); let name = expect_ident () in expect TEq "="; SLet (name, parse_expr ())
    | TIdent "show" -> adv (); SShow (parse_expr ())
    | _ -> fail "expected a statement (set / map / diagram / data / fold / let / show)"
  in
  let rec prog acc = match peek () with TEOF -> List.rev acc | _ -> prog (parse_stmt () :: acc) in
  prog []

let parse_string (s : string) : stmt list = parse (Array.of_list (tokenize s))
