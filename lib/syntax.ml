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
       | _ -> failwith (Printf.sprintf "unexpected character '%c'" c));
      incr i
    end
  done;
  push TEOF;
  List.rev !toks

type expr =
  | EVar of string
  | EFillInner of string * string
  | EFillLimit of string
  | EFillColimit of string
  | EProduct of string list
  | ECoproduct of string list

type stmt =
  | SSet of string * int
  | SMap of string * string * string * int list
  | SDiagram of string * string list * (int * int * string) list
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
  let parse_expr () =
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
    | TIdent name -> adv (); EVar name
    | _ -> fail "expected an expression"
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
    | TIdent "let" ->
        adv (); let name = expect_ident () in expect TEq "="; SLet (name, parse_expr ())
    | TIdent "show" -> adv (); SShow (parse_expr ())
    | _ -> fail "expected a statement (set / map / diagram / let / show)"
  in
  let rec prog acc = match peek () with TEOF -> List.rev acc | _ -> prog (parse_stmt () :: acc) in
  prog []

let parse_string (s : string) : stmt list = parse (Array.of_list (tokenize s))
