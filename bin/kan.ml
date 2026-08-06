(* ============================================================================
   kan — the surface-language interpreter (Phase 1)
   ----------------------------------------------------------------------------
   Reads a .kan file, parses it, and runs it on the fill kernel (lib/kernel.ml).
   The surface deliberately centers on ONE keyword — `fill` — plus the sugar
   `product` / `coproduct`. Grammar (whitespace-insensitive; `--` comments):

     program ::= stmt*
     stmt    ::= "set" name "=" int
               | "map" name ":" name "->" name "=" "[" int-list "]"
               | "diagram" name "{" "vertices" namelist edge-list "}"
               | "let" name "=" expr
               | "show" expr
     expr    ::= "fill" "inner" "(" name "," name ")"   -- composition (Exists)
               | "fill" "limit"   name                  -- limit   of a diagram (Universal)
               | "fill" "colimit" name                  -- colimit of a diagram (Universal)
               | "product"   "[" namelist "]"           -- sugar: fill limit   of a discrete diagram
               | "coproduct" "[" namelist "]"           -- sugar: fill colimit of a discrete diagram
               | name                                   -- a previously bound value
   ========================================================================== *)

open Kernel

(* ------------------------------- Lexer ------------------------------------ *)

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

(* -------------------------------- AST ------------------------------------- *)

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

(* ------------------------------- Parser ----------------------------------- *)

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

(* ------------------------------ Evaluator --------------------------------- *)

type value =
  | VObj of obj
  | VMor of mor
  | VDiagram of diagram
  | VLimit of obj * mor array
  | VColim of obj * mor array

let run (stmts : stmt list) : unit =
  let env : (string, value) Hashtbl.t = Hashtbl.create 32 in
  let lookup name =
    match Hashtbl.find_opt env name with
    | Some v -> v
    | None -> failwith ("unbound name '" ^ name ^ "'")
  in
  let as_obj name = match lookup name with VObj o -> o | _ -> failwith (name ^ " is not a set") in
  let as_mor name = match lookup name with VMor m -> m | _ -> failwith (name ^ " is not a map") in
  let as_diagram name = match lookup name with VDiagram d -> d | _ -> failwith (name ^ " is not a diagram") in
  let eval e =
    match e with
    | EVar name -> lookup name
    | EFillInner (f, g) ->
        let ff = as_mor f and gg = as_mor g in
        if ff.cod.card <> gg.dom.card then
          failwith (Printf.sprintf "cannot fill inner horn: %s : ->%s and %s : %s-> are not composable"
                      f ff.cod.name g gg.dom.name);
        (match fill (Inner (ff, gg)) Exists with Edge m -> VMor m | _ -> assert false)
    | EFillLimit dn ->
        (match fill (LimCone (as_diagram dn)) Universal with
         | Limit { lobj; proj; _ } -> VLimit (lobj, proj) | _ -> assert false)
    | EFillColimit dn ->
        (match fill (ColCocone (as_diagram dn)) Universal with
         | Colim { cobj; incl; _ } -> VColim (cobj, incl) | _ -> assert false)
    | EProduct ns ->
        let objs = Array.of_list (List.map as_obj ns) in
        (match fill (LimCone (discrete objs)) Universal with
         | Limit { lobj; proj; _ } -> VLimit (lobj, proj) | _ -> assert false)
    | ECoproduct ns ->
        let objs = Array.of_list (List.map as_obj ns) in
        (match fill (ColCocone (discrete objs)) Universal with
         | Colim { cobj; incl; _ } -> VColim (cobj, incl) | _ -> assert false)
  in
  let show v =
    match v with
    | VObj o -> Printf.printf "%s : Set(%d)\n" o.name o.card
    | VMor m -> Printf.printf "%s\n" (string_of_mor m)
    | VDiagram d ->
        Printf.printf "diagram: %d vertices, %d edges\n" (Array.length d.verts) (List.length d.arrs)
    | VLimit (o, proj) ->
        Printf.printf "limit: %d elements\n" o.card;
        Array.iteri (fun i p -> Printf.printf "  proj[%d] = %s\n" i (string_of_mor p)) proj
    | VColim (o, incl) ->
        Printf.printf "colimit: %d elements\n" o.card;
        Array.iteri (fun i p -> Printf.printf "  incl[%d] = %s\n" i (string_of_mor p)) incl
  in
  List.iter
    (fun s ->
      match s with
      | SSet (name, n) ->
          if n < 0 then failwith (Printf.sprintf "set %s: size must be >= 0" name);
          Hashtbl.replace env name (VObj (obj name n))
      | SMap (name, dom, cod, tbl) ->
          let d = as_obj dom and c = as_obj cod in
          if List.length tbl <> d.card then
            failwith (Printf.sprintf "map %s: table has %d entries but domain %s has %d elements"
                        name (List.length tbl) dom d.card);
          List.iter
            (fun y ->
              if y < 0 || y >= c.card then
                failwith (Printf.sprintf "map %s: image %d is outside codomain %s (size %d)"
                            name y cod c.card))
            tbl;
          Hashtbl.replace env name (VMor (mor d c (Array.of_list tbl)))
      | SDiagram (name, vs, es) ->
          let verts = Array.of_list (List.map as_obj vs) in
          let nv = Array.length verts in
          let arrs =
            List.map
              (fun (i, j, mn) ->
                if i < 0 || i >= nv || j < 0 || j >= nv then
                  failwith (Printf.sprintf "diagram %s: edge endpoint out of range (have %d vertices)" name nv);
                let m = as_mor mn in
                if m.dom.card <> verts.(i).card || m.cod.card <> verts.(j).card then
                  failwith (Printf.sprintf "diagram %s: map %s does not match vertices %d -> %d" name mn i j);
                (i, j, m))
              es
          in
          Hashtbl.replace env name (VDiagram { verts; arrs })
      | SLet (name, e) -> Hashtbl.replace env name (eval e)
      | SShow e -> show (eval e))
    stmts

(* -------------------------------- Main ------------------------------------ *)

let () =
  match Sys.argv with
  | [| _; file |] ->
      let src =
        let ic = open_in_bin file in
        let len = in_channel_length ic in
        let s = really_input_string ic len in
        close_in ic; s
      in
      (try run (parse (Array.of_list (tokenize src)) )
       with e ->
         Printf.eprintf "kan: %s\n" (match e with Failure m -> m | _ -> Printexc.to_string e);
         exit 1)
  | _ ->
      prerr_endline "usage: kan <file.kan>";
      exit 1
