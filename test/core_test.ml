(* Phase 2 milestone 1 — exercise the dependent type checker (lib/core.ml). *)

open Core

let () =
  (* the dependent identity: id : (A : U) -> (x : A) -> A := \A. \x. x
     de Bruijn: inside the body, x = index 0, A = index 1. *)
  let idty = Pi ("A", U, Pi ("x", Var 0, Var 1)) in
  let idtm = Ann (Lam ("A", Lam ("x", Var 0)), idty) in

  print_endline "Kan core — dependent type checker (Phase 2, milestone 1)";
  print_endline "lambda-Pi with normalization-by-evaluation + bidirectional checking";
  print_newline ();

  (* it type-checks, and we recover its type *)
  Printf.printf "id   := %s\n" (show idtm);
  Printf.printf "  |- id : %s\n\n" (show (type_of idtm));

  (* dependent application: the return type depends on the argument *)
  let idU = App (idtm, U) in
  Printf.printf "id U : %s   (return type depends on the argument)\n" (show (type_of idU));
  Printf.printf "       normalizes to  %s\n\n" (show (normalize idU));

  (* computation via NbE: id returns its argument *)
  let e = App (App (idtm, idty), idtm) in
  Printf.printf "id idty idtm : %s\n" (show (type_of e));
  Printf.printf "  normalizes to  %s   (the argument, unchanged)\n\n" (show (normalize e));

  (* ill-typed terms are rejected, with a message *)
  let expect_reject label t =
    match (try ignore (type_of t); None with Type_error m -> Some m) with
    | Some m -> Printf.printf "  ok  rejected %-16s  (%s)\n" label m
    | None -> Printf.printf "  !!  WRONGLY ACCEPTED %s\n" label
  in
  print_endline "ill-typed terms are rejected:";
  expect_reject "(U U)" (App (U, U));
  expect_reject "(U : (x:U)->x)" (Ann (U, Pi ("x", U, Var 0)));

  print_newline ();
  print_endline "Type checker works: dependent function types, NbE, definitional equality."
