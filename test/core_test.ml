(* Test suite for the dependent type checker (lib/core.ml).
   Positive cases (accepted + their types/normal forms) and negative cases
   (must be rejected). Exit code nonzero if any negative case is wrongly
   accepted, so this doubles as a regression check. *)

open Core

let failures = ref 0

let ok label t =
  match (try Some (type_of t) with Type_error m -> Printf.printf "  !! %-8s wrongly REJECTED: %s\n" label m; incr failures; None) with
  | Some ty -> Printf.printf "  ok  %-8s : %s\n" label (show ty)
  | None -> ()

let nf label t = Printf.printf "  ok  %-8s = %s\n" label (show (normalize t))

let reject label t =
  match (try ignore (type_of t); None with Type_error m -> Some m) with
  | Some m -> Printf.printf "  ok  rejected %-14s (%s)\n" label m
  | None -> Printf.printf "  !! WRONGLY ACCEPTED %s\n" label; incr failures

let () =
  print_endline "Kan core — dependent type theory (test suite)\n";

  print_endline "== universes (no Type-in-Type) ==";
  ok "U0" (U 0);            (* U 0 : U 1 *)
  ok "Bool" Bool;           (* Bool : U 0 = U *)

  print_endline "\n== functions ==";
  let idty = Pi ("A", U 0, Pi ("x", Var 0, Var 1)) in
  let idtm = Ann (Lam ("A", Lam ("x", Var 0)), idty) in
  ok "id" idtm;

  print_endline "\n== Bool computes ==";
  nf "if-t" (If (True, True, False));
  nf "if-f" (If (False, True, False));

  print_endline "\n== dependent pairs (Sigma) ==";
  let pair = Ann (Pair (Bool, True), Sig ("A", U 0, Var 0)) in   (* (Bool, true) : (A:U)*A *)
  ok "pair" pair;
  nf "pair.1" (Fst pair);
  nf "pair.2" (Snd pair);

  print_endline "\n== equality: refl ==";
  ok "refl" (Ann (Refl, Id (Bool, True, True)));

  print_endline "\n== proofs the checker accepts ==";
  let sym_ty =
    Pi ("A", U 0, Pi ("a", Var 0, Pi ("b", Var 1,
      Pi ("p", Id (Var 2, Var 1, Var 0), Id (Var 3, Var 1, Var 2)))))
  in
  let sym =
    Ann (Lam ("A", Lam ("a", Lam ("b", Lam ("p",
      Transp (Var 3, Lam ("z", Id (Var 4, Var 0, Var 3)), Var 2, Var 1, Var 0, Refl))))), sym_ty)
  in
  ok "sym" sym;
  let ap_ty =
    Pi ("A", U 0, Pi ("B", U 0, Pi ("f", Pi ("_", Var 1, Var 1),
      Pi ("a", Var 2, Pi ("b", Var 3,
        Pi ("p", Id (Var 4, Var 1, Var 0),
          Id (Var 4, App (Var 3, Var 2), App (Var 3, Var 1))))))))
  in
  let ap =
    Ann (Lam ("A", Lam ("B", Lam ("f", Lam ("a", Lam ("b", Lam ("p",
      Transp (Var 5, Lam ("z", Id (Var 5, App (Var 4, Var 3), App (Var 4, Var 0))),
        Var 2, Var 1, Var 0, Refl))))))), ap_ty)
  in
  ok "ap" ap;

  print_endline "\n== equality proofs compute (on a real closed value) ==";
  nf "sym-refl" (App (App (App (App (sym, Bool), True), True), Refl));

  print_endline "\n== Nat: inductive type with a dependent eliminator ==";
  ok "Nat" Nat;
  ok "two" (Suc (Suc Zero));
  (* add = \m n. natElim (\_.Nat) n (\k ih. suc ih) m *)
  let add =
    Ann (Lam ("m", Lam ("n",
      NatElim (Lam ("_", Nat), Var 0, Lam ("k", Lam ("ih", Suc (Var 0))), Var 1))),
      Pi ("_", Nat, Pi ("_", Nat, Nat)))
  in
  ok "add" add;
  nf "2+3" (App (App (add, Suc (Suc Zero)), Suc (Suc (Suc Zero))));   (* = 5 *)

  print_endline "\n== ill-typed terms are rejected ==";
  reject "natElim base" (NatElim (Lam ("_", Nat), True, Lam ("k", Lam ("ih", Suc (Var 0))), Zero));
  reject "refl bad" (Ann (Refl, Id (Bool, True, False)));   (* true <> false *)
  reject "U : U" (Ann (U 0, U 0));                          (* U 0 : U 1, not U 0 *)
  reject "apply Bool" (App (Bool, True));                   (* Bool is not a function *)
  reject "if mismatch" (If (True, Bool, True));             (* branches Bool vs true differ *)

  print_newline ();
  if !failures = 0 then print_endline "All checks passed."
  else (Printf.printf "%d FAILURE(S).\n" !failures; exit 1)
