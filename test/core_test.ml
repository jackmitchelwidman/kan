(* Phase 2 — exercise the dependent type checker (lib/core.ml).
   Milestone 2: Sigma types, identity types, and PROOFS (sym, ap) that the
   checker accepts — equality reasoning, the basis for "diagrams commute". *)

open Core

let ok label t =
  match (try Some (type_of t) with Type_error m -> Printf.printf "  !! %s failed: %s\n" label m; None) with
  | Some ty -> Printf.printf "  |- %-6s : %s\n" label (show ty)
  | None -> ()

let reject label t =
  match (try ignore (type_of t); None with Type_error m -> Some m) with
  | Some m -> Printf.printf "  ok  rejected %-18s (%s)\n" label m
  | None -> Printf.printf "  !!  WRONGLY ACCEPTED %s\n" label

let () =
  print_endline "Kan core — dependent type theory (Phase 2, milestone 2)";
  print_endline "lambda-Pi, Sigma, and identity types with refl + transport\n";

  (* dependent identity, as a warm-up *)
  let idty = Pi ("A", U, Pi ("x", Var 0, Var 1)) in
  let idtm = Ann (Lam ("A", Lam ("x", Var 0)), idty) in
  print_endline "== functions ==";
  ok "id" idtm;

  (* Sigma: a dependent pair (A : U) * A, packaged and projected *)
  print_endline "\n== dependent pairs (Sigma) ==";
  let sig_ty = Sig ("A", U, Var 0) in
  let pair = Ann (Pair (U, U), sig_ty) in          (* (U, U) : (A:U)*A *)
  ok "pair" pair;
  Printf.printf "  pair.1 normalizes to  %s\n" (show (normalize (Fst pair)));
  Printf.printf "  pair.2 normalizes to  %s\n" (show (normalize (Snd pair)));

  (* Identity type: refl, and a rejection when endpoints differ *)
  print_endline "\n== equality: refl ==";
  ok "refl_U" (Ann (Refl, Id (U, U, U)));           (* refl : Id U U U *)
  reject "refl bad" (Ann (Refl, Id (U, U, Pi ("x", U, U))));  (* U <> (x:U)->U *)

  (* PROOF: equality is symmetric.
     sym : (A:U)(a:A)(b:A)(p:Id A a b) -> Id A b a
         := \A a b p. transp A (\z. Id A z a) a b p refl                  *)
  print_endline "\n== proofs the checker accepts ==";
  let sym_ty =
    Pi ("A", U, Pi ("a", Var 0, Pi ("b", Var 1,
      Pi ("p", Id (Var 2, Var 1, Var 0), Id (Var 3, Var 1, Var 2)))))
  in
  let sym =
    Ann (Lam ("A", Lam ("a", Lam ("b", Lam ("p",
      Transp (Var 3, Lam ("z", Id (Var 4, Var 0, Var 3)), Var 2, Var 1, Var 0, Refl))))), sym_ty)
  in
  ok "sym" sym;

  (* PROOF: congruence — equal inputs give equal outputs (needed for diagrams).
     ap : (A:U)(B:U)(f:A->B)(a:A)(b:A)(p:Id A a b) -> Id B (f a) (f b)
        := \A B f a b p. transp A (\z. Id B (f a)(f z)) a b p refl        *)
  let ap_ty =
    Pi ("A", U, Pi ("B", U, Pi ("f", Pi ("_", Var 1, Var 1),
      Pi ("a", Var 2, Pi ("b", Var 3,
        Pi ("p", Id (Var 4, Var 1, Var 0),
          Id (Var 4, App (Var 3, Var 2), App (Var 3, Var 1))))))))
  in
  let ap =
    Ann (Lam ("A", Lam ("B", Lam ("f", Lam ("a", Lam ("b", Lam ("p",
      Transp (Var 5,
        Lam ("z", Id (Var 5, App (Var 4, Var 3), App (Var 4, Var 0))),
        Var 2, Var 1, Var 0, Refl))))))), ap_ty)
  in
  ok "ap" ap;

  (* computation: sym on refl is refl (transport along refl reduces) *)
  print_endline "\n== equality proofs compute ==";
  let sym_refl = App (App (App (App (sym, U), U), U), Refl) in   (* sym U U U refl *)
  Printf.printf "  sym U U U refl  normalizes to  %s\n" (show (normalize sym_refl));

  print_newline ();
  print_endline "The type theory proves symmetry and congruence of equality."
