(* ============================================================================
   Kan — Phase 1 reference demos
   ----------------------------------------------------------------------------
   Proof that the seed computes. All constructions below go through the single
   `fill` kernel (see lib/kernel.ml). There is deliberately NO `compose`, NO
   `product`, NO `limit`, NO recursion primitive — those names are results of
   `fill`.  Run:  dune exec reference/kan_ref.exe   (or  ocaml over the lib).
   ========================================================================== *)

open Kernel

let demo_composition () =
  print_endline "== Demo 1 — composition IS a horn filling ==";
  let a = obj "A" 3 and b = obj "B" 2 and c = obj "C" 4 in
  let f = mor a b [| 0; 1; 1 |] in
  let g = mor b c [| 3; 2 |] in
  (match fill (Inner (f, g)) Exists with
   | Edge gf ->
       Printf.printf "  f = %s\n" (string_of_mor f);
       Printf.printf "  g = %s\n" (string_of_mor g);
       Printf.printf "  fill (Inner (f,g)) Exists  =  g∘f  =  %s\n" (string_of_mor gf);
       assert (gf.tbl = [| 3; 2; 2 |]);
       print_endline "  ✓ the composite was produced by `fill` alone — no compose primitive"
   | _ -> assert false);
  print_newline ()

let demo_product () =
  print_endline "== Demo 2 — the product A×B is a universal fill (limit of a discrete diagram) ==";
  let a = obj "A" 2 and b = obj "B" 3 in
  (match fill (LimCone (discrete [| a; b |])) Universal with
   | Limit { lobj; proj; mediate } ->
       Printf.printf "  |A|=%d |B|=%d  ⇒  |A×B|=%d (expected %d)\n"
         a.card b.card lobj.card (a.card * b.card);
       assert (lobj.card = a.card * b.card);
       Printf.printf "  π₁ = %s\n" (string_of_mor proj.(0));
       Printf.printf "  π₂ = %s\n" (string_of_mor proj.(1));
       let t = obj "T" 2 in
       let l0 = mor t a [| 0; 1 |] and l1 = mor t b [| 2; 0 |] in
       let u = mediate { apex = t; legs = [| l0; l1 |] } in
       Printf.printf "  ⟨l₀,l₁⟩ : T→A×B = %s\n" (string_of_mor u);
       assert (mor_equal (compose_raw u proj.(0)) l0);
       assert (mor_equal (compose_raw u proj.(1)) l1);
       print_endline "  ✓ πᵢ∘⟨l₀,l₁⟩ = lᵢ — the universal property was computed, not assumed"
   | _ -> assert false);
  print_newline ()

let demo_pullback () =
  print_endline "== Demo 3 — a pullback is the SAME universal fill (limit of a cospan) ==";
  let a = obj "A" 3 and b = obj "B" 3 and c = obj "C" 2 in
  let f = mor a c [| 0; 0; 1 |] and g = mor b c [| 0; 1; 1 |] in
  let d = { verts = [| a; b; c |]; arrs = [ (0, 2, f); (1, 2, g) ] } in
  (match fill (LimCone d) Universal with
   | Limit { lobj; proj; _ } ->
       Printf.printf "  A ×_C B has %d elements\n" lobj.card;
       for i = 0 to lobj.card - 1 do
         let ai = proj.(0).tbl.(i) and bi = proj.(1).tbl.(i) in
         assert (f.tbl.(ai) = g.tbl.(bi))
       done;
       print_endline "  ✓ every pair (a,b) in the fill satisfies f(a)=g(b) — a real pullback"
   | _ -> assert false);
  print_newline ()

let demo_coproduct () =
  print_endline "== Demo 4 — the coproduct A+B is a universal fill (colimit of a discrete diagram) ==";
  let a = obj "A" 2 and b = obj "B" 3 in
  (match fill (ColCocone (discrete [| a; b |])) Universal with
   | Colim { cobj; incl; comediate } ->
       Printf.printf "  |A+B| = %d (expected %d)\n" cobj.card (a.card + b.card);
       assert (cobj.card = a.card + b.card);
       Printf.printf "  ι₁ = %s\n" (string_of_mor incl.(0));
       Printf.printf "  ι₂ = %s\n" (string_of_mor incl.(1));
       let t = obj "T" 4 in
       let r0 = mor a t [| 0; 1 |] and r1 = mor b t [| 1; 2; 3 |] in
       let u = comediate { coapex = t; colegs = [| r0; r1 |] } in
       Printf.printf "  [r₀,r₁] : A+B→T = %s\n" (string_of_mor u);
       assert (mor_equal (compose_raw incl.(0) u) r0);
       assert (mor_equal (compose_raw incl.(1) u) r1);
       print_endline "  ✓ [r₀,r₁]∘ιᵢ = rᵢ — universal property computed"
   | _ -> assert false);
  print_newline ()

let demo_nat () =
  print_endline "== Demo 5 — recursion is a fold: ℕ as the initial algebra of F(X)=1+X ==";
  let nat = [| { cname = "Zero"; payload = 1; arity = 0 };
               { cname = "Succ"; payload = 1; arity = 1 } |] in
  Printf.printf "  F(X) = %s\n" (show_functor nat);
  let zero = Node (0, 0, [||]) in
  let succ n = Node (1, 0, [| n |]) in
  let rec of_int n = if n <= 0 then zero else succ (of_int (n - 1)) in
  assert (wf nat (of_int 5));
  let value_alg c _ kids = match c with 0 -> 0 | 1 -> 1 + kids.(0) | _ -> assert false in
  let value = fill_fold value_alg Universal in
  Printf.printf "  fold value (of_int 5) = %d\n" (value (of_int 5));
  assert (value (of_int 5) = 5);
  assert (value (of_int 0) = 0);
  print_endline "  ✓ produced by a universal fill of the initial-algebra horn — no primitive recursion";
  print_newline ()

let demo_list () =
  print_endline "== Demo 6 — fold over List A: sum and length as universal fills ==";
  let list_sig = [| { cname = "Nil";  payload = 1;   arity = 0 };
                    { cname = "Cons"; payload = 100; arity = 1 } |] in
  Printf.printf "  F(X) = %s   (payload of Cons carries the element)\n" (show_functor list_sig);
  let nil = Node (0, 0, [||]) in
  let cons a t = Node (1, a, [| t |]) in
  let of_list xs = List.fold_right cons xs nil in
  assert (wf list_sig (of_list [ 3; 1; 4; 1; 5 ]));
  let sum_alg    c p kids = match c with 0 -> 0 | 1 -> p + kids.(0) | _ -> assert false in
  let length_alg c _ kids = match c with 0 -> 0 | 1 -> 1 + kids.(0) | _ -> assert false in
  let xs = of_list [ 3; 1; 4; 1; 5 ] in
  Printf.printf "  sum    [3;1;4;1;5] = %d\n" (fill_fold sum_alg    Universal xs);
  Printf.printf "  length [3;1;4;1;5] = %d\n" (fill_fold length_alg Universal xs);
  assert (fill_fold sum_alg    Universal xs = 14);
  assert (fill_fold length_alg Universal xs = 5);
  print_endline "  ✓ two different algebras, one fill operation, real values";
  print_newline ()

let demo_expr () =
  print_endline "== Demo 7 — fold IS an interpreter: evaluating an expression tree ==";
  let expr_sig = [| { cname = "Lit"; payload = 100; arity = 0 };
                    { cname = "Add"; payload = 1;   arity = 2 };
                    { cname = "Mul"; payload = 1;   arity = 2 } |] in
  Printf.printf "  F(X) = %s\n" (show_functor expr_sig);
  let lit n = Node (0, n, [||]) in
  let add a b = Node (1, 0, [| a; b |]) in
  let mul a b = Node (2, 0, [| a; b |]) in
  let eval_alg c p kids =
    match c with 0 -> p | 1 -> kids.(0) + kids.(1) | 2 -> kids.(0) * kids.(1) | _ -> assert false
  in
  let e = mul (add (lit 2) (lit 3)) (lit 4) in   (* (2+3)*4 *)
  assert (wf expr_sig e);
  Printf.printf "  eval ((2+3)*4) = %d\n" (fill_fold eval_alg Universal e);
  assert (fill_fold eval_alg Universal e = 20);
  print_endline "  ✓ the evaluator is the unique homomorphism out of the initial algebra";
  print_newline ()

let demo_fold_laws () =
  print_endline "== Demo 8 — the universal property, witnessed: reflection & fusion ==";
  let in_alg c p kids = Node (c, p, kids) in
  let lit n = Node (0, n, [||]) and add a b = Node (1, 0, [| a; b |]) in
  let e = add (lit 7) (add (lit 2) (lit 5)) in
  assert (fill_fold in_alg Universal e = e);
  print_endline "  ✓ reflection:  cata in = id      (cata in e = e)";
  let nil = Node (0, 0, [||]) in
  let cons a t = Node (1, a, [| t |]) in
  let of_list xs = List.fold_right cons xs nil in
  let sum_alg  c p kids = match c with 0 -> 0 | 1 -> p     + kids.(0) | _ -> assert false in
  let beta_alg c p kids = match c with 0 -> 0 | 1 -> 2 * p + kids.(0) | _ -> assert false in
  let h x = 2 * x in
  let xs = of_list [ 3; 1; 4; 1; 5 ] in
  assert (h (fill_fold sum_alg Universal xs) = fill_fold beta_alg Universal xs);
  Printf.printf "  ✓ fusion:      h ∘ cata α = cata β   (both = %d)\n"
    (fill_fold beta_alg Universal xs);
  print_newline ()

let () =
  print_endline "Kan — Phase 1 reference demos";
  print_endline "One operation: fill — complete a partial diagram, at a chosen modality.";
  print_newline ();
  print_endline "--- FinSet universe: structure ---";
  print_newline ();
  demo_composition ();
  demo_product ();
  demo_pullback ();
  demo_coproduct ();
  print_endline "--- Initial-algebra universe: data & recursion ---";
  print_newline ();
  demo_nat ();
  demo_list ();
  demo_expr ();
  demo_fold_laws ();
  print_endline "All demos passed.";
  print_endline
    "Composition, every universal construction, AND recursion each reduced to a single `fill`."
