(* ============================================================================
   Kan — Phase 1 reference interpreter
   ----------------------------------------------------------------------------
   Purpose: prove the seed of the language computes.

   The whole thesis (README §4) is that there is ONE operation, `fill`, that
   solves an extension problem along an inclusion at a chosen *modality*, and
   that everything else — composition, products, limits, colimits — is a
   special case of it. This file demonstrates exactly that, on real values.

   Semantic universe: FinSet (finite sets and functions), the smallest place
   where both composition and universal constructions are concrete and
   computable.

   Kernel:  fill : horn -> modality -> filler
     - fill (Inner (f,g))   Exists     = the composite  g∘f      (a horn filler)
     - fill (LimCone d)     Universal  = the limiting cone of d  (a Kan extension)
     - fill (ColCocone d)   Universal  = the colimiting cocone of d

   There is deliberately NO `compose`, NO `product`, NO `limit` primitive.
   Those names are results of `fill`.
   ========================================================================== *)

(* ----------------------------- FinSet --------------------------------------
   An object is a finite set; its elements are the integers 0 .. card-1.
   A morphism is a function, given by its table of images.                    *)

type obj = { card : int; name : string }

type mor = { dom : obj; cod : obj; tbl : int array }

let obj name card = { card; name }

let mor dom cod tbl =
  assert (Array.length tbl = dom.card);
  Array.iter (fun y -> assert (y >= 0 && y < cod.card)) tbl;
  { dom; cod; tbl }

let mor_equal (a : mor) (b : mor) =
  a.dom.card = b.dom.card && a.cod.card = b.cod.card && a.tbl = b.tbl

(* Raw composition of functions. This is an *implementation detail of the
   kernel*, never exposed to the language: the only way a Kan program obtains a
   composite is by filling an inner horn (see `fill` below). We also use it in
   the test harness to check universal properties. *)
let compose_raw (f : mor) (g : mor) : mor =
  (* f : A -> B , g : B -> C  ⇒  g∘f : A -> C *)
  assert (f.cod.card = g.dom.card);
  mor f.dom g.cod (Array.init f.dom.card (fun x -> g.tbl.(f.tbl.(x))))

let string_of_mor (f : mor) =
  Printf.sprintf "%s -> %s : [%s]" f.dom.name f.cod.name
    (String.concat "; " (Array.to_list (Array.map string_of_int f.tbl)))

(* --------------------------- Diagrams & cones ------------------------------
   A (finite) diagram is a functor from a shape category into FinSet, given
   concretely by its vertices and the morphisms between them. A cone/cocone is
   what a universal fill must be tested against.                              *)

type diagram = {
  verts : obj array;                  (* the objects D(j)                     *)
  arrs  : (int * int * mor) list;     (* (j,k,f):  f : D(j) -> D(k)           *)
}

let discrete verts = { verts; arrs = [] }

type cone   = { apex   : obj; legs   : mor array }  (* legs.(j)   : apex   -> D(j) *)
type cocone = { coapex : obj; colegs : mor array }  (* colegs.(j) : D(j)   -> coapex *)

(* ------------------------------- Horns -------------------------------------
   A horn is a partial diagram missing exactly one face — the thing `fill`
   completes. Three shapes suffice for Phase 1.                               *)

type horn =
  | Inner     of mor * mor   (* Λ²₁ : two composable edges; missing face = the composite *)
  | LimCone   of diagram     (* missing face = the limiting cone   *)
  | ColCocone of diagram     (* missing face = the colimiting cocone *)

type modality = Exists | Universal

(* The result of a fill. *)
type filler =
  | Edge  of mor
  | Limit of { lobj : obj; proj : mor array; mediate   : cone   -> mor }
  | Colim of { cobj : obj; incl : mor array; comediate : cocone -> mor }

(* ------------------------- Universal fillers -------------------------------
   A limit in FinSet is the set of tuples, one component per vertex, that are
   compatible with every arrow of the diagram:
        lim D = { (x_j)_j ∈ ∏_j D(j) | ∀ (u:j→k). D(u)(x_j) = x_k }
   The projections are the components; the mediating map sends an element of a
   test cone's apex to the unique compatible tuple it names — this is where the
   universal property is *computed*, not merely asserted.                     *)

let compute_limit (d : diagram) : filler =
  let n = Array.length d.verts in
  let tuples = ref [] in
  let cur = Array.make (max n 1) 0 in
  let rec loop j =
    if j = n then begin
      let ok = List.for_all (fun (a, b, f) -> f.tbl.(cur.(a)) = cur.(b)) d.arrs in
      if ok then tuples := Array.sub cur 0 n :: !tuples
    end else
      for v = 0 to d.verts.(j).card - 1 do
        cur.(j) <- v; loop (j + 1)
      done
  in
  if n = 0 then tuples := [ [||] ]   (* limit of the empty diagram = terminal object 1 *)
  else loop 0;
  let tuples = Array.of_list (List.rev !tuples) in
  let lobj = obj "lim" (Array.length tuples) in
  let proj =
    Array.init n (fun j -> mor lobj d.verts.(j) (Array.map (fun t -> t.(j)) tuples))
  in
  let mediate (c : cone) : mor =
    let tbl =
      Array.init c.apex.card (fun x ->
          let target = Array.init n (fun j -> c.legs.(j).tbl.(x)) in
          let idx = ref (-1) in
          Array.iteri (fun i t -> if t = target then idx := i) tuples;
          if !idx < 0 then failwith "cone does not factor through the limit";
          !idx)
    in
    mor c.apex lobj tbl
  in
  Limit { lobj; proj; mediate }

(* A colimit is the disjoint union of the vertices, quotiented by the relation
   the arrows generate — computed here with union–find.                       *)

let compute_colimit (d : diagram) : filler =
  let n = Array.length d.verts in
  let offset = Array.make (max n 1) 0 in
  let total = ref 0 in
  for j = 0 to n - 1 do
    offset.(j) <- !total; total := !total + d.verts.(j).card
  done;
  let total = !total in
  let parent = Array.init total (fun i -> i) in
  let rec find i = if parent.(i) = i then i else (let r = find parent.(i) in parent.(i) <- r; r) in
  let union a b = let ra = find a and rb = find b in if ra <> rb then parent.(ra) <- rb in
  List.iter
    (fun (a, b, f) ->
      for x = 0 to d.verts.(a).card - 1 do
        union (offset.(a) + x) (offset.(b) + f.tbl.(x))
      done)
    d.arrs;
  let class_of = Array.make (max total 1) (-1) in
  let ncls = ref 0 in
  for i = 0 to total - 1 do
    let r = find i in
    if class_of.(r) = -1 then (class_of.(r) <- !ncls; incr ncls)
  done;
  let cls i = class_of.(find i) in
  let cobj = obj "colim" !ncls in
  let incl =
    Array.init n (fun j ->
        mor d.verts.(j) cobj (Array.init d.verts.(j).card (fun x -> cls (offset.(j) + x))))
  in
  let rep_j = Array.make (max !ncls 1) (-1) and rep_x = Array.make (max !ncls 1) (-1) in
  for j = 0 to n - 1 do
    for x = 0 to d.verts.(j).card - 1 do
      let c = cls (offset.(j) + x) in
      if rep_j.(c) = -1 then (rep_j.(c) <- j; rep_x.(c) <- x)
    done
  done;
  let comediate (cc : cocone) : mor =
    let tbl = Array.init cobj.card (fun c -> cc.colegs.(rep_j.(c)).tbl.(rep_x.(c))) in
    mor cobj cc.coapex tbl
  in
  Colim { cobj; incl; comediate }

(* ============================== THE KERNEL =================================
   One operation. The modality selects how strong a solution to demand.       *)

let fill (h : horn) (m : modality) : filler =
  match h, m with
  | Inner (f, g), Exists ->
      assert (f.cod.card = g.dom.card);   (* the edges must be composable *)
      Edge (compose_raw f g)
  | LimCone d,   Universal -> compute_limit d
  | ColCocone d, Universal -> compute_colimit d
  | Inner _, Universal ->
      failwith "inner horn asks only for existence of a filler, not a universal one"
  | (LimCone _ | ColCocone _), Exists ->
      failwith "a (co)limit horn asks for the universal filler; use Universal"

(* ================================ DEMOS =================================== *)

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

(* ======================= Initial algebras & folds =========================
   README §6: data and recursion. A recursive datatype is the *initial
   algebra* of a polynomial (signature) endofunctor F. Its carrier μF is the
   set of finite trees over the signature; the constructor `in : F(μF) → μF`
   is tree-building. For ANY F-algebra (A, α) there is a UNIQUE F-algebra
   homomorphism  cata α : μF → A — the catamorphism, a.k.a. `fold`.

   That uniqueness is a universal property, so `fold` is a *universal fill*:
   the initial-algebra horn is a target algebra, and filling it (Universal
   modality) produces the one homomorphism out of μF. This is the same
   operation as before, at a new semantic universe — finite trees — running
   alongside FinSet. (A single typed kernel spanning both universes is Phase 2;
   here `fill_fold` is kept as its own entry because its carrier type is
   arbitrary, which the monomorphic FinSet `filler` cannot hold.)             *)

type ctor = { cname : string; payload : int; arity : int }
(* A constructor of the functor F. `payload` = cardinality of the finite
   parameter carried at the node (1 = none); `arity` = number of recursive
   subterms. So F(X) = Σ_c  payload_c · X^(arity_c). *)

type signature = ctor array

(* Values of μF: finite trees. Node (c,p,kids) uses constructor index c,
   payload value p, and kids of length arity_c. `Node` itself is the
   structure map `in : F(μF) → μF`. *)
type tree = Node of int * int * tree array

(* An F-algebra with carrier 'a: one action per constructor. *)
type 'a algebra = int -> int -> 'a array -> 'a
(* alg c p folded_kids  =  α_c (p, folded_kids) *)

(* THE FOLD — the unique homomorphism μF → A, defined structurally. *)
let rec cata (alg : 'a algebra) (t : tree) : 'a =
  match t with
  | Node (c, p, kids) -> alg c p (Array.map (cata alg) kids)

(* fold as a universal fill of the initial-algebra horn. *)
let fill_fold (alg : 'a algebra) (m : modality) : tree -> 'a =
  match m with
  | Universal -> cata alg
  | Exists -> failwith "the initial-algebra horn asks for the universal filler (fold)"

(* Well-formedness: is `t` an element of μF for the functor `sg`?
   Each node must use a valid constructor, a payload within range, and exactly
   arity-many subterms — i.e. the tree really lies in the initial algebra. *)
let rec wf (sg : signature) (t : tree) : bool =
  match t with
  | Node (c, p, kids) ->
      c >= 0 && c < Array.length sg
      &&
      let k = sg.(c) in
      p >= 0 && p < k.payload && Array.length kids = k.arity && Array.for_all (wf sg) kids

let show_functor (sg : signature) =
  String.concat " + "
    (Array.to_list
       (Array.map
          (fun k ->
            if k.arity = 0 then k.cname else Printf.sprintf "%s·X^%d" k.cname k.arity)
          sg))

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
  (* reflection:  cata in = id  — folding with the constructors rebuilds the tree *)
  let in_alg c p kids = Node (c, p, kids) in
  let lit n = Node (0, n, [||]) and add a b = Node (1, 0, [| a; b |]) in
  let e = add (lit 7) (add (lit 2) (lit 5)) in
  assert (fill_fold in_alg Universal e = e);
  print_endline "  ✓ reflection:  cata in = id      (cata in e = e)";
  (* fusion:  h an algebra hom α→β  ⇒  h ∘ cata α = cata β.
     α = list sum,  h = (·2),  β = (nil↦0, cons p y ↦ 2p+y). *)
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
  print_endline "Kan — Phase 1 reference interpreter";
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
