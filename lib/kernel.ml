(* ============================================================================
   Kan — the fill kernel (library)
   ----------------------------------------------------------------------------
   ONE operation, `fill`, solves an extension problem along an inclusion at a
   chosen *modality*; composition, limits, colimits, and folds are all special
   cases (README §4). Semantic universe: FinSet (finite sets and functions),
   plus finite trees for initial algebras.

   This module is the shared core used by both the demo runner
   (`reference/kan_ref.ml`) and the surface-language interpreter (`bin/kan.ml`).
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
   completes.                                                                  *)

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
        lim D = { (x_j)_j ∈ ∏_j D(j) | ∀ (u:j→k). D(u)(x_j) = x_k }          *)

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

(* ======================= Initial algebras & folds =========================
   A recursive datatype is the *initial algebra* of a polynomial (signature)
   endofunctor F. μF is the set of finite trees; for ANY F-algebra (A, α) there
   is a UNIQUE homomorphism cata α : μF → A — the catamorphism (`fold`), which
   is a universal fill of the initial-algebra horn.                            *)

type ctor = { cname : string; payload : int; arity : int }
(* payload = cardinality of the finite parameter at the node (1 = none);
   arity = number of recursive subterms. F(X) = Σ_c payload_c · X^(arity_c). *)

type signature = ctor array

(* Values of μF: finite trees. `Node` itself is the structure map in : F(μF)→μF. *)
type tree = Node of int * int * tree array

(* An F-algebra with carrier 'a: one action per constructor. *)
type 'a algebra = int -> int -> 'a array -> 'a

(* THE FOLD — the unique homomorphism μF → A. *)
let rec cata (alg : 'a algebra) (t : tree) : 'a =
  match t with
  | Node (c, p, kids) -> alg c p (Array.map (cata alg) kids)

let fill_fold (alg : 'a algebra) (m : modality) : tree -> 'a =
  match m with
  | Universal -> cata alg
  | Exists -> failwith "the initial-algebra horn asks for the universal filler (fold)"

(* Is `t` an element of μF for the functor `sg`? *)
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
