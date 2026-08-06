(* ============================================================================
   Kan core type theory — Phase 2.
   ----------------------------------------------------------------------------
   A small DEPENDENT type theory: the substrate in which Kan states and checks
   the properties `fill` must satisfy (a diagram commutes, a construction is
   universal, an extension is unique up to equivalence — README §5).

   Milestone 1: λΠ + normalization-by-evaluation + bidirectional checking.
   Milestone 2 (this file): Σ-types (dependent pairs) and the IDENTITY TYPE
     with `refl` and `transport` — enough to state and prove equalities, and
     hence to reason about commuting diagrams. `sym` and `ap` (congruence) are
     derived and type-checked in test/core_test.ml.

   Still Type-in-Type (U : U): correct for a computational core; a universe
   hierarchy is a later, mechanical refinement.
   ========================================================================== *)

(* -------- Syntax: de Bruijn indices -------- *)

type tm =
  | Var of int
  | U
  | Pi of string * tm * tm
  | Lam of string * tm
  | App of tm * tm
  | Sig of string * tm * tm          (* (x : A) * B — dependent pair type *)
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Id of tm * tm * tm               (* Id A a b — the identity/equality type *)
  | Refl                             (* checkable against Id A a a *)
  | Transp of tm * tm * tm * tm * tm * tm
      (* transp A P x y (p : Id A x y) (d : P x) : P y ;  transp .. refl d = d *)
  | Ann of tm * tm

(* -------- Values: de Bruijn levels -------- *)

type value =
  | VVar of int
  | VApp of value * value
  | VU
  | VPi of string * value * closure
  | VLam of string * closure
  | VSig of string * value * closure
  | VPair of value * value
  | VFst of value
  | VSnd of value
  | VId of value * value * value
  | VRefl
  | VTransp of value * value * value * value * value * value  (* neutral: the path arg is neutral *)

and closure = { env : value list; body : tm }

(* -------- Normalization by Evaluation -------- *)

let rec eval (env : value list) (t : tm) : value =
  match t with
  | Var i -> List.nth env i
  | U -> VU
  | Pi (x, a, b) -> VPi (x, eval env a, { env; body = b })
  | Lam (x, b) -> VLam (x, { env; body = b })
  | App (f, a) -> vapp (eval env f) (eval env a)
  | Sig (x, a, b) -> VSig (x, eval env a, { env; body = b })
  | Pair (t, u) -> VPair (eval env t, eval env u)
  | Fst t -> vfst (eval env t)
  | Snd t -> vsnd (eval env t)
  | Id (a, x, y) -> VId (eval env a, eval env x, eval env y)
  | Refl -> VRefl
  | Transp (a, p, x, y, pe, d) ->
      vtransp (eval env a) (eval env p) (eval env x) (eval env y) (eval env pe) (eval env d)
  | Ann (t, _) -> eval env t

and vapp f a = match f with VLam (_, c) -> inst c a | _ -> VApp (f, a)
and vfst v = match v with VPair (a, _) -> a | _ -> VFst v
and vsnd v = match v with VPair (_, b) -> b | _ -> VSnd v
and vtransp a p x y pe d = match pe with VRefl -> d | _ -> VTransp (a, p, x, y, pe, d)
and inst c v = eval (v :: c.env) c.body

let rec quote (l : int) (v : value) : tm =
  match v with
  | VVar x -> Var (l - x - 1)
  | VApp (f, a) -> App (quote l f, quote l a)
  | VU -> U
  | VPi (x, a, c) -> Pi (x, quote l a, quote (l + 1) (inst c (VVar l)))
  | VLam (x, c) -> Lam (x, quote (l + 1) (inst c (VVar l)))
  | VSig (x, a, c) -> Sig (x, quote l a, quote (l + 1) (inst c (VVar l)))
  | VPair (a, b) -> Pair (quote l a, quote l b)
  | VFst v -> Fst (quote l v)
  | VSnd v -> Snd (quote l v)
  | VId (a, x, y) -> Id (quote l a, quote l x, quote l y)
  | VRefl -> Refl
  | VTransp (a, p, x, y, pe, d) ->
      Transp (quote l a, quote l p, quote l x, quote l y, quote l pe, quote l d)

let normalize (t : tm) : tm = quote 0 (eval [] t)

let rec conv (l : int) (a : value) (b : value) : bool =
  match a, b with
  | VU, VU -> true
  | VVar x, VVar y -> x = y
  | VApp (f, x), VApp (g, y) -> conv l f g && conv l x y
  | VPi (_, a, c), VPi (_, a', c') -> conv l a a' && conv (l + 1) (inst c (VVar l)) (inst c' (VVar l))
  | VSig (_, a, c), VSig (_, a', c') -> conv l a a' && conv (l + 1) (inst c (VVar l)) (inst c' (VVar l))
  | VLam (_, c), VLam (_, c') -> conv (l + 1) (inst c (VVar l)) (inst c' (VVar l))
  | VLam (_, c), t | t, VLam (_, c) -> conv (l + 1) (inst c (VVar l)) (vapp t (VVar l))
  | VPair (a, b), VPair (a', b') -> conv l a a' && conv l b b'
  | VPair (a, b), t | t, VPair (a, b) -> conv l a (vfst t) && conv l b (vsnd t)
  | VFst a, VFst b -> conv l a b
  | VSnd a, VSnd b -> conv l a b
  | VId (a, x, y), VId (a', x', y') -> conv l a a' && conv l x x' && conv l y y'
  | VRefl, VRefl -> true
  | VTransp (a, p, x, y, pe, d), VTransp (a', p', x', y', pe', d') ->
      conv l a a' && conv l p p' && conv l x x' && conv l y y' && conv l pe pe' && conv l d d'
  | _ -> false

(* -------- Bidirectional type checking -------- *)

type ctx = { env : value list; types : value list; lvl : int }

let empty = { env = []; types = []; lvl = 0 }
let bind ctx a = { env = VVar ctx.lvl :: ctx.env; types = a :: ctx.types; lvl = ctx.lvl + 1 }

exception Type_error of string
let fail msg = raise (Type_error msg)

let rec check (ctx : ctx) (t : tm) (ty : value) : unit =
  match t, ty with
  | Lam (_, b), VPi (_, a, c) -> check (bind ctx a) b (inst c (VVar ctx.lvl))
  | Pair (t, u), VSig (_, a, c) -> check ctx t a; check ctx u (inst c (eval ctx.env t))
  | Refl, VId (_, x, y) ->
      if not (conv ctx.lvl x y) then
        fail (Printf.sprintf "refl: endpoints not definitionally equal: %s vs %s"
                (show (quote ctx.lvl x)) (show (quote ctx.lvl y)))
  | _ ->
      let inferred = infer ctx t in
      if not (conv ctx.lvl inferred ty) then
        fail (Printf.sprintf "type mismatch: have %s, expected %s"
                (show (quote ctx.lvl inferred)) (show (quote ctx.lvl ty)))

and infer (ctx : ctx) (t : tm) : value =
  match t with
  | Var i -> (match List.nth_opt ctx.types i with Some ty -> ty | None -> fail (Printf.sprintf "unbound variable %d" i))
  | U -> VU
  | Pi (_, a, b) -> check ctx a VU; check (bind ctx (eval ctx.env a)) b VU; VU
  | Sig (_, a, b) -> check ctx a VU; check (bind ctx (eval ctx.env a)) b VU; VU
  | Lam _ -> fail "cannot infer the type of a bare lambda; add an annotation"
  | Pair _ -> fail "cannot infer the type of a bare pair; add an annotation"
  | Refl -> fail "cannot infer refl; it needs an expected Id type"
  | App (f, a) ->
      (match infer ctx f with
       | VPi (_, ta, c) -> check ctx a ta; inst c (eval ctx.env a)
       | other -> fail (Printf.sprintf "expected a function, but got a %s" (show (quote ctx.lvl other))))
  | Fst t ->
      (match infer ctx t with VSig (_, a, _) -> a | o -> fail (Printf.sprintf "fst: expected a pair, got %s" (show (quote ctx.lvl o))))
  | Snd t ->
      (match infer ctx t with
       | VSig (_, _, c) -> inst c (vfst (eval ctx.env t))
       | o -> fail (Printf.sprintf "snd: expected a pair, got %s" (show (quote ctx.lvl o))))
  | Id (a, x, y) -> check ctx a VU; let va = eval ctx.env a in check ctx x va; check ctx y va; VU
  | Transp (a, p, x, y, pe, d) ->
      check ctx a VU;
      let va = eval ctx.env a in
      (* motive P : A -> U *)
      check ctx p (VPi ("_", va, { env = []; body = U }));
      let vp = eval ctx.env p in
      check ctx x va; check ctx y va;
      let vx = eval ctx.env x and vy = eval ctx.env y in
      check ctx pe (VId (va, vx, vy));
      check ctx d (vapp vp vx);
      vapp vp vy
  | Ann (tm, ty) -> check ctx ty VU; let vty = eval ctx.env ty in check ctx tm vty; vty

and show ?(ns = []) (t : tm) : string =
  match t with
  | Var i -> (match List.nth_opt ns i with Some n -> n | None -> "@" ^ string_of_int i)
  | U -> "U"
  | Pi (x, a, b) -> Printf.sprintf "(%s : %s) -> %s" x (show ~ns a) (show ~ns:(x :: ns) b)
  | Lam (x, b) -> Printf.sprintf "\\%s. %s" x (show ~ns:(x :: ns) b)
  | App (f, a) -> Printf.sprintf "(%s %s)" (show ~ns f) (show ~ns a)
  | Sig (x, a, b) -> Printf.sprintf "(%s : %s) * %s" x (show ~ns a) (show ~ns:(x :: ns) b)
  | Pair (a, b) -> Printf.sprintf "(%s, %s)" (show ~ns a) (show ~ns b)
  | Fst t -> Printf.sprintf "%s.1" (show ~ns t)
  | Snd t -> Printf.sprintf "%s.2" (show ~ns t)
  | Id (a, x, y) -> Printf.sprintf "Id %s %s %s" (show ~ns a) (show ~ns x) (show ~ns y)
  | Refl -> "refl"
  | Transp (_, p, _, _, pe, d) -> Printf.sprintf "transp %s %s %s" (show ~ns p) (show ~ns pe) (show ~ns d)
  | Ann (t, ty) -> Printf.sprintf "(%s : %s)" (show ~ns t) (show ~ns ty)

let type_of (t : tm) : tm = quote 0 (infer empty t)
