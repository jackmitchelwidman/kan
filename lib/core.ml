(* ============================================================================
   Kan core type theory — Phase 2, milestone 1.
   ----------------------------------------------------------------------------
   A minimal DEPENDENT type theory: the substrate in which Kan will state and
   check the properties `fill` is meant to satisfy (a diagram commutes, a
   construction is universal). This module is deliberately tiny and standard
   (à la Coquand / elaboration-zoo):

     - λΠ: dependent function types (Pi), lambda, application, a universe.
     - Normalization by Evaluation (eval to values with closures, then quote).
     - Bidirectional type checking with definitional equality via NbE.

   Milestone 1 uses Type-in-Type (U : U). That is logically inconsistent as a
   proof system, but it is the correct small first step for a *computational*
   core; a universe hierarchy is a later, mechanical refinement.

   This is NOT yet wired to the surface `.kan` language — it is the kernel of
   the type layer, tested on its own first (see test/core_test.ml).
   ========================================================================== *)

(* -------- Syntax: terms use de Bruijn indices -------- *)

type tm =
  | Var of int                     (* de Bruijn index *)
  | U                              (* the universe, Type *)
  | Pi of string * tm * tm         (* (x : A) -> B *)
  | Lam of string * tm             (* \x. t *)
  | App of tm * tm
  | Ann of tm * tm                 (* (t : A) — annotation, lets us infer a lambda *)

(* -------- Semantic values use de Bruijn LEVELS -------- *)

type value =
  | VVar of int                    (* a free variable, by level (a "neutral") *)
  | VApp of value * value          (* a stuck application (neutral) *)
  | VU
  | VPi of string * value * closure
  | VLam of string * closure

and closure = { env : value list; body : tm }

(* -------- Normalization by Evaluation -------- *)

let rec eval (env : value list) (t : tm) : value =
  match t with
  | Var i -> List.nth env i
  | U -> VU
  | Pi (x, a, b) -> VPi (x, eval env a, { env; body = b })
  | Lam (x, b) -> VLam (x, { env; body = b })
  | App (f, a) -> vapp (eval env f) (eval env a)
  | Ann (t, _) -> eval env t

and vapp (f : value) (a : value) : value =
  match f with
  | VLam (_, c) -> inst c a
  | _ -> VApp (f, a)

and inst (c : closure) (v : value) : value = eval (v :: c.env) c.body

(* readback: turn a value back into a term, under `l` binders *)
let rec quote (l : int) (v : value) : tm =
  match v with
  | VVar x -> Var (l - x - 1)
  | VApp (f, a) -> App (quote l f, quote l a)
  | VU -> U
  | VPi (x, a, c) -> Pi (x, quote l a, quote (l + 1) (inst c (VVar l)))
  | VLam (x, c) -> Lam (x, quote (l + 1) (inst c (VVar l)))

let normalize (t : tm) : tm = quote 0 (eval [] t)

(* definitional equality: compare values, going under binders with fresh vars.
   Includes eta for functions. *)
let rec conv (l : int) (a : value) (b : value) : bool =
  match a, b with
  | VU, VU -> true
  | VVar x, VVar y -> x = y
  | VApp (f, x), VApp (g, y) -> conv l f g && conv l x y
  | VPi (_, a, c), VPi (_, a', c') ->
      conv l a a' && conv (l + 1) (inst c (VVar l)) (inst c' (VVar l))
  | VLam (_, c), VLam (_, c') -> conv (l + 1) (inst c (VVar l)) (inst c' (VVar l))
  | VLam (_, c), t | t, VLam (_, c) -> conv (l + 1) (inst c (VVar l)) (vapp t (VVar l))
  | _ -> false

(* -------- Bidirectional type checking -------- *)

type ctx = { env : value list; types : value list; lvl : int }

let empty = { env = []; types = []; lvl = 0 }

(* extend the context with a fresh variable of (value) type `a` *)
let bind (ctx : ctx) (a : value) : ctx =
  { env = VVar ctx.lvl :: ctx.env; types = a :: ctx.types; lvl = ctx.lvl + 1 }

exception Type_error of string
let fail msg = raise (Type_error msg)

let rec check (ctx : ctx) (t : tm) (ty : value) : unit =
  match t, ty with
  | Lam (_, b), VPi (_, a, c) -> check (bind ctx a) b (inst c (VVar ctx.lvl))
  | _ ->
      let inferred = infer ctx t in
      if not (conv ctx.lvl inferred ty) then
        fail (Printf.sprintf "type mismatch: have %s, expected %s"
                (show (quote ctx.lvl inferred)) (show (quote ctx.lvl ty)))

and infer (ctx : ctx) (t : tm) : value =
  match t with
  | Var i ->
      (match List.nth_opt ctx.types i with Some ty -> ty | None -> fail (Printf.sprintf "unbound variable %d" i))
  | U -> VU                         (* Type-in-Type *)
  | Pi (_, a, b) ->
      check ctx a VU;
      check (bind ctx (eval ctx.env a)) b VU;
      VU
  | Lam _ -> fail "cannot infer the type of a bare lambda; add an annotation"
  | App (f, a) ->
      (match infer ctx f with
       | VPi (_, ta, c) -> check ctx a ta; inst c (eval ctx.env a)
       | other -> fail (Printf.sprintf "expected a function, but got a %s" (show (quote ctx.lvl other))))
  | Ann (tm, ty) ->
      check ctx ty VU;
      let vty = eval ctx.env ty in
      check ctx tm vty;
      vty

(* -------- Pretty-printer (names threaded for display) -------- *)

and show ?(ns = []) (t : tm) : string =
  match t with
  | Var i -> (match List.nth_opt ns i with Some n -> n | None -> "@" ^ string_of_int i)
  | U -> "U"
  | Pi (x, a, b) -> Printf.sprintf "(%s : %s) -> %s" x (show ~ns a) (show ~ns:(x :: ns) b)
  | Lam (x, b) -> Printf.sprintf "\\%s. %s" x (show ~ns:(x :: ns) b)
  | App (f, a) -> Printf.sprintf "(%s %s)" (show ~ns f) (show ~ns a)
  | Ann (t, ty) -> Printf.sprintf "(%s : %s)" (show ~ns t) (show ~ns ty)

(* infer a closed term's type and return it as a (normal-form) term *)
let type_of (t : tm) : tm = quote 0 (infer empty t)
