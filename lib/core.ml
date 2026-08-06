(* ============================================================================
   Kan core type theory.
   ----------------------------------------------------------------------------
   A small but SOUND dependent type theory: the substrate in which Kan states
   and checks the properties `fill` must satisfy (README §5).

   Contents:
     - λΠ + Σ + a predicative UNIVERSE HIERARCHY (U 0 : U 1 : U 2 : …).
     - The identity type (Id, refl, transport) — equality, for commuting diagrams.
     - Bool (true, false, if) — a base type, so the theory has closed values to
       compute with.
     - Normalization by evaluation, definitional equality, bidirectional checking.

   No Type-in-Type: `U i : U (i+1)` and `Pi/Sig/Id` land in the max of their
   components' levels. Non-cumulative (simple and sound); cumulativity is a
   later ergonomic refinement.
   ========================================================================== *)

type tm =
  | Var of int
  | U of int                          (* U i : U (i+1) *)
  | Pi of string * tm * tm
  | Lam of string * tm
  | App of tm * tm
  | Sig of string * tm * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Id of tm * tm * tm
  | Refl
  | Transp of tm * tm * tm * tm * tm * tm
  | Bool
  | True
  | False
  | If of tm * tm * tm                (* non-dependent: if c then t else e *)
  | Nat
  | Zero
  | Suc of tm
  | NatElim of tm * tm * tm * tm      (* dependent induction: natElim P z s n : P n *)
  | Data of string                    (* a user-declared datatype, by name *)
  | Con of string * tm list           (* a constructor applied: c a1 .. an *)
  | Elim of string * tm * tm list * tm (* the datatype's eliminator: elim_D P methods target *)
  | Ann of tm * tm

(* closed Nat numerals -> int, for display *)
let rec nat_int = function
  | Zero -> Some 0
  | Suc t -> (match nat_int t with Some k -> Some (k + 1) | None -> None)
  | _ -> None

(* ---- registry of user-declared datatypes ----
   Each constructor argument is (name, type, is-recursive-occurrence-of-the-datatype). *)
type ctor_spec = { cs_name : string; cs_args : (string * tm * bool) list }
type data_spec = { ds_ctors : ctor_spec list }

let (sigenv : (string, data_spec) Hashtbl.t) = Hashtbl.create 16
let (ctor_data : (string, string) Hashtbl.t) = Hashtbl.create 32   (* ctor -> datatype *)

let declare_data (name : string) (ctors : ctor_spec list) : unit =
  Hashtbl.replace sigenv name { ds_ctors = ctors };
  List.iter (fun cs -> Hashtbl.replace ctor_data cs.cs_name name) ctors

let ctor_index (ds : data_spec) (c : string) : int * ctor_spec =
  let rec go i = function
    | cs :: _ when cs.cs_name = c -> (i, cs)
    | _ :: t -> go (i + 1) t
    | [] -> failwith ("unknown constructor " ^ c)
  in
  go 0 ds.ds_ctors

type value =
  | VVar of int
  | VApp of value * value
  | VU of int
  | VPi of string * value * closure
  | VLam of string * closure
  | VSig of string * value * closure
  | VPair of value * value
  | VFst of value
  | VSnd of value
  | VId of value * value * value
  | VRefl
  | VTransp of value * value * value * value * value * value
  | VBool
  | VTrue
  | VFalse
  | VIf of value * value * value      (* neutral scrutinee *)
  | VNat
  | VZero
  | VSuc of value
  | VNatElim of value * value * value * value   (* neutral target *)
  | VData of string
  | VCon of string * value list
  | VElim of string * value * value list * value  (* neutral target *)

and closure = { env : value list; body : tm }

(* -------- Normalization by Evaluation -------- *)

let rec eval (env : value list) (t : tm) : value =
  match t with
  | Var i -> List.nth env i
  | U i -> VU i
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
  | Bool -> VBool
  | True -> VTrue
  | False -> VFalse
  | If (c, t, e) -> vif (eval env c) (eval env t) (eval env e)
  | Nat -> VNat
  | Zero -> VZero
  | Suc n -> VSuc (eval env n)
  | NatElim (p, z, s, n) -> vnatelim (eval env p) (eval env z) (eval env s) (eval env n)
  | Data d -> VData d
  | Con (c, args) -> VCon (c, List.map (eval env) args)
  | Elim (d, m, ms, t) -> velim d (eval env m) (List.map (eval env) ms) (eval env t)
  | Ann (t, _) -> eval env t

and vapp f a = match f with VLam (_, c) -> inst c a | _ -> VApp (f, a)
and vfst v = match v with VPair (a, _) -> a | _ -> VFst v
and vsnd v = match v with VPair (_, b) -> b | _ -> VSnd v
and vtransp a p x y pe d = match pe with VRefl -> d | _ -> VTransp (a, p, x, y, pe, d)
and vif c t e = match c with VTrue -> t | VFalse -> e | _ -> VIf (c, t, e)
and vnatelim p z s n =
  match n with
  | VZero -> z
  | VSuc m -> vapp (vapp s m) (vnatelim p z s m)
  | _ -> VNatElim (p, z, s, n)
and velim d motive methods target =
  match target with
  | VCon (c, args) ->
      let ds = Hashtbl.find sigenv d in
      let i, cs = ctor_index ds c in
      let m = List.nth methods i in
      (* induction hypotheses: recurse on the recursive arguments, in order *)
      let ihs =
        List.concat
          (List.map2 (fun (_, _, rc) a -> if rc then [ velim d motive methods a ] else []) cs.cs_args args)
      in
      List.fold_left vapp m (args @ ihs)
  | _ -> VElim (d, motive, methods, target)
and inst c v = eval (v :: c.env) c.body

let rec quote (l : int) (v : value) : tm =
  match v with
  | VVar x -> Var (l - x - 1)
  | VApp (f, a) -> App (quote l f, quote l a)
  | VU i -> U i
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
  | VBool -> Bool
  | VTrue -> True
  | VFalse -> False
  | VIf (c, t, e) -> If (quote l c, quote l t, quote l e)
  | VNat -> Nat
  | VZero -> Zero
  | VSuc n -> Suc (quote l n)
  | VNatElim (p, z, s, n) -> NatElim (quote l p, quote l z, quote l s, quote l n)
  | VData d -> Data d
  | VCon (c, args) -> Con (c, List.map (quote l) args)
  | VElim (d, m, ms, t) -> Elim (d, quote l m, List.map (quote l) ms, quote l t)

let normalize (t : tm) : tm = quote 0 (eval [] t)

(* weakening: shift free variables (index >= cutoff) up by d *)
let rec lift d c t =
  match t with
  | Var i -> if i >= c then Var (i + d) else Var i
  | U _ | Bool | True | False | Nat | Zero | Refl | Data _ -> t
  | Pi (x, a, b) -> Pi (x, lift d c a, lift d (c + 1) b)
  | Lam (x, b) -> Lam (x, lift d (c + 1) b)
  | App (f, a) -> App (lift d c f, lift d c a)
  | Sig (x, a, b) -> Sig (x, lift d c a, lift d (c + 1) b)
  | Pair (a, b) -> Pair (lift d c a, lift d c b)
  | Fst t -> Fst (lift d c t)
  | Snd t -> Snd (lift d c t)
  | Id (a, x, y) -> Id (lift d c a, lift d c x, lift d c y)
  | Transp (a, p, x, y, pe, dd) -> Transp (lift d c a, lift d c p, lift d c x, lift d c y, lift d c pe, lift d c dd)
  | If (a, b, e) -> If (lift d c a, lift d c b, lift d c e)
  | Suc t -> Suc (lift d c t)
  | NatElim (p, z, s, n) -> NatElim (lift d c p, lift d c z, lift d c s, lift d c n)
  | Con (cn, args) -> Con (cn, List.map (lift d c) args)
  | Elim (dn, m, ms, tg) -> Elim (dn, lift d c m, List.map (lift d c) ms, lift d c tg)
  | Ann (t, ty) -> Ann (lift d c t, lift d c ty)

(* The type of the method for constructor `cs`, given the eliminator's motive term `mot`
   (in the current context). For c with args a1:A1 .. an:An (Ai closed; some recursive),
   the method has type:
      (a1:A1) -> .. -> (an:An) -> (ih_j : P a_{rec j}) .. -> P (c a1 .. an)                 *)
let method_type (mot : tm) (cs : ctor_spec) : tm =
  let args = cs.cs_args in
  let n = List.length args in
  let rec_positions = List.mapi (fun i (_, _, r) -> (i, r)) args |> List.filter snd |> List.map fst in
  let r = List.length rec_positions in
  let codomain =
    App (lift (n + r) 0 mot, Con (cs.cs_name, List.init n (fun i -> Var (n + r - 1 - i))))
  in
  let arg_binders = List.mapi (fun i (name, ty, _) -> (name, lift i 0 ty)) args in
  let ih_binders =
    List.mapi (fun j p -> ("ih", App (lift (n + j) 0 mot, Var (n + j - 1 - p)))) rec_positions
  in
  List.fold_right (fun (nm, ty) body -> Pi (nm, ty, body)) (arg_binders @ ih_binders) codomain

let rec conv (l : int) (a : value) (b : value) : bool =
  match a, b with
  | VU i, VU j -> i = j
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
  | VBool, VBool -> true
  | VTrue, VTrue -> true
  | VFalse, VFalse -> true
  | VIf (c, t, e), VIf (c', t', e') -> conv l c c' && conv l t t' && conv l e e'
  | VNat, VNat -> true
  | VZero, VZero -> true
  | VSuc a, VSuc b -> conv l a b
  | VNatElim (p, z, s, n), VNatElim (p', z', s', n') ->
      conv l p p' && conv l z z' && conv l s s' && conv l n n'
  | VData a, VData b -> a = b
  | VCon (c, xs), VCon (c', ys) -> c = c' && List.length xs = List.length ys && List.for_all2 (conv l) xs ys
  | VElim (d, m, ms, t), VElim (d', m', ms', t') ->
      d = d' && conv l m m' && List.length ms = List.length ms' && List.for_all2 (conv l) ms ms' && conv l t t'
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
  | If (c, t, e), ty -> check ctx c VBool; check ctx t ty; check ctx e ty
  | _ ->
      let inferred = infer ctx t in
      if not (conv ctx.lvl inferred ty) then
        fail (Printf.sprintf "type mismatch: have %s, expected %s"
                (show (quote ctx.lvl inferred)) (show (quote ctx.lvl ty)))

and infer (ctx : ctx) (t : tm) : value =
  match t with
  | Var i -> (match List.nth_opt ctx.types i with Some ty -> ty | None -> fail (Printf.sprintf "unbound variable %d" i))
  | U i -> VU (i + 1)
  | Pi (_, a, b) -> let i = infer_univ ctx a in let j = infer_univ (bind ctx (eval ctx.env a)) b in VU (max i j)
  | Sig (_, a, b) -> let i = infer_univ ctx a in let j = infer_univ (bind ctx (eval ctx.env a)) b in VU (max i j)
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
  | Id (a, x, y) -> let i = infer_univ ctx a in let va = eval ctx.env a in check ctx x va; check ctx y va; VU i
  | Transp (a, p, x, y, pe, d) ->
      let i = infer_univ ctx a in
      let va = eval ctx.env a in
      check ctx p (VPi ("_", va, { env = []; body = U i }));   (* motive P : A -> U i *)
      let vp = eval ctx.env p in
      check ctx x va; check ctx y va;
      let vx = eval ctx.env x and vy = eval ctx.env y in
      check ctx pe (VId (va, vx, vy));
      check ctx d (vapp vp vx);
      vapp vp vy
  | Bool -> VU 0
  | True | False -> VBool
  | If (c, t, e) -> check ctx c VBool; let ct = infer ctx t in check ctx e ct; ct
  | Nat -> VU 0
  | Zero -> VNat
  | Suc n -> check ctx n VNat; VNat
  | NatElim (p, z, s, n) ->
      (* motive  P : Nat -> U 0  (level-0 families; the common case) *)
      check ctx p (VPi ("_", VNat, { env = []; body = U 0 }));
      let vp = eval ctx.env p in
      check ctx z (vapp vp VZero);                         (* base : P zero *)
      (* step : (k : Nat) -> P k -> P (suc k)  — built directly as a value *)
      let s_ty =
        VPi ("k", VNat,
             { env = [ vp ]; body = Pi ("_", App (Var 1, Var 0), App (Var 2, Suc (Var 1))) })
      in
      check ctx s s_ty;
      check ctx n VNat;
      vapp vp (eval ctx.env n)                             (* result : P n *)
  | Data _ -> VU 0                                         (* user datatypes live in U 0 *)
  | Con (c, args) ->
      let d = (try Hashtbl.find ctor_data c with Not_found -> fail ("unknown constructor " ^ c)) in
      let ds = Hashtbl.find sigenv d in
      let _, cs = ctor_index ds c in
      if List.length args <> List.length cs.cs_args then
        fail (Printf.sprintf "constructor %s expects %d argument(s), got %d" c (List.length cs.cs_args) (List.length args));
      List.iter2 (fun (_, ty, _) a -> check ctx a (eval ctx.env ty)) cs.cs_args args;
      VData d
  | Elim (d, motive, methods, target) ->
      let ds = (try Hashtbl.find sigenv d with Not_found -> fail ("unknown datatype " ^ d)) in
      if List.length methods <> List.length ds.ds_ctors then
        fail (Printf.sprintf "elim %s expects %d method(s), got %d" d (List.length ds.ds_ctors) (List.length methods));
      check ctx motive (VPi ("_", VData d, { env = []; body = U 0 }));   (* motive P : D -> U 0 *)
      List.iter2 (fun cs m -> check ctx m (eval ctx.env (method_type motive cs))) ds.ds_ctors methods;
      check ctx target (VData d);
      vapp (eval ctx.env motive) (eval ctx.env target)     (* result : P target *)
  | Ann (tm, ty) -> ignore (infer_univ ctx ty); let vty = eval ctx.env ty in check ctx tm vty; vty

and infer_univ (ctx : ctx) (t : tm) : int =
  match infer ctx t with
  | VU i -> i
  | o -> fail (Printf.sprintf "expected a type, but %s : %s" (show (quote ctx.lvl (eval ctx.env t))) (show (quote ctx.lvl o)))

and show ?(ns = []) (t : tm) : string =
  let dom a = match a with Pi _ | Sig _ -> "(" ^ show ~ns a ^ ")" | _ -> show ~ns a in
  match t with
  | Var i -> (match List.nth_opt ns i with Some n -> n | None -> "@" ^ string_of_int i)
  | U 0 -> "U"
  | U i -> "U" ^ string_of_int i
  | Pi ("_", a, b) -> Printf.sprintf "%s -> %s" (dom a) (show ~ns:("_" :: ns) b)
  | Pi (x, a, b) -> Printf.sprintf "(%s : %s) -> %s" x (show ~ns a) (show ~ns:(x :: ns) b)
  | Lam (x, b) -> Printf.sprintf "\\%s. %s" x (show ~ns:(x :: ns) b)
  | App (f, a) -> Printf.sprintf "(%s %s)" (show ~ns f) (show ~ns a)
  | Sig ("_", a, b) -> Printf.sprintf "%s * %s" (dom a) (show ~ns:("_" :: ns) b)
  | Sig (x, a, b) -> Printf.sprintf "(%s : %s) * %s" x (show ~ns a) (show ~ns:(x :: ns) b)
  | Pair (a, b) -> Printf.sprintf "(%s, %s)" (show ~ns a) (show ~ns b)
  | Fst t -> Printf.sprintf "%s.1" (show ~ns t)
  | Snd t -> Printf.sprintf "%s.2" (show ~ns t)
  | Id (a, x, y) -> Printf.sprintf "Id %s %s %s" (show ~ns a) (show ~ns x) (show ~ns y)
  | Refl -> "refl"
  | Transp (_, p, _, _, pe, d) -> Printf.sprintf "transp %s %s %s" (show ~ns p) (show ~ns pe) (show ~ns d)
  | Bool -> "Bool"
  | True -> "true"
  | False -> "false"
  | If (c, t, e) -> Printf.sprintf "if %s %s %s" (show ~ns c) (show ~ns t) (show ~ns e)
  | Nat -> "Nat"
  | Zero -> "0"
  | Suc t -> (match nat_int t with Some k -> string_of_int (k + 1) | None -> Printf.sprintf "suc %s" (show ~ns t))
  | NatElim (p, z, s, n) -> Printf.sprintf "natElim %s %s %s %s" (show ~ns p) (show ~ns z) (show ~ns s) (show ~ns n)
  | Data d -> d
  | Con (c, []) -> c
  | Con (c, args) -> "(" ^ c ^ " " ^ String.concat " " (List.map (show ~ns) args) ^ ")"
  | Elim (d, m, ms, t) ->
      Printf.sprintf "%s_elim %s %s %s" d (show ~ns m) (String.concat " " (List.map (show ~ns) ms)) (show ~ns t)
  | Ann (t, ty) -> Printf.sprintf "(%s : %s)" (show ~ns t) (show ~ns ty)

let type_of (t : tm) : tm = quote 0 (infer empty t)
