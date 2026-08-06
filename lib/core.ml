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
  | Data of string                    (* a datatype/type-former head; applied to params via App *)
  | Con of string                     (* a constructor head; applied to params & args via App *)
  | Elim of string                    (* an eliminator head; applied to params, motive, methods, target *)
  | StringT                           (* the primitive type of strings *)
  | Str of string                     (* a string literal *)
  | StrApp of tm * tm                 (* string concatenation *)
  | StrEq of tm * tm                  (* string equality -> Bool *)
  | Ann of tm * tm

(* closed Nat numerals -> int, for display *)
let rec nat_int = function
  | Zero -> Some 0
  | Suc t -> (match nat_int t with Some k -> Some (k + 1) | None -> None)
  | _ -> None

(* ---- registry of user-declared (parameterized) datatypes ----
   A constructor argument is symbolic: a parameter, a recursive occurrence of the
   datatype (applied to the params), or a closed type. *)
type arg_ty = AParam of int | ARec | AClosed of tm
type ctor_spec = { cs_name : string; cs_args : (string * arg_ty) list }
type data_spec = {
  ds_name : string;
  ds_params : (string * tm) list;        (* parameter name and type *)
  ds_ctors : ctor_spec list;
  ds_former : tm;                        (* type-former's type: (params) -> U 0 *)
  ds_ctor_types : (string * tm) list;    (* each constructor's full type *)
  ds_elim_name : string;
  ds_elim_type : tm;                     (* the eliminator's full type *)
}

let (sigenv : (string, data_spec) Hashtbl.t) = Hashtbl.create 16
let (ctor_data : (string, string) Hashtbl.t) = Hashtbl.create 32   (* ctor -> datatype *)
let (elim_data : (string, string) Hashtbl.t) = Hashtbl.create 16   (* elim -> datatype *)

let ctor_index (ds : data_spec) (c : string) : int * ctor_spec =
  let rec go i = function
    | cs :: _ when cs.cs_name = c -> (i, cs)
    | _ :: t -> go (i + 1) t
    | [] -> failwith ("unknown constructor " ^ c)
  in
  go 0 ds.ds_ctors

(* small list helpers *)
let take n l = List.filteri (fun i _ -> i < n) l
let drop n l = List.filteri (fun i _ -> i >= n) l
let sub_list off len l = take len (drop off l)

(* Build closed dependent types by threading a name scope (innermost first),
   so de Bruijn indices are computed by lookup, not by hand. *)
let scope_index nm scope =
  let rec go i = function
    | [] -> failwith ("type builder: unbound " ^ nm)
    | x :: _ when x = nm -> i
    | _ :: t -> go (i + 1) t
  in
  go 0 scope

let rec build_pis scope binders codomain =
  match binders with
  | [] -> codomain scope
  | (name, mkty) :: rest -> Pi (name, mkty scope, build_pis (name :: scope) rest codomain)

let declare_data (name : string) (params : (string * tm) list) (ctors : ctor_spec list) : unit =
  let pnames = List.map fst params in
  let vref scope nm = Var (scope_index nm scope) in
  let applied_data scope = List.fold_left (fun acc p -> App (acc, vref scope p)) (Data name) pnames in
  let arg_tm aty scope =
    match aty with AParam i -> vref scope (List.nth pnames i) | ARec -> applied_data scope | AClosed t -> t
  in
  let param_binders = List.map (fun (pn, pty) -> (pn, fun _ -> pty)) params in
  let ds_former = build_pis [] param_binders (fun _ -> U 0) in
  let ctor_type cs =
    let arg_binders = List.map (fun (an, aty) -> (an, fun s -> arg_tm aty s)) cs.cs_args in
    build_pis [] (param_binders @ arg_binders) applied_data
  in
  let ds_ctor_types = List.map (fun cs -> (cs.cs_name, ctor_type cs)) ctors in
  (* the method for a constructor: (args) -> (ih per recursive arg) -> P (c params args) *)
  let method_type cs scope0 =
    let con_applied scope =
      List.fold_left (fun acc x -> App (acc, x)) (Con cs.cs_name)
        (List.map (vref scope) pnames @ List.map (fun (an, _) -> vref scope an) cs.cs_args)
    in
    let arg_binders = List.map (fun (an, aty) -> (an, fun s -> arg_tm aty s)) cs.cs_args in
    let ih_binders =
      List.filter_map
        (fun (an, aty) -> match aty with ARec -> Some ("ih_" ^ an, fun s -> App (vref s "P", vref s an)) | _ -> None)
        cs.cs_args
    in
    let rec go scope = function
      | [] -> App (vref scope "P", con_applied scope)
      | (nm, mkty) :: rest -> Pi (nm, mkty scope, go (nm :: scope) rest)
    in
    go scope0 (arg_binders @ ih_binders)
  in
  let elim_name = name ^ "_elim" in
  let p_binder = ("P", fun scope -> Pi ("_", applied_data scope, U 0)) in
  let method_binders = List.map (fun cs -> ("m_" ^ cs.cs_name, fun scope -> method_type cs scope)) ctors in
  let target_binder = ("t", fun scope -> applied_data scope) in
  let ds_elim_type =
    build_pis [] (param_binders @ [ p_binder ] @ method_binders @ [ target_binder ])
      (fun scope -> App (vref scope "P", vref scope "t"))
  in
  Hashtbl.replace sigenv name
    { ds_name = name; ds_params = params; ds_ctors = ctors; ds_former; ds_ctor_types;
      ds_elim_name = elim_name; ds_elim_type };
  List.iter (fun cs -> Hashtbl.replace ctor_data cs.cs_name name) ctors;
  Hashtbl.replace elim_data elim_name name

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
  | VData of string * value list       (* type former applied to a spine of arguments *)
  | VCon of string * value list        (* constructor applied to a spine (params ++ args) *)
  | VElim of string * value list       (* eliminator applied to a spine (stuck / accumulating) *)
  | VStringT
  | VStr of string
  | VStrApp of value * value           (* stuck concatenation *)
  | VStrEq of value * value            (* stuck equality *)

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
  | Data d -> VData (d, [])
  | Con c -> VCon (c, [])
  | Elim e -> VElim (e, [])
  | StringT -> VStringT
  | Str s -> VStr s
  | StrApp (a, b) -> vstrapp (eval env a) (eval env b)
  | StrEq (a, b) -> vstreq (eval env a) (eval env b)
  | Ann (t, _) -> eval env t

and vapp f a =
  match f with
  | VLam (_, c) -> inst c a
  | VData (d, sp) -> VData (d, sp @ [ a ])
  | VCon (c, sp) -> VCon (c, sp @ [ a ])
  | VElim (e, sp) -> velim e (sp @ [ a ])
  | _ -> VApp (f, a)
(* the eliminator's iota-rule: fires once the spine is complete and the target
   is a fully-applied constructor. *)
and velim e sp =
  let d = Hashtbl.find elim_data e in
  let ds = Hashtbl.find sigenv d in
  let np = List.length ds.ds_params and nc = List.length ds.ds_ctors in
  let arity = np + 1 + nc + 1 in
  if List.length sp <> arity then VElim (e, sp)
  else
    let params = take np sp in
    let motive = List.nth sp np in
    let methods = sub_list (np + 1) nc sp in
    let target = List.nth sp (arity - 1) in
    match target with
    | VCon (c, cargs) when List.mem_assoc c ds.ds_ctor_types
                           && List.length cargs = np + List.length (snd (ctor_index ds c)).cs_args ->
        let i, cs = ctor_index ds c in
        let own = drop np cargs in
        let m = List.nth methods i in
        let ihs =
          List.filter_map
            (fun ((_, aty), a) ->
              match aty with ARec -> Some (List.fold_left vapp (VElim (e, [])) (params @ [ motive ] @ methods @ [ a ])) | _ -> None)
            (List.combine cs.cs_args own)
        in
        List.fold_left vapp m (own @ ihs)
    | _ -> VElim (e, sp)
and vfst v = match v with VPair (a, _) -> a | _ -> VFst v
and vsnd v = match v with VPair (_, b) -> b | _ -> VSnd v
and vtransp a p x y pe d = match pe with VRefl -> d | _ -> VTransp (a, p, x, y, pe, d)
and vif c t e = match c with VTrue -> t | VFalse -> e | _ -> VIf (c, t, e)
and vnatelim p z s n =
  match n with
  | VZero -> z
  | VSuc m -> vapp (vapp s m) (vnatelim p z s m)
  | _ -> VNatElim (p, z, s, n)
and vstrapp a b = match a, b with VStr x, VStr y -> VStr (x ^ y) | _ -> VStrApp (a, b)
and vstreq a b = match a, b with VStr x, VStr y -> if x = y then VTrue else VFalse | _ -> VStrEq (a, b)
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
  | VData (d, sp) -> List.fold_left (fun acc v -> App (acc, quote l v)) (Data d) sp
  | VCon (c, sp) -> List.fold_left (fun acc v -> App (acc, quote l v)) (Con c) sp
  | VElim (e, sp) -> List.fold_left (fun acc v -> App (acc, quote l v)) (Elim e) sp
  | VStringT -> StringT
  | VStr s -> Str s
  | VStrApp (a, b) -> StrApp (quote l a, quote l b)
  | VStrEq (a, b) -> StrEq (quote l a, quote l b)

let normalize (t : tm) : tm = quote 0 (eval [] t)

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
  | VData (a, xs), VData (b, ys) -> a = b && List.length xs = List.length ys && List.for_all2 (conv l) xs ys
  | VCon (c, xs), VCon (c', ys) -> c = c' && List.length xs = List.length ys && List.for_all2 (conv l) xs ys
  | VElim (e, xs), VElim (e', ys) -> e = e' && List.length xs = List.length ys && List.for_all2 (conv l) xs ys
  | VStringT, VStringT -> true
  | VStr a, VStr b -> a = b
  | VStrApp (a, b), VStrApp (a', b') -> conv l a a' && conv l b b'
  | VStrEq (a, b), VStrEq (a', b') -> conv l a a' && conv l b b'
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
  | Data d -> (match Hashtbl.find_opt sigenv d with Some ds -> eval [] ds.ds_former | None -> fail ("unknown datatype " ^ d))
  | Con c ->
      (match Hashtbl.find_opt ctor_data c with
       | Some d -> eval [] (List.assoc c (Hashtbl.find sigenv d).ds_ctor_types)
       | None -> fail ("unknown constructor " ^ c))
  | Elim e ->
      (match Hashtbl.find_opt elim_data e with
       | Some d -> eval [] (Hashtbl.find sigenv d).ds_elim_type
       | None -> fail ("unknown eliminator " ^ e))
  | StringT -> VU 0
  | Str _ -> VStringT
  | StrApp (a, b) -> check ctx a VStringT; check ctx b VStringT; VStringT
  | StrEq (a, b) -> check ctx a VStringT; check ctx b VStringT; VBool
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
  | App _ ->
      (* flatten the application spine: (f a b c) rather than (((f a) b) c) *)
      let rec spine acc = function App (f, a) -> spine (a :: acc) f | h -> (h, acc) in
      let h, args = spine [] t in
      let p x = match x with Lam _ | Pi _ | Sig _ | Ann _ -> "(" ^ show ~ns x ^ ")" | _ -> show ~ns x in
      "(" ^ String.concat " " (List.map p (h :: args)) ^ ")"
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
  | Con c -> c
  | Elim e -> e
  | StringT -> "String"
  | Str s -> "\"" ^ s ^ "\""
  | StrApp (a, b) -> Printf.sprintf "strcat %s %s" (show ~ns a) (show ~ns b)
  | StrEq (a, b) -> Printf.sprintf "streq %s %s" (show ~ns a) (show ~ns b)
  | Ann (t, ty) -> Printf.sprintf "(%s : %s)" (show ~ns t) (show ~ns ty)

let type_of (t : tm) : tm = quote 0 (infer empty t)
