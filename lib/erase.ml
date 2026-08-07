(* ============================================================================
   Type erasure — the bridge from the dependent core to a compilable language.
   ----------------------------------------------------------------------------
   Erases the dependent type theory (lib/core.ml) to an untyped functional IR:
   types and proofs become a dummy value; eliminators become recursion. This IR
   is target-independent — a backend (OCaml first, then C) compiles it. Here we
   also give a reference evaluator, so we can check that erasure preserves the
   computational meaning (erased result == the checker's `eval`).
   ========================================================================== *)

open Core

(* -------- untyped IR -------- *)
type iexpr =
  | IVar of int
  | ILam of iexpr
  | IApp of iexpr * iexpr
  | IPair of iexpr * iexpr
  | IFst of iexpr
  | ISnd of iexpr
  | IConH of string          (* constructor head, applied via IApp *)
  | IElimH of string         (* eliminator head, applied via IApp *)
  | IBool of bool
  | IIf of iexpr * iexpr * iexpr
  | INat of int
  | ISuc of iexpr
  | INatElim of iexpr * iexpr * iexpr
  | IStr of string
  | IStrApp of iexpr * iexpr
  | IStrEq of iexpr * iexpr
  | IInt of Bigint.t
  | IIntAdd of iexpr * iexpr
  | IIntSub of iexpr * iexpr
  | IIntMul of iexpr * iexpr
  | IIntDiv of iexpr * iexpr
  | IIntGcd of iexpr * iexpr
  | IIntEq of iexpr * iexpr
  | IIntLt of iexpr * iexpr
  | IIntFromNat of iexpr
  | IUnit                    (* an erased type or proof *)

let rec erase (t : tm) : iexpr =
  match t with
  | Var i -> IVar i
  | Lam (_, b) -> ILam (erase b)
  | App (f, a) -> IApp (erase f, erase a)
  | Pair (a, b) -> IPair (erase a, erase b)
  | Fst t -> IFst (erase t)
  | Snd t -> ISnd (erase t)
  | True -> IBool true
  | False -> IBool false
  | If (c, t, e) -> IIf (erase c, erase t, erase e)
  | Zero -> INat 0
  | Suc n -> (match erase n with INat k -> INat (k + 1) | e -> ISuc e)
  | NatElim (_, z, s, n) -> INatElim (erase z, erase s, erase n)   (* motive erased *)
  | Con c -> IConH c
  | Elim e -> IElimH e
  | Str s -> IStr s
  | StrApp (a, b) -> IStrApp (erase a, erase b)
  | StrEq (a, b) -> IStrEq (erase a, erase b)
  | IntLit b -> IInt b
  | IntAdd (a, b) -> IIntAdd (erase a, erase b)
  | IntSub (a, b) -> IIntSub (erase a, erase b)
  | IntMul (a, b) -> IIntMul (erase a, erase b)
  | IntDiv (a, b) -> IIntDiv (erase a, erase b)
  | IntGcd (a, b) -> IIntGcd (erase a, erase b)
  | IntEq (a, b) -> IIntEq (erase a, erase b)
  | IntLt (a, b) -> IIntLt (erase a, erase b)
  | IntFromNat n -> IIntFromNat (erase n)
  | Transp (_, _, _, _, _, d) -> erase d                           (* transport is identity on its value *)
  | Ann (t, _) -> erase t
  | U _ | Pi _ | Sig _ | Id _ | Refl | Bool | Nat | Data _ | StringT | IntT -> IUnit  (* types & proofs erase *)

(* -------- reference runtime -------- *)
type ival =
  | VClo of (ival -> ival)
  | VConV of string * ival list
  | VElimV of string * ival list
  | VBoolV of bool
  | VNatV of int
  | VStrV of string
  | VIntV of Bigint.t
  | VPairV of ival * ival
  | VUnit

let rec iapp f a =
  match f with
  | VClo g -> g a
  | VUnit -> VUnit                       (* an erased type absorbs application *)
  | VConV (c, sp) -> VConV (c, sp @ [ a ])
  | VElimV (e, sp) -> ielim e (sp @ [ a ])
  | _ -> failwith "erased runtime: cannot apply a non-function"

and ielim e sp =
  let d = Hashtbl.find elim_data e in
  let ds = Hashtbl.find sigenv d in
  let np = List.length ds.ds_params and nc = List.length ds.ds_ctors in
  let arity = np + 1 + nc + 1 in
  if List.length sp <> arity then VElimV (e, sp)
  else
    let methods = sub_list (np + 1) nc sp in
    match List.nth sp (arity - 1) with
    | VConV (c, cargs) when List.length cargs = np + List.length (snd (ctor_index ds c)).cs_args ->
        let i, cs = ctor_index ds c in
        let own = drop np cargs in
        let m = List.nth methods i in
        let ihs =
          List.filter_map
            (fun ((_, aty), a) -> match aty with ARec -> Some (ielim e (sub_list 0 (np + 1 + nc) sp @ [ a ])) | _ -> None)
            (List.combine cs.cs_args own)
        in
        List.fold_left iapp m (own @ ihs)
    | _ -> VElimV (e, sp)

and ieval env t =
  match t with
  | IVar i -> List.nth env i
  | ILam b -> VClo (fun x -> ieval (x :: env) b)
  | IApp (f, a) -> iapp (ieval env f) (ieval env a)
  | IPair (a, b) -> VPairV (ieval env a, ieval env b)
  | IFst t -> (match ieval env t with VPairV (a, _) -> a | VUnit -> VUnit | _ -> failwith "fst")
  | ISnd t -> (match ieval env t with VPairV (_, b) -> b | VUnit -> VUnit | _ -> failwith "snd")
  | IConH c -> VConV (c, [])
  | IElimH e -> VElimV (e, [])
  | IBool b -> VBoolV b
  | IIf (c, t, e) -> (match ieval env c with VBoolV true -> ieval env t | VBoolV false -> ieval env e | _ -> failwith "if")
  | INat n -> VNatV n
  | ISuc e -> (match ieval env e with VNatV k -> VNatV (k + 1) | _ -> failwith "suc")
  | INatElim (z, s, n) ->
      (match ieval env n with
       | VNatV k ->
           let sv = ieval env s and zv = ieval env z in
           (* fold bottom-up so recursion depth is O(1), not O(k): a naive
              [go (k-1)] blows the stack once k reaches ~10^6 (e.g. fac 10). *)
           let acc = ref zv in
           for i = 0 to k - 1 do acc := iapp (iapp sv (VNatV i)) !acc done;
           !acc
       | _ -> failwith "natElim on a non-numeral")
  | IStr s -> VStrV s
  | IStrApp (a, b) -> (match ieval env a, ieval env b with VStrV x, VStrV y -> VStrV (x ^ y) | _ -> failwith "strcat")
  | IStrEq (a, b) -> (match ieval env a, ieval env b with VStrV x, VStrV y -> VBoolV (x = y) | _ -> failwith "streq")
  | IInt b -> VIntV b
  | IIntAdd (a, b) -> (match ieval env a, ieval env b with VIntV x, VIntV y -> VIntV (Bigint.add x y) | _ -> failwith "iadd")
  | IIntSub (a, b) -> (match ieval env a, ieval env b with VIntV x, VIntV y -> VIntV (Bigint.sub x y) | _ -> failwith "isub")
  | IIntMul (a, b) -> (match ieval env a, ieval env b with VIntV x, VIntV y -> VIntV (Bigint.mul x y) | _ -> failwith "imul")
  | IIntDiv (a, b) -> (match ieval env a, ieval env b with VIntV x, VIntV y -> VIntV (Bigint.div x y) | _ -> failwith "idiv")
  | IIntGcd (a, b) -> (match ieval env a, ieval env b with VIntV x, VIntV y -> VIntV (Bigint.gcd x y) | _ -> failwith "igcd")
  | IIntEq (a, b) -> (match ieval env a, ieval env b with VIntV x, VIntV y -> VBoolV (Bigint.equal x y) | _ -> failwith "ieq")
  | IIntLt (a, b) -> (match ieval env a, ieval env b with VIntV x, VIntV y -> VBoolV (Bigint.compare x y < 0) | _ -> failwith "ilt")
  | IIntFromNat n -> (match ieval env n with VNatV k -> VIntV (Bigint.of_int k) | _ -> failwith "fromNat")
  | IUnit -> VUnit

let rec ishow = function
  | VNatV n -> string_of_int n
  | VBoolV b -> if b then "true" else "false"
  | VStrV s -> "\"" ^ s ^ "\""
  | VIntV b -> Bigint.to_string b
  | VUnit -> "_"
  | VPairV (a, b) -> "(" ^ ishow a ^ ", " ^ ishow b ^ ")"
  | VConV (c, []) -> c
  | VConV (c, sp) -> "(" ^ c ^ " " ^ String.concat " " (List.map ishow sp) ^ ")"
  | VElimV (e, _) -> e ^ "<partial>"
  | VClo _ -> "<function>"

(* -------- run a parsed program through erasure -------- *)
let run (decls : Tt.decl list) : unit =
  let genv = ref [] in
  List.iter
    (fun d ->
      match d with
      | Tt.Data_decl (name, params, ctors) ->
          let specs =
            List.map (fun (cn, argtys) -> { cs_name = cn; cs_args = List.mapi (fun i a -> (Printf.sprintf "x%d" i, a)) argtys }) ctors
          in
          declare_data name params specs
      | Tt.Def (_, _, body) -> genv := ieval !genv (erase body) :: !genv
      | Tt.Eval body -> Printf.printf "%s\n" (ishow (ieval !genv (erase body)))
      | Tt.Check _ | Tt.Import _ -> ())
    decls
