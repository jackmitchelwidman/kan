(* ============================================================================
   OCaml backend — compile the erased IR (lib/erase.ml) to OCaml source.
   ----------------------------------------------------------------------------
   A program becomes: a fixed runtime (a universal `ival` type + iapp/ielim/…),
   a generated datatype registry (constructor/eliminator arities), the `def`s as
   `let` bindings, and the `eval`s as prints. `kan build foo.ktt` then runs
   `ocamlopt` on it to produce a native binary. Type-checking happens in the same
   pass (via lib/core.ml), so `build` rejects ill-typed programs.
   ========================================================================== *)

open Core
open Erase

let prelude1 = {ml|type ival =
  | VClo of (ival -> ival)
  | VConV of string * ival list
  | VElimV of string * ival list
  | VBoolV of bool
  | VNatV of int
  | VStrV of string
  | VPairV of ival * ival
  | VUnit

let sublist off len l = List.filteri (fun i _ -> i >= off && i < off + len) l
let dropn n l = List.filteri (fun i _ -> i >= n) l
let ifst = function VPairV (a, _) -> a | VUnit -> VUnit | _ -> failwith "fst"
let isnd = function VPairV (_, b) -> b | VUnit -> VUnit | _ -> failwith "snd"
let iif c t e = match c with VBoolV true -> t () | VBoolV false -> e () | _ -> failwith "if"
let isuc = function VNatV k -> VNatV (k + 1) | _ -> failwith "suc"
let istrapp a b = match a, b with VStrV x, VStrV y -> VStrV (x ^ y) | _ -> failwith "strcat"
let istreq a b = match a, b with VStrV x, VStrV y -> VBoolV (x = y) | _ -> failwith "streq"
let rec ishow = function
  | VNatV n -> string_of_int n
  | VBoolV b -> if b then "true" else "false"
  | VStrV s -> "\"" ^ s ^ "\""
  | VUnit -> "_"
  | VPairV (a, b) -> "(" ^ ishow a ^ ", " ^ ishow b ^ ")"
  | VConV (c, []) -> c
  | VConV (c, sp) -> "(" ^ c ^ " " ^ String.concat " " (List.map ishow sp) ^ ")"
  | VElimV (e, _) -> e ^ "<partial>"
  | VClo _ -> "<fun>"
|ml}

let prelude2 = {ml|let rec iapp f a =
  match f with
  | VClo g -> g a
  | VUnit -> VUnit
  | VConV (c, sp) -> VConV (c, sp @ [ a ])
  | VElimV (e, sp) -> ielim e (sp @ [ a ])
  | _ -> failwith "cannot apply"
and ielim e sp =
  let np = elim_np e and nc = elim_nc e in
  let arity = np + 1 + nc + 1 in
  if List.length sp <> arity then VElimV (e, sp)
  else
    let methods = sublist (np + 1) nc sp in
    match List.nth sp (arity - 1) with
    | VConV (c, cargs) when List.length cargs = ctor_np c + List.length (ctor_recs c) ->
        let own = dropn np cargs in
        let m = List.nth methods (ctor_pos c) in
        let ihs = List.filter_map (fun (r, a) -> if r then Some (ielim e (sublist 0 (np + 1 + nc) sp @ [ a ])) else None) (List.combine (ctor_recs c) own) in
        List.fold_left iapp m (own @ ihs)
    | _ -> VElimV (e, sp)
let rec inatelim z s n =
  match n with
  | VNatV k -> let rec go k = if k <= 0 then z else iapp (iapp s (VNatV (k - 1))) (go (k - 1)) in go k
  | _ -> failwith "natElim"
|ml}

let fresh = let n = ref 0 in fun () -> incr n; "u" ^ string_of_int !n

let rec cexpr globals locals (e : iexpr) : string =
  let go = cexpr globals locals in
  match e with
  | IVar i -> if i < List.length locals then List.nth locals i else List.nth globals (i - List.length locals)
  | ILam b -> let v = fresh () in Printf.sprintf "(VClo (fun %s -> %s))" v (cexpr globals (v :: locals) b)
  | IApp (f, a) -> Printf.sprintf "(iapp %s %s)" (go f) (go a)
  | IPair (a, b) -> Printf.sprintf "(VPairV (%s, %s))" (go a) (go b)
  | IFst t -> Printf.sprintf "(ifst %s)" (go t)
  | ISnd t -> Printf.sprintf "(isnd %s)" (go t)
  | IConH c -> Printf.sprintf "(VConV (%S, []))" c
  | IElimH e -> Printf.sprintf "(VElimV (%S, []))" e
  | IBool b -> Printf.sprintf "(VBoolV %b)" b
  | IIf (c, t, e) -> Printf.sprintf "(iif %s (fun () -> %s) (fun () -> %s))" (go c) (go t) (go e)
  | INat n -> Printf.sprintf "(VNatV %d)" n
  | ISuc e -> Printf.sprintf "(isuc %s)" (go e)
  | INatElim (z, s, n) -> Printf.sprintf "(inatelim %s %s %s)" (go z) (go s) (go n)
  | IStr s -> Printf.sprintf "(VStrV %S)" s
  | IStrApp (a, b) -> Printf.sprintf "(istrapp %s %s)" (go a) (go b)
  | IStrEq (a, b) -> Printf.sprintf "(istreq %s %s)" (go a) (go b)
  | IUnit -> "VUnit"

let registry elims ctors =
  let case_i pairs = String.concat "" (List.map (fun (k, v) -> Printf.sprintf "  | %S -> %d\n" k v) pairs) in
  let elim_np = List.map (fun (e, np, _) -> (e, np)) elims in
  let elim_nc = List.map (fun (e, _, nc) -> (e, nc)) elims in
  let ctor_np = List.map (fun (c, np, _, _) -> (c, np)) ctors in
  let ctor_pos = List.map (fun (c, _, p, _) -> (c, p)) ctors in
  let ctor_recs =
    String.concat ""
      (List.map (fun (c, _, _, recs) -> Printf.sprintf "  | %S -> [%s]\n" c (String.concat "; " (List.map string_of_bool recs))) ctors)
  in
  Printf.sprintf
    "let elim_np = function\n%s  | _ -> failwith \"elim_np\"\nlet elim_nc = function\n%s  | _ -> failwith \"elim_nc\"\nlet ctor_np = function\n%s  | _ -> 0\nlet ctor_pos = function\n%s  | _ -> 0\nlet ctor_recs = function\n%s  | _ -> []\n"
    (case_i elim_np) (case_i elim_nc) (case_i ctor_np) (case_i ctor_pos) ctor_recs

(* type-check and compile in one pass *)
let compile (decls : Tt.decl list) : string =
  let ctx = ref empty in
  let globals = ref [] in
  let gi = ref 0 in
  let body = Buffer.create 4096 in
  let elims = ref [] and ctors = ref [] in
  List.iter
    (fun d ->
      match d with
      | Tt.Data_decl (name, params, cs) ->
          let specs = List.map (fun (cn, argtys) -> { cs_name = cn; cs_args = List.mapi (fun i a -> (Printf.sprintf "x%d" i, a)) argtys }) cs in
          declare_data name params specs;
          let np = List.length params and nc = List.length cs in
          elims := (name ^ "_elim", np, nc) :: !elims;
          List.iteri (fun pos (cn, argtys) -> ctors := (cn, np, pos, List.map (fun a -> a = ARec) argtys) :: !ctors) cs
      | Tt.Def (_, ty, tm) ->
          let vty = match ty with Some t -> ignore (infer_univ !ctx t); eval !ctx.env t | None -> infer !ctx tm in
          check !ctx tm vty;
          let g = Printf.sprintf "g%d" !gi in
          incr gi;
          Buffer.add_string body (Printf.sprintf "let %s = %s\n" g (cexpr !globals [] (erase tm)));
          ctx := { env = eval !ctx.env tm :: !ctx.env; types = vty :: !ctx.types; lvl = !ctx.lvl + 1 };
          globals := g :: !globals
      | Tt.Eval tm ->
          ignore (infer !ctx tm);
          Buffer.add_string body (Printf.sprintf "let () = print_endline (ishow %s)\n" (cexpr !globals [] (erase tm)))
      | Tt.Check tm -> ignore (infer !ctx tm)
      | Tt.Import _ -> ())
    decls;
  prelude1 ^ "\n" ^ registry !elims !ctors ^ "\n" ^ prelude2 ^ "\n" ^ Buffer.contents body
