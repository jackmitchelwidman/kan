(* ============================================================================
   Kan interpreter — evaluate a parsed program directly on the fill kernel.
   Structural constructions are one kernel `fill`; folds are `Kernel.cata`
   (the unique homomorphism out of an initial algebra = a universal fill).
   ========================================================================== *)

open Kernel
open Syntax

type value =
  | VObj of obj
  | VMor of mor
  | VDiagram of diagram
  | VLimit of obj * mor array
  | VColim of obj * mor array
  | VInt of int
  | VTree of string * tree      (* datatype name, value *)

(* ctor name -> (index, has_payload, arity, datatype) *)
type ctor_info = { idx : int; payload : bool; arity : int; data : string }

let run (stmts : stmt list) : unit =
  let env : (string, value) Hashtbl.t = Hashtbl.create 64 in
  let ctors : (string, ctor_info) Hashtbl.t = Hashtbl.create 32 in
  let ctor_names : (string, string array) Hashtbl.t = Hashtbl.create 16 in
  let datanc : (string, int) Hashtbl.t = Hashtbl.create 16 in
  let folds : (string, string * int algebra) Hashtbl.t = Hashtbl.create 16 in
  let lookup name =
    match Hashtbl.find_opt env name with Some v -> v | None -> failwith ("unbound name '" ^ name ^ "'")
  in
  let as_obj name = match lookup name with VObj o -> o | _ -> failwith (name ^ " is not a set") in
  let as_mor name = match lookup name with VMor m -> m | _ -> failwith (name ^ " is not a map") in
  let as_diagram name = match lookup name with VDiagram d -> d | _ -> failwith (name ^ " is not a diagram") in
  let rec eval_aexpr benv a =
    match a with
    | AInt n -> n
    | AVar v -> (match Hashtbl.find_opt benv v with Some x -> x | None -> failwith ("unbound variable '" ^ v ^ "' in fold body"))
    | AAdd (x, y) -> eval_aexpr benv x + eval_aexpr benv y
    | ASub (x, y) -> eval_aexpr benv x - eval_aexpr benv y
    | AMul (x, y) -> eval_aexpr benv x * eval_aexpr benv y
  in
  let rec eval e =
    match e with
    | EInt n -> VInt n
    | EVar name ->
        (match Hashtbl.find_opt env name with
         | Some v -> v
         | None ->
             (match Hashtbl.find_opt ctors name with
              | Some c when (not c.payload) && c.arity = 0 -> VTree (c.data, Node (c.idx, 0, [||]))
              | Some _ -> failwith ("constructor '" ^ name ^ "' needs arguments")
              | None -> failwith ("unbound name '" ^ name ^ "'")))
    | EApp (head, args) ->
        (match Hashtbl.find_opt ctors head with
         | Some c ->
             let need = (if c.payload then 1 else 0) + c.arity in
             if List.length args <> need then
               failwith (Printf.sprintf "%s expects %d argument(s), got %d" head need (List.length args));
             let p, childargs =
               if c.payload then
                 match args with
                 | a :: rest -> ((match eval a with VInt n -> n | _ -> failwith (head ^ ": payload must be an int")), rest)
                 | [] -> assert false
               else (0, args)
             in
             let kids =
               Array.of_list
                 (List.map
                    (fun a ->
                      match eval a with
                      | VTree (d, t) ->
                          if d <> c.data then failwith (head ^ ": a child has type " ^ d ^ ", expected " ^ c.data);
                          t
                      | _ -> failwith (head ^ ": argument must be a value of " ^ c.data))
                    childargs)
             in
             VTree (c.data, Node (c.idx, p, kids))
         | None ->
             (match Hashtbl.find_opt folds head with
              | Some (ty, alg) ->
                  (match args with
                   | [ a ] ->
                       (match eval a with
                        | VTree (d, t) ->
                            if d <> ty then failwith (head ^ ": expects a " ^ ty ^ ", got a " ^ d);
                            VInt (cata alg t)
                        | _ -> failwith (head ^ ": argument must be a value"))
                   | _ -> failwith (head ^ ": a fold takes exactly one argument"))
              | None -> failwith ("unknown constructor or fold '" ^ head ^ "'")))
    | EFillInner (f, g) ->
        let ff = as_mor f and gg = as_mor g in
        if ff.cod.card <> gg.dom.card then
          failwith (Printf.sprintf "cannot fill inner horn: %s : ->%s and %s : %s-> are not composable"
                      f ff.cod.name g gg.dom.name);
        (match fill (Inner (ff, gg)) Exists with Edge m -> VMor m | _ -> assert false)
    | EFillLimit dn ->
        (match fill (LimCone (as_diagram dn)) Universal with
         | Limit { lobj; proj; _ } -> VLimit (lobj, proj) | _ -> assert false)
    | EFillColimit dn ->
        (match fill (ColCocone (as_diagram dn)) Universal with
         | Colim { cobj; incl; _ } -> VColim (cobj, incl) | _ -> assert false)
    | EProduct ns ->
        let objs = Array.of_list (List.map as_obj ns) in
        (match fill (LimCone (discrete objs)) Universal with
         | Limit { lobj; proj; _ } -> VLimit (lobj, proj) | _ -> assert false)
    | ECoproduct ns ->
        let objs = Array.of_list (List.map as_obj ns) in
        (match fill (ColCocone (discrete objs)) Universal with
         | Colim { cobj; incl; _ } -> VColim (cobj, incl) | _ -> assert false)
  in
  let rec pretty dn t =
    match t with
    | Node (c, p, kids) ->
        let name = (Hashtbl.find ctor_names dn).(c) in
        let info = Hashtbl.find ctors name in
        if (not info.payload) && Array.length kids = 0 then name
        else
          let args =
            (if info.payload then [ string_of_int p ] else [])
            @ Array.to_list (Array.map (pretty dn) kids)
          in
          name ^ "(" ^ String.concat ", " args ^ ")"
  in
  let show v =
    match v with
    | VObj o -> Printf.printf "%s : Set(%d)\n" o.name o.card
    | VMor m -> Printf.printf "%s\n" (string_of_mor m)
    | VInt n -> Printf.printf "%d\n" n
    | VTree (dn, t) -> Printf.printf "%s\n" (pretty dn t)
    | VDiagram d ->
        Printf.printf "diagram: %d vertices, %d edges\n" (Array.length d.verts) (List.length d.arrs)
    | VLimit (o, proj) ->
        Printf.printf "limit: %d elements\n" o.card;
        Array.iteri (fun i pr -> Printf.printf "  proj[%d] = %s\n" i (string_of_mor pr)) proj
    | VColim (o, incl) ->
        Printf.printf "colimit: %d elements\n" o.card;
        Array.iteri (fun i pr -> Printf.printf "  incl[%d] = %s\n" i (string_of_mor pr)) incl
  in
  let build_algebra name ty clauses : int algebra =
    let nct = match Hashtbl.find_opt datanc ty with Some n -> n | None -> failwith ("fold " ^ name ^ ": unknown type " ^ ty) in
    let byidx = Array.make nct None in
    List.iter
      (fun cl ->
        match Hashtbl.find_opt ctors cl.fc_ctor with
        | None -> failwith ("fold " ^ name ^ ": unknown constructor '" ^ cl.fc_ctor ^ "'")
        | Some c ->
            if c.data <> ty then failwith ("fold " ^ name ^ ": '" ^ cl.fc_ctor ^ "' is not from " ^ ty);
            let need = (if c.payload then 1 else 0) + c.arity in
            if List.length cl.fc_vars <> need then
              failwith (Printf.sprintf "fold %s: %s binds %d vars but needs %d" name cl.fc_ctor
                          (List.length cl.fc_vars) need);
            let pv, cvs = if c.payload then (Some (List.hd cl.fc_vars), List.tl cl.fc_vars) else (None, cl.fc_vars) in
            byidx.(c.idx) <- Some (pv, cvs, cl.fc_body))
      clauses;
    Array.iteri (fun i o -> if o = None then failwith (Printf.sprintf "fold %s: missing a clause for constructor #%d of %s" name i ty)) byidx;
    fun c p kids ->
      match byidx.(c) with
      | None -> failwith "fold: no clause"
      | Some (pv, cvs, body) ->
          let benv = Hashtbl.create 8 in
          (match pv with Some v -> Hashtbl.replace benv v p | None -> ());
          List.iteri (fun i v -> Hashtbl.replace benv v kids.(i)) cvs;
          eval_aexpr benv body
  in
  List.iter
    (fun s ->
      match s with
      | SSet (name, n) ->
          if n < 0 then failwith (Printf.sprintf "set %s: size must be >= 0" name);
          Hashtbl.replace env name (VObj (obj name n))
      | SMap (name, dom, cod, tbl) ->
          let d = as_obj dom and c = as_obj cod in
          if List.length tbl <> d.card then
            failwith (Printf.sprintf "map %s: table has %d entries but domain %s has %d elements"
                        name (List.length tbl) dom d.card);
          List.iter
            (fun y ->
              if y < 0 || y >= c.card then
                failwith (Printf.sprintf "map %s: image %d is outside codomain %s (size %d)" name y cod c.card))
            tbl;
          Hashtbl.replace env name (VMor (mor d c (Array.of_list tbl)))
      | SDiagram (name, vs, es) ->
          let verts = Array.of_list (List.map as_obj vs) in
          let nv = Array.length verts in
          let arrs =
            List.map
              (fun (i, j, mn) ->
                if i < 0 || i >= nv || j < 0 || j >= nv then
                  failwith (Printf.sprintf "diagram %s: edge endpoint out of range (have %d vertices)" name nv);
                let m = as_mor mn in
                if m.dom.card <> verts.(i).card || m.cod.card <> verts.(j).card then
                  failwith (Printf.sprintf "diagram %s: map %s does not match vertices %d -> %d" name mn i j);
                (i, j, m))
              es
          in
          Hashtbl.replace env name (VDiagram { verts; arrs })
      | SData (name, cs) ->
          Hashtbl.replace datanc name (List.length cs);
          let names = Array.make (List.length cs) "" in
          List.iteri
            (fun idx cd ->
              if Hashtbl.mem ctors cd.cd_name then failwith ("constructor '" ^ cd.cd_name ^ "' already defined");
              Hashtbl.replace ctors cd.cd_name { idx; payload = cd.cd_payload; arity = cd.cd_arity; data = name };
              names.(idx) <- cd.cd_name)
            cs;
          Hashtbl.replace ctor_names name names
      | SFold (name, ty, clauses) -> Hashtbl.replace folds name (ty, build_algebra name ty clauses)
      | SLet (name, e) -> Hashtbl.replace env name (eval e)
      | SShow e -> show (eval e))
    stmts
