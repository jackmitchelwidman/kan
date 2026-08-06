(* ============================================================================
   Kan interpreter — evaluate a parsed program directly on the fill kernel.
   Every surface form is exactly one kernel `fill`.
   ========================================================================== *)

open Kernel
open Syntax

type value =
  | VObj of obj
  | VMor of mor
  | VDiagram of diagram
  | VLimit of obj * mor array
  | VColim of obj * mor array

let run (stmts : stmt list) : unit =
  let env : (string, value) Hashtbl.t = Hashtbl.create 32 in
  let lookup name =
    match Hashtbl.find_opt env name with
    | Some v -> v
    | None -> failwith ("unbound name '" ^ name ^ "'")
  in
  let as_obj name = match lookup name with VObj o -> o | _ -> failwith (name ^ " is not a set") in
  let as_mor name = match lookup name with VMor m -> m | _ -> failwith (name ^ " is not a map") in
  let as_diagram name = match lookup name with VDiagram d -> d | _ -> failwith (name ^ " is not a diagram") in
  let eval e =
    match e with
    | EVar name -> lookup name
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
  let show v =
    match v with
    | VObj o -> Printf.printf "%s : Set(%d)\n" o.name o.card
    | VMor m -> Printf.printf "%s\n" (string_of_mor m)
    | VDiagram d ->
        Printf.printf "diagram: %d vertices, %d edges\n" (Array.length d.verts) (List.length d.arrs)
    | VLimit (o, proj) ->
        Printf.printf "limit: %d elements\n" o.card;
        Array.iteri (fun i p -> Printf.printf "  proj[%d] = %s\n" i (string_of_mor p)) proj
    | VColim (o, incl) ->
        Printf.printf "colimit: %d elements\n" o.card;
        Array.iteri (fun i p -> Printf.printf "  incl[%d] = %s\n" i (string_of_mor p)) incl
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
                failwith (Printf.sprintf "map %s: image %d is outside codomain %s (size %d)"
                            name y cod c.card))
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
      | SLet (name, e) -> Hashtbl.replace env name (eval e)
      | SShow e -> show (eval e))
    stmts
