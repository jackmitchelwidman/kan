(* ============================================================================
   Kan → C compiler (Phase 1 backend).
   ----------------------------------------------------------------------------
   Lowers a program to a self-contained C translation unit that performs the
   categorical computation at RUNTIME: composition; finite limits by tuple
   enumeration; colimits by union-find; and folds as recursive C functions
   over an initial-algebra tree type. bin/kan.ml then invokes `cc`.
   ========================================================================== *)

open Syntax

type ctype = TObj | TMor | TLimit | TColim | TInt | TTree | TDiagram

let ctype_c = function
  | TObj -> "Obj"
  | TMor -> "Mor"
  | TLimit | TColim -> "Cone"
  | TInt -> "int"
  | TTree -> "KTree*"
  | TDiagram -> failwith "a diagram has no single C value"

type ctor_info = { idx : int; payload : bool; arity : int; data : string }

let runtime = {c|#include <stdio.h>
#include <stdlib.h>

typedef struct { int card; const char *name; } Obj;
typedef struct { int dom_card; int cod_card; const char *dom; const char *cod; int *tbl; } Mor;
typedef struct { Obj obj; Mor *legs; int nlegs; } Cone;

/* values of an initial algebra: finite trees */
typedef struct KTree { int ctor; const char *cname; int payload; int has_payload;
                       struct KTree **kids; int nkids; } KTree;

static KTree *kan_node(int ctor, const char *cname, int payload, int has_payload,
                       KTree **kids, int nkids) {
  KTree *t = (KTree *)malloc(sizeof(KTree));
  t->ctor = ctor; t->cname = cname; t->payload = payload; t->has_payload = has_payload;
  t->nkids = nkids;
  if (nkids > 0) { t->kids = (KTree **)malloc(sizeof(KTree *) * nkids);
                   for (int i = 0; i < nkids; i++) t->kids[i] = kids[i]; }
  else t->kids = NULL;
  return t;
}

static void kan_show_tree(KTree *t) {
  printf("%s", t->cname);
  if (t->has_payload || t->nkids > 0) {
    printf("(");
    int first = 1;
    if (t->has_payload) { printf("%d", t->payload); first = 0; }
    for (int i = 0; i < t->nkids; i++) { if (!first) printf(", "); first = 0; kan_show_tree(t->kids[i]); }
    printf(")");
  }
}

/* composition g∘f as an inner-horn fill */
static Mor kan_compose(Mor f, Mor g) {
  int n = f.dom_card;
  int *t = (int *)malloc(sizeof(int) * (n > 0 ? n : 1));
  for (int x = 0; x < n; x++) t[x] = g.tbl[f.tbl[x]];
  Mor r; r.dom_card = f.dom_card; r.cod_card = g.cod_card; r.dom = f.dom; r.cod = g.cod; r.tbl = t;
  return r;
}

/* limit of a finite diagram = compatible tuples of the product (universal fill) */
static Cone kan_limit(int *vcards, const char **vnames, int nv,
                      int *ei, int *ej, int **etbl, int ne) {
  Cone c;
  if (nv == 0) { Obj o; o.card = 1; o.name = "lim"; c.obj = o; c.legs = NULL; c.nlegs = 0; return c; }
  int *cur = (int *)calloc(nv, sizeof(int));
  int empty = 0;
  for (int j = 0; j < nv; j++) if (vcards[j] == 0) empty = 1;
  int cap = 16, cnt = 0;
  int *tuples = (int *)malloc(sizeof(int) * cap * nv);
  if (!empty) {
    for (;;) {
      int ok = 1;
      for (int e = 0; e < ne; e++) { if (etbl[e][cur[ei[e]]] != cur[ej[e]]) { ok = 0; break; } }
      if (ok) {
        if (cnt == cap) { cap *= 2; tuples = (int *)realloc(tuples, sizeof(int) * cap * nv); }
        for (int j = 0; j < nv; j++) tuples[cnt * nv + j] = cur[j];
        cnt++;
      }
      int k = nv - 1;
      while (k >= 0) { cur[k]++; if (cur[k] < vcards[k]) break; cur[k] = 0; k--; }
      if (k < 0) break;
    }
  }
  Obj o; o.card = cnt; o.name = "lim";
  Mor *legs = (Mor *)malloc(sizeof(Mor) * nv);
  for (int j = 0; j < nv; j++) {
    int *t = (int *)malloc(sizeof(int) * (cnt > 0 ? cnt : 1));
    for (int i = 0; i < cnt; i++) t[i] = tuples[i * nv + j];
    legs[j].dom_card = cnt; legs[j].cod_card = vcards[j];
    legs[j].dom = "lim"; legs[j].cod = vnames[j]; legs[j].tbl = t;
  }
  free(cur); free(tuples);
  c.obj = o; c.legs = legs; c.nlegs = nv; return c;
}

static int kan_find(int *p, int i) { while (p[i] != i) { p[i] = p[p[i]]; i = p[i]; } return i; }

/* colimit of a finite diagram = disjoint union quotiented by the arrows */
static Cone kan_colimit(int *vcards, const char **vnames, int nv,
                        int *ei, int *ej, int **etbl, int ne) {
  Cone c;
  int *offset = (int *)malloc(sizeof(int) * (nv > 0 ? nv : 1));
  int total = 0;
  for (int j = 0; j < nv; j++) { offset[j] = total; total += vcards[j]; }
  int *parent = (int *)malloc(sizeof(int) * (total > 0 ? total : 1));
  for (int i = 0; i < total; i++) parent[i] = i;
  for (int e = 0; e < ne; e++) {
    int a = ei[e], b = ej[e];
    for (int x = 0; x < vcards[a]; x++) {
      int ra = kan_find(parent, offset[a] + x);
      int rb = kan_find(parent, offset[b] + etbl[e][x]);
      if (ra != rb) parent[ra] = rb;
    }
  }
  int *classof = (int *)malloc(sizeof(int) * (total > 0 ? total : 1));
  for (int i = 0; i < total; i++) classof[i] = -1;
  int ncls = 0;
  for (int i = 0; i < total; i++) { int r = kan_find(parent, i); if (classof[r] == -1) classof[r] = ncls++; }
  Obj o; o.card = ncls; o.name = "colim";
  Mor *legs = (Mor *)malloc(sizeof(Mor) * (nv > 0 ? nv : 1));
  for (int j = 0; j < nv; j++) {
    int *t = (int *)malloc(sizeof(int) * (vcards[j] > 0 ? vcards[j] : 1));
    for (int x = 0; x < vcards[j]; x++) t[x] = classof[kan_find(parent, offset[j] + x)];
    legs[j].dom_card = vcards[j]; legs[j].cod_card = ncls;
    legs[j].dom = vnames[j]; legs[j].cod = "colim"; legs[j].tbl = t;
  }
  free(offset); free(parent); free(classof);
  c.obj = o; c.legs = legs; c.nlegs = nv; return c;
}

static void kan_show_mor(Mor m) {
  printf("%s -> %s : [", m.dom, m.cod);
  for (int i = 0; i < m.dom_card; i++) { printf("%d", m.tbl[i]); if (i + 1 < m.dom_card) printf("; "); }
  printf("]\n");
}
static void kan_show_obj(Obj o) { printf("%s : Set(%d)\n", o.name, o.card); }
static void kan_show_limit(Cone c) {
  printf("limit: %d elements\n", c.obj.card);
  for (int j = 0; j < c.nlegs; j++) { printf("  proj[%d] = ", j); kan_show_mor(c.legs[j]); }
}
static void kan_show_colimit(Cone c) {
  printf("colimit: %d elements\n", c.obj.card);
  for (int j = 0; j < c.nlegs; j++) { printf("  incl[%d] = ", j); kan_show_mor(c.legs[j]); }
}
|c}

let rec compile_aexpr a =
  match a with
  | AInt n -> string_of_int n
  | AVar v -> "u_" ^ v
  | AAdd (x, y) -> "(" ^ compile_aexpr x ^ " + " ^ compile_aexpr y ^ ")"
  | ASub (x, y) -> "(" ^ compile_aexpr x ^ " - " ^ compile_aexpr y ^ ")"
  | AMul (x, y) -> "(" ^ compile_aexpr x ^ " * " ^ compile_aexpr y ^ ")"

let compile (stmts : stmt list) : string =
  let decls = Buffer.create 2048 in
  let body = Buffer.create 4096 in
  let emit fmt = Printf.ksprintf (Buffer.add_string body) fmt in
  let emitd fmt = Printf.ksprintf (Buffer.add_string decls) fmt in
  let tenv : (string, ctype) Hashtbl.t = Hashtbl.create 32 in
  let dims : (string, int * int) Hashtbl.t = Hashtbl.create 8 in
  let ctors : (string, ctor_info) Hashtbl.t = Hashtbl.create 32 in
  let datanc : (string, int) Hashtbl.t = Hashtbl.create 16 in
  let folds : (string, string) Hashtbl.t = Hashtbl.create 16 in
  let tmp = ref 0 in
  let fresh () = incr tmp; Printf.sprintf "t%d" !tmp in
  let cv name = "k_" ^ name in
  let bind name t =
    if Hashtbl.mem tenv name then
      failwith (Printf.sprintf "redefinition of '%s' is not supported by the compiler yet" name);
    Hashtbl.replace tenv name t
  in
  let names_arr ns = String.concat ", " (List.map (fun s -> "\"" ^ s ^ "\"") ns) in
  let cards_arr ns = String.concat ", " (List.map (fun s -> cv s ^ ".card") ns) in
  let type_of e =
    match e with
    | EInt _ -> TInt
    | EVar n ->
        (match Hashtbl.find_opt tenv n with
         | Some t -> t
         | None ->
             (match Hashtbl.find_opt ctors n with
              | Some c when (not c.payload) && c.arity = 0 -> TTree
              | Some _ -> failwith ("constructor '" ^ n ^ "' needs arguments")
              | None -> failwith ("unbound name '" ^ n ^ "'")))
    | EApp (head, _) ->
        if Hashtbl.mem ctors head then TTree
        else if Hashtbl.mem folds head then TInt
        else failwith ("unknown constructor or fold '" ^ head ^ "'")
    | EFillInner _ -> TMor
    | EFillLimit _ | EProduct _ -> TLimit
    | EFillColimit _ | ECoproduct _ -> TColim
  in
  (* value expressions (constructor applications) -> a C expression of type KTree* *)
  let rec compile_value e =
    match e with
    | EVar n ->
        (match Hashtbl.find_opt tenv n with
         | Some TTree -> cv n
         | Some _ -> failwith (n ^ " is not a value")
         | None ->
             (match Hashtbl.find_opt ctors n with
              | Some c when (not c.payload) && c.arity = 0 ->
                  Printf.sprintf "kan_node(%d, \"%s\", 0, 0, NULL, 0)" c.idx n
              | Some _ -> failwith ("constructor '" ^ n ^ "' needs arguments")
              | None -> failwith ("unbound value '" ^ n ^ "'")))
    | EApp (head, args) ->
        (match Hashtbl.find_opt ctors head with
         | Some c ->
             let need = (if c.payload then 1 else 0) + c.arity in
             if List.length args <> need then
               failwith (Printf.sprintf "%s expects %d argument(s), got %d" head need (List.length args));
             let p, kidargs =
               if c.payload then
                 match args with a :: r -> (compile_int a, r) | [] -> assert false
               else ("0", args)
             in
             let kidscode = String.concat ", " (List.map compile_value kidargs) in
             let kidsarr = if c.arity = 0 then "NULL" else Printf.sprintf "(KTree*[]){%s}" kidscode in
             Printf.sprintf "kan_node(%d, \"%s\", %s, %d, %s, %d)"
               c.idx head p (if c.payload then 1 else 0) kidsarr c.arity
         | None -> failwith ("'" ^ head ^ "' is not a constructor (cannot appear as a value)"))
    | EInt _ -> failwith "an int is not a tree value"
    | _ -> failwith "not a value expression"
  and compile_int e =
    match e with EInt n -> string_of_int n | _ -> failwith "a constructor payload must be an integer literal"
  in
  let emit_into target e : ctype =
    match e with
    | EInt n -> emit "  int %s = %d;\n" target n; TInt
    | EVar n ->
        (match Hashtbl.find_opt tenv n with
         | Some t -> emit "  %s %s = %s;\n" (ctype_c t) target (cv n); t
         | None -> emit "  KTree *%s = %s;\n" target (compile_value e); TTree)
    | EApp (head, args) ->
        if Hashtbl.mem ctors head then (emit "  KTree *%s = %s;\n" target (compile_value e); TTree)
        else if Hashtbl.mem folds head then
          (match args with
           | [ a ] -> emit "  int %s = f_%s(%s);\n" target head (compile_value a); TInt
           | _ -> failwith (head ^ ": a fold takes exactly one argument"))
        else failwith ("unknown constructor or fold '" ^ head ^ "'")
    | EFillInner (f, g) -> emit "  Mor %s = kan_compose(%s, %s);\n" target (cv f) (cv g); TMor
    | EFillLimit d ->
        let nv, ne = (try Hashtbl.find dims d with Not_found -> failwith (d ^ " is not a diagram")) in
        let a s = if ne = 0 then "NULL" else Printf.sprintf "d_%s_%s" d s in
        emit "  Cone %s = kan_limit(d_%s_verts, d_%s_vnames, %d, %s, %s, %s, %d);\n"
          target d d nv (a "ei") (a "ej") (a "etbl") ne; TLimit
    | EFillColimit d ->
        let nv, ne = (try Hashtbl.find dims d with Not_found -> failwith (d ^ " is not a diagram")) in
        let a s = if ne = 0 then "NULL" else Printf.sprintf "d_%s_%s" d s in
        emit "  Cone %s = kan_colimit(d_%s_verts, d_%s_vnames, %d, %s, %s, %s, %d);\n"
          target d d nv (a "ei") (a "ej") (a "etbl") ne; TColim
    | EProduct ns ->
        let v = fresh () in
        emit "  int %s_v[] = {%s};\n" v (cards_arr ns);
        emit "  const char *%s_n[] = {%s};\n" v (names_arr ns);
        emit "  Cone %s = kan_limit(%s_v, %s_n, %d, NULL, NULL, NULL, 0);\n" target v v (List.length ns); TLimit
    | ECoproduct ns ->
        let v = fresh () in
        emit "  int %s_v[] = {%s};\n" v (cards_arr ns);
        emit "  const char *%s_n[] = {%s};\n" v (names_arr ns);
        emit "  Cone %s = kan_colimit(%s_v, %s_n, %d, NULL, NULL, NULL, 0);\n" target v v (List.length ns); TColim
  in
  let emit_fold name ty clauses =
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
            byidx.(c.idx) <- Some (c.payload, cl.fc_vars, cl.fc_body))
      clauses;
    Array.iteri (fun i o -> if o = None then failwith (Printf.sprintf "fold %s: missing a clause for constructor #%d of %s" name i ty)) byidx;
    emitd "static int f_%s(KTree *t) {\n" name;
    emitd "  switch (t->ctor) {\n";
    Array.iteri
      (fun idx o ->
        match o with
        | None -> ()
        | Some (payload, vars, bodya) ->
            emitd "  case %d: {\n" idx;
            let pv, cvs = if payload then (Some (List.hd vars), List.tl vars) else (None, vars) in
            (match pv with Some v -> emitd "    int u_%s = t->payload;\n" v | None -> ());
            List.iteri (fun i v -> emitd "    int u_%s = f_%s(t->kids[%d]);\n" v name i) cvs;
            emitd "    return %s;\n" (compile_aexpr bodya);
            emitd "  }\n")
      byidx;
    emitd "  default: return 0;\n";
    emitd "  }\n}\n\n";
    Hashtbl.replace folds name ty
  in
  List.iter
    (fun s ->
      match s with
      | SSet (name, n) ->
          if n < 0 then failwith (Printf.sprintf "set %s: size must be >= 0" name);
          bind name TObj;
          emit "  Obj %s = {%d, \"%s\"};\n" (cv name) n name
      | SMap (name, dom, cod, tbl) ->
          bind name TMor;
          let tblstr = if tbl = [] then "0" else String.concat ", " (List.map string_of_int tbl) in
          emit "  int %s_tbl[] = {%s};\n" (cv name) tblstr;
          emit "  Mor %s = {%s.card, %s.card, \"%s\", \"%s\", %s_tbl};\n"
            (cv name) (cv dom) (cv cod) dom cod (cv name)
      | SDiagram (name, vs, es) ->
          let nv = List.length vs and ne = List.length es in
          emit "  int d_%s_verts[] = {%s};\n" name (cards_arr vs);
          emit "  const char *d_%s_vnames[] = {%s};\n" name (names_arr vs);
          if ne > 0 then begin
            emit "  int d_%s_ei[] = {%s};\n" name
              (String.concat ", " (List.map (fun (i, _, _) -> string_of_int i) es));
            emit "  int d_%s_ej[] = {%s};\n" name
              (String.concat ", " (List.map (fun (_, j, _) -> string_of_int j) es));
            emit "  int *d_%s_etbl[] = {%s};\n" name
              (String.concat ", " (List.map (fun (_, _, m) -> cv m ^ "_tbl") es))
          end;
          bind name TDiagram;
          Hashtbl.replace dims name (nv, ne)
      | SData (name, cs) ->
          Hashtbl.replace datanc name (List.length cs);
          List.iteri
            (fun idx cd ->
              if Hashtbl.mem ctors cd.cd_name then failwith ("constructor '" ^ cd.cd_name ^ "' already defined");
              Hashtbl.replace ctors cd.cd_name { idx; payload = cd.cd_payload; arity = cd.cd_arity; data = name })
            cs
      | SFold (name, ty, clauses) -> emit_fold name ty clauses
      | SLet (name, e) ->
          let t = type_of e in
          bind name t;
          ignore (emit_into (cv name) e)
      | SShow e ->
          (match type_of e with
           | TDiagram ->
               (match e with
                | EVar n ->
                    let nv, ne = Hashtbl.find dims n in
                    emit "  printf(\"diagram: %%d vertices, %%d edges\\n\", %d, %d);\n" nv ne
                | _ -> failwith "cannot show an anonymous diagram")
           | t ->
               let v = match e with EVar n when Hashtbl.mem tenv n -> cv n | _ -> let v = fresh () in ignore (emit_into v e); v in
               (match t with
                | TObj -> emit "  kan_show_obj(%s);\n" v
                | TMor -> emit "  kan_show_mor(%s);\n" v
                | TLimit -> emit "  kan_show_limit(%s);\n" v
                | TColim -> emit "  kan_show_colimit(%s);\n" v
                | TInt -> emit "  printf(\"%%d\\n\", %s);\n" v
                | TTree -> emit "  kan_show_tree(%s); printf(\"\\n\");\n" v
                | TDiagram -> assert false)))
    stmts;
  runtime ^ "\n" ^ Buffer.contents decls ^ "int main(void) {\n" ^ Buffer.contents body ^ "  return 0;\n}\n"
