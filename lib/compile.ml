(* ============================================================================
   Kan → C compiler (Phase 1 backend).
   ----------------------------------------------------------------------------
   Lowers a parsed program to a self-contained C translation unit that, at
   RUNTIME, performs the categorical computation itself (composition; finite
   limits by tuple enumeration; colimits by union–find) and prints the same
   results the interpreter would. bin/kan.ml then invokes `cc` to produce a
   native binary.  This is a real compiler, not constant-folding: the emitted
   binary contains the fill algorithms and runs them.
   ========================================================================== *)

open Syntax

type ctype = TObj | TMor | TLimit | TColim | TDiagram

let ctype_c = function
  | TObj -> "Obj"
  | TMor -> "Mor"
  | TLimit | TColim -> "Cone"
  | TDiagram -> failwith "a diagram has no single C value"

(* The categorical runtime, embedded verbatim. *)
let runtime = {c|#include <stdio.h>
#include <stdlib.h>

typedef struct { int card; const char *name; } Obj;
typedef struct { int dom_card; int cod_card; const char *dom; const char *cod; int *tbl; } Mor;
typedef struct { Obj obj; Mor *legs; int nlegs; } Cone;

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

let compile (stmts : stmt list) : string =
  let body = Buffer.create 4096 in
  let emit fmt = Printf.ksprintf (Buffer.add_string body) fmt in
  let tenv : (string, ctype) Hashtbl.t = Hashtbl.create 32 in
  let dims : (string, int * int) Hashtbl.t = Hashtbl.create 8 in
  let tmp = ref 0 in
  let fresh () = incr tmp; Printf.sprintf "t%d" !tmp in
  let cv name = "k_" ^ name in
  let bind name t =
    if Hashtbl.mem tenv name then
      failwith (Printf.sprintf "redefinition of '%s' is not supported by the compiler yet" name);
    Hashtbl.replace tenv name t
  in
  let type_of e =
    match e with
    | EVar n -> (match Hashtbl.find_opt tenv n with Some t -> t | None -> failwith ("unbound name '" ^ n ^ "'"))
    | EFillInner _ -> TMor
    | EFillLimit _ | EProduct _ -> TLimit
    | EFillColimit _ | ECoproduct _ -> TColim
  in
  let names_arr ns = String.concat ", " (List.map (fun s -> "\"" ^ s ^ "\"") ns) in
  let cards_arr ns = String.concat ", " (List.map (fun s -> cv s ^ ".card") ns) in
  (* Emit code computing expr `e` into a freshly declared C variable `target`. *)
  let emit_into target e : ctype =
    match e with
    | EVar n ->
        let t = type_of e in
        emit "  %s %s = %s;\n" (ctype_c t) target (cv n); t
    | EFillInner (f, g) ->
        emit "  Mor %s = kan_compose(%s, %s);\n" target (cv f) (cv g); TMor
    | EFillLimit d ->
        let nv, ne = try Hashtbl.find dims d with Not_found -> failwith (d ^ " is not a diagram") in
        let a s = if ne = 0 then "NULL" else Printf.sprintf "d_%s_%s" d s in
        emit "  Cone %s = kan_limit(d_%s_verts, d_%s_vnames, %d, %s, %s, %s, %d);\n"
          target d d nv (a "ei") (a "ej") (a "etbl") ne;
        TLimit
    | EFillColimit d ->
        let nv, ne = try Hashtbl.find dims d with Not_found -> failwith (d ^ " is not a diagram") in
        let a s = if ne = 0 then "NULL" else Printf.sprintf "d_%s_%s" d s in
        emit "  Cone %s = kan_colimit(d_%s_verts, d_%s_vnames, %d, %s, %s, %s, %d);\n"
          target d d nv (a "ei") (a "ej") (a "etbl") ne;
        TColim
    | EProduct ns ->
        let v = fresh () in
        emit "  int %s_v[] = {%s};\n" v (cards_arr ns);
        emit "  const char *%s_n[] = {%s};\n" v (names_arr ns);
        emit "  Cone %s = kan_limit(%s_v, %s_n, %d, NULL, NULL, NULL, 0);\n"
          target v v (List.length ns);
        TLimit
    | ECoproduct ns ->
        let v = fresh () in
        emit "  int %s_v[] = {%s};\n" v (cards_arr ns);
        emit "  const char *%s_n[] = {%s};\n" v (names_arr ns);
        emit "  Cone %s = kan_colimit(%s_v, %s_n, %d, NULL, NULL, NULL, 0);\n"
          target v v (List.length ns);
        TColim
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
      | SLet (name, e) ->
          let t = type_of e in
          bind name t;
          ignore (emit_into (cv name) e)
      | SShow e ->
          let t = type_of e in
          let v = match e with EVar n -> cv n | _ -> let v = fresh () in ignore (emit_into v e); v in
          (match t with
           | TObj -> emit "  kan_show_obj(%s);\n" v
           | TMor -> emit "  kan_show_mor(%s);\n" v
           | TLimit -> emit "  kan_show_limit(%s);\n" v
           | TColim -> emit "  kan_show_colimit(%s);\n" v
           | TDiagram ->
               (match e with
                | EVar n ->
                    let nv, ne = Hashtbl.find dims n in
                    emit "  printf(\"diagram: %%d vertices, %%d edges\\n\", %d, %d);\n" nv ne
                | _ -> failwith "cannot show an anonymous diagram")))
    stmts;
  runtime ^ "\nint main(void) {\n" ^ Buffer.contents body ^ "  return 0;\n}\n"
