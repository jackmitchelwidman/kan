(* ============================================================================
   C backend — compile the erased IR (lib/erase.ml) to C.
   ----------------------------------------------------------------------------
   Same erased IR as the OCaml backend, but C has no closures, so we do closure
   conversion by hand: every lambda becomes a top-level C function taking a
   captured environment (a heap-allocated linked list, so closures may escape)
   plus its argument. Values are a tagged union (closure / constructor /
   eliminator / bool / nat / pair / unit). Type-checking happens in the same
   pass, so `kan build -c` rejects ill-typed programs.
   ========================================================================== *)

open Core
open Erase

let prelude1 = {c|#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct Value Value;
typedef struct Env { Value *head; struct Env *tail; } Env;
typedef Value *(*Fn)(Env *, Value *);

enum { VCLO, VCON, VELIM, VBOOL, VNAT, VPAIR, VUNIT };
struct Value {
  int tag;
  Fn fn; Env *env;                       /* VCLO */
  const char *name; Value **args; int nargs;  /* VCON / VELIM */
  int i;                                 /* VBOOL (0/1) / VNAT */
  Value *a; Value *b;                    /* VPAIR */
};

static Value *alloc(int tag) { Value *v = malloc(sizeof(Value)); v->tag = tag; return v; }
static Value UNIT_V = { VUNIT, 0,0, 0,0,0, 0, 0,0 };
#define UNIT (&UNIT_V)

static Env *cons(Value *h, Env *t) { Env *e = malloc(sizeof(Env)); e->head = h; e->tail = t; return e; }
static Value *env_get(Env *e, int i) { while (i-- > 0) e = e->tail; return e->head; }

static Value *mk_clo(Fn f, Env *env) { Value *v = alloc(VCLO); v->fn = f; v->env = env; return v; }
static Value *mk_bool(int b) { Value *v = alloc(VBOOL); v->i = b; return v; }
static Value *mk_nat(int n) { Value *v = alloc(VNAT); v->i = n; return v; }
static Value *mk_pair(Value *a, Value *b) { Value *v = alloc(VPAIR); v->a = a; v->b = b; return v; }
static Value *mk_head(int tag, const char *name) { Value *v = alloc(tag); v->name = name; v->args = NULL; v->nargs = 0; return v; }
static Value *mk_con(const char *name) { return mk_head(VCON, name); }
static Value *mk_elim(const char *name) { return mk_head(VELIM, name); }

static int as_bool(Value *v) { return v->i; }
static Value *fst_v(Value *v) { return v->tag == VPAIR ? v->a : UNIT; }
static Value *snd_v(Value *v) { return v->tag == VPAIR ? v->b : UNIT; }
static Value *suc_v(Value *v) { return mk_nat(v->i + 1); }
|c}

let prelude2 = {c|static Value *apply(Value *f, Value *a);

static Value *ielim(const char *e, Value **sp, int n) {
  int np = elim_np(e), nc = elim_nc(e);
  int arity = np + 1 + nc + 1;
  if (n != arity) {
    Value *v = alloc(VELIM); v->name = e; v->nargs = n;
    v->args = malloc(sizeof(Value *) * (n > 0 ? n : 1));
    for (int k = 0; k < n; k++) v->args[k] = sp[k];
    return v;
  }
  Value *target = sp[arity - 1];
  if (target->tag != VCON) {
    Value *v = alloc(VELIM); v->name = e; v->nargs = n;
    v->args = malloc(sizeof(Value *) * n);
    for (int k = 0; k < n; k++) v->args[k] = sp[k];
    return v;
  }
  const char *c = target->name;
  int cnp = ctor_np(c);
  int own_n = target->nargs - cnp;
  Value *r = sp[np + 1 + ctor_pos(c)];
  for (int k = 0; k < own_n; k++) r = apply(r, target->args[cnp + k]);
  int *recs = ctor_recs(c);
  int base = np + 1 + nc;
  for (int k = 0; k < own_n; k++)
    if (recs[k]) {
      Value **sp2 = malloc(sizeof(Value *) * (base + 1));
      for (int j = 0; j < base; j++) sp2[j] = sp[j];
      sp2[base] = target->args[cnp + k];
      r = apply(r, ielim(e, sp2, base + 1));
    }
  return r;
}

static Value *apply(Value *f, Value *a) {
  switch (f->tag) {
    case VCLO: return f->fn(f->env, a);
    case VUNIT: return f;
    case VCON: {
      Value *v = alloc(VCON); v->name = f->name; v->nargs = f->nargs + 1;
      v->args = malloc(sizeof(Value *) * v->nargs);
      for (int k = 0; k < f->nargs; k++) v->args[k] = f->args[k];
      v->args[f->nargs] = a; return v;
    }
    case VELIM: {
      int n = f->nargs + 1; Value **sp = malloc(sizeof(Value *) * n);
      for (int k = 0; k < f->nargs; k++) sp[k] = f->args[k];
      sp[f->nargs] = a; return ielim(f->name, sp, n);
    }
    default: fprintf(stderr, "kan: cannot apply\n"); exit(1);
  }
}

static Value *inatelim(Value *z, Value *s, Value *n) {
  int k = n->i; Value *acc = z;
  for (int j = 0; j < k; j++) acc = apply(apply(s, mk_nat(j)), acc);
  return acc;
}

static void print_value(Value *v) {
  switch (v->tag) {
    case VNAT: printf("%d", v->i); break;
    case VBOOL: printf(v->i ? "true" : "false"); break;
    case VUNIT: printf("_"); break;
    case VPAIR: printf("("); print_value(v->a); printf(", "); print_value(v->b); printf(")"); break;
    case VCON:
      if (v->nargs == 0) printf("%s", v->name);
      else { printf("(%s", v->name); for (int k = 0; k < v->nargs; k++) { printf(" "); print_value(v->args[k]); } printf(")"); }
      break;
    case VELIM: printf("%s<partial>", v->name); break;
    default: printf("<fun>");
  }
}
|c}

let fresh = let n = ref 0 in fun () -> incr n; "fn_" ^ string_of_int !n

let quote s = "\"" ^ s ^ "\""

let compile (decls : Tt.decl list) : string =
  let ctx = ref empty in
  let ndefs = ref 0 in
  let funcs = Buffer.create 4096 in
  let main_body = Buffer.create 2048 in
  let elims = ref [] and ctors = ref [] in
  let rec cexpr nloc envv (e : iexpr) : string =
    match e with
    | IVar i -> if i < nloc then Printf.sprintf "env_get(%s, %d)" envv i else Printf.sprintf "G[%d]" (!ndefs - 1 - (i - nloc))
    | ILam b ->
        let fn = fresh () in
        let body = cexpr (nloc + 1) "e" b in
        Buffer.add_string funcs (Printf.sprintf "static Value *%s(Env *cap, Value *arg) { Env *e = cons(arg, cap); return %s; }\n" fn body);
        Printf.sprintf "mk_clo(%s, %s)" fn envv
    | IApp (f, a) -> Printf.sprintf "apply(%s, %s)" (cexpr nloc envv f) (cexpr nloc envv a)
    | IPair (a, b) -> Printf.sprintf "mk_pair(%s, %s)" (cexpr nloc envv a) (cexpr nloc envv b)
    | IFst t -> Printf.sprintf "fst_v(%s)" (cexpr nloc envv t)
    | ISnd t -> Printf.sprintf "snd_v(%s)" (cexpr nloc envv t)
    | IConH c -> Printf.sprintf "mk_con(%s)" (quote c)
    | IElimH e -> Printf.sprintf "mk_elim(%s)" (quote e)
    | IBool b -> Printf.sprintf "mk_bool(%d)" (if b then 1 else 0)
    | IIf (c, t, e) -> Printf.sprintf "(as_bool(%s) ? %s : %s)" (cexpr nloc envv c) (cexpr nloc envv t) (cexpr nloc envv e)
    | INat n -> Printf.sprintf "mk_nat(%d)" n
    | ISuc e -> Printf.sprintf "suc_v(%s)" (cexpr nloc envv e)
    | INatElim (z, s, n) -> Printf.sprintf "inatelim(%s, %s, %s)" (cexpr nloc envv z) (cexpr nloc envv s) (cexpr nloc envv n)
    | IUnit -> "UNIT"
  in
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
          Buffer.add_string main_body (Printf.sprintf "  G[%d] = %s;\n" !ndefs (cexpr 0 "0" (erase tm)));
          ctx := { env = eval !ctx.env tm :: !ctx.env; types = vty :: !ctx.types; lvl = !ctx.lvl + 1 };
          incr ndefs
      | Tt.Eval tm ->
          ignore (infer !ctx tm);
          Buffer.add_string main_body (Printf.sprintf "  print_value(%s); printf(\"\\n\");\n" (cexpr 0 "0" (erase tm)))
      | Tt.Check tm -> ignore (infer !ctx tm)
      | Tt.Import _ -> ())
    decls;
  (* registry *)
  let case_int pairs = String.concat "" (List.map (fun (k, v) -> Printf.sprintf "  if (!strcmp(x, %s)) return %d;\n" (quote k) v) pairs) in
  let reg = Buffer.create 1024 in
  Buffer.add_string reg (Printf.sprintf "static int elim_np(const char *x) {\n%s  return 0;\n}\n" (case_int (List.map (fun (e, np, _) -> (e, np)) !elims)));
  Buffer.add_string reg (Printf.sprintf "static int elim_nc(const char *x) {\n%s  return 0;\n}\n" (case_int (List.map (fun (e, _, nc) -> (e, nc)) !elims)));
  Buffer.add_string reg (Printf.sprintf "static int ctor_np(const char *x) {\n%s  return 0;\n}\n" (case_int (List.map (fun (c, np, _, _) -> (c, np)) !ctors)));
  Buffer.add_string reg (Printf.sprintf "static int ctor_pos(const char *x) {\n%s  return 0;\n}\n" (case_int (List.map (fun (c, _, p, _) -> (c, p)) !ctors)));
  List.iter (fun (c, _, _, recs) -> Buffer.add_string reg (Printf.sprintf "static int _recs_%s[] = {%s};\n" c (if recs = [] then "0" else String.concat ", " (List.map (fun b -> if b then "1" else "0") recs)))) !ctors;
  Buffer.add_string reg (Printf.sprintf "static int *ctor_recs(const char *x) {\n%s  return 0;\n}\n" (String.concat "" (List.map (fun (c, _, _, _) -> Printf.sprintf "  if (!strcmp(x, %s)) return _recs_%s;\n" (quote c) c) !ctors)));
  let n = max !ndefs 1 in
  prelude1 ^ "\n" ^ Buffer.contents reg ^ "\n" ^ prelude2 ^ "\n"
  ^ Printf.sprintf "static Value *G[%d];\n\n" n
  ^ Buffer.contents funcs
  ^ "\nint main(void) {\n" ^ Buffer.contents main_body ^ "  return 0;\n}\n"
