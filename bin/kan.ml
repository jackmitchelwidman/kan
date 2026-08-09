(* ============================================================================
   kan — the Kan command-line driver.

   Kan is a dependently typed language; its files are .kan.
     kan check <file.kan>            type-check and report the types
     kan run   <file.kan>            type-check, then run the program
     kan explain <file.kan>          show each definition as its Kan-extension fiber
     kan build <file.kan> [-o out]   type-check, then compile to a native binary
     kan emit-ml <file.kan>          print the generated OCaml
     kan       <file.kan>            same as `check`
   ========================================================================== *)

let read_file file =
  let ic = open_in_bin file in
  let len = in_channel_length ic in
  let s = really_input_string ic len in
  close_in ic;
  s

(* normalize a path, collapsing "." and ".." segments *)
let normalize path =
  let parts = String.split_on_char '/' path in
  let rec go acc = function
    | [] -> List.rev acc
    | "." :: t -> go acc t
    | ".." :: t -> (match acc with _ :: r -> go r t | [] -> go acc t)
    | x :: t -> go (x :: acc) t
  in
  String.concat "/" (go [] parts)

let canon file = normalize (if Filename.is_relative file then Filename.concat (Sys.getcwd ()) file else file)

(* the import clauses of a file, found without full parsing. Each is
   (path, alias, filter): `import "p"` → (p, None, FAll); `... as M` sets the
   alias; `... exposing (a,b)` / `... hiding (a,b)` sets the filter on the
   unqualified names brought in. *)
let scan_imports toks =
  let n = Array.length toks in
  let at j = if j < n then toks.(j) else Tt.EOF in
  (* parse a `(name, name, …)` list starting at LP index j; returns (names, next) *)
  let name_list j =
    let rec go j acc = match at j with
      | Tt.ID x -> (match at (j + 1) with Tt.COMMA -> go (j + 2) (x :: acc) | _ -> (List.rev (x :: acc), j + 1))
      | Tt.RP -> (List.rev acc, j + 1)
      | _ -> (List.rev acc, j)
    in
    if at j = Tt.LP then go (j + 1) [] else ([], j)
  in
  let rec go i acc =
    if i + 1 >= n then List.rev acc
    else match toks.(i), toks.(i + 1) with
      | Tt.ID "import", Tt.STR p ->
          let j = i + 2 in
          let alias, j = (match at j, at (j + 1) with Tt.ID "as", Tt.ID m -> (Some m, j + 2) | _ -> (None, j)) in
          let filter, j =
            match at j with
            | Tt.ID "exposing" -> let l, j' = name_list (j + 1) in (Tt.FOnly l, j')
            | Tt.ID "hiding" -> let l, j' = name_list (j + 1) in (Tt.FExcept l, j')
            | _ -> (Tt.FAll, j)
          in
          go j ((p, alias, filter) :: acc)
      | _ -> go (i + 1) acc
  in
  go 0 []

(* the `open M` statements of a file: aliases whose names are brought in unqualified *)
let scan_opens toks =
  let n = Array.length toks in
  let rec go i acc =
    if i + 1 >= n then List.rev acc
    else match toks.(i), toks.(i + 1) with
      | Tt.ID "open", Tt.ID m -> go (i + 2) (m :: acc)
      | _ -> go (i + 1) acc
  in
  go 0 []

(* load a program: recursively splice in imports (relative to each importing file's
   directory, each file included at most once), parsing imports BEFORE their importer
   so the shared parser tables see earlier files' datatypes. *)
let load_program entry : Tt.decl list =
  Tt.reset_tables ();
  let visited = Hashtbl.create 16 in
  (* Every file is a module loaded under a unique tag "basename#k" (k disambiguates
     duplicate basenames). Its declarations live under that tag internally; a file
     is loaded once (keyed by canonical path), and `import "x" as M` is a surface
     alias M -> x's tag. *)
  let tags = Hashtbl.create 32 in       (* canonical path -> tag *)
  let base_ct = Hashtbl.create 32 in    (* basename -> next counter *)
  let tag_of file =
    let c = canon file in
    match Hashtbl.find_opt tags c with
    | Some t -> t
    | None ->
        let b = Filename.remove_extension (Filename.basename c) in
        let k = try Hashtbl.find base_ct b with Not_found -> 0 in
        Hashtbl.replace base_ct b (k + 1);
        let t = Printf.sprintf "%s#%d" b k in
        Hashtbl.replace tags c t; t
  in
  (* `ns` accumulates every loaded def's full (tagged) name in load order, so the
     parser can turn a resolved name into a de Bruijn index into the global env. *)
  let rec load ns file =
    let c = canon file in
    if Hashtbl.mem visited c then ([], ns)
    else begin
      Hashtbl.replace visited c ();
      let self = tag_of file in
      let toks = Tt.tokenize (read_file file) in
      let dir = Filename.dirname file in
      let imports = scan_imports toks in
      let idecls, ns1 =
        List.fold_left
          (fun (acc, ns) (p, _alias, _f) -> let d, ns' = load ns (Filename.concat dir p) in (acc @ d, ns'))
          ([], ns) imports
      in
      let aliases =
        List.filter_map
          (fun (p, alias, _f) -> match alias with Some m -> Some (m, tag_of (Filename.concat dir p)) | None -> None)
          imports
      in
      (* an UNQUALIFIED import (no alias) opens its names bare, subject to its filter *)
      let opened_imports =
        List.filter_map
          (fun (p, alias, f) -> match alias with None -> Some (tag_of (Filename.concat dir p), f) | Some _ -> None)
          imports
      in
      (* `open M` also opens an already-aliased module's names, unfiltered *)
      let opened_opens =
        List.map
          (fun m -> match List.assoc_opt m aliases with
             | Some tag -> (tag, Tt.FAll)
             | None -> failwith (Printf.sprintf "open: '%s' is not a module aliased in this file (use `import \"…\" as %s` first)" m m))
          (scan_opens toks)
      in
      let opened = opened_imports @ opened_opens in
      let own = Tt.parse ~ns0:ns1 ~self ~opened ~aliases toks |> List.filter (function Tt.Import _ | Tt.Open _ -> false | _ -> true) in
      let ns2 = List.fold_left (fun a d -> match d with Tt.Def (n, _, _) -> n :: a | _ -> a) ns1 own in
      (idecls @ own, ns2)
    end
  in
  let decls = fst (load [] entry) in
  Tt.check_unique decls;          (* per-module uniqueness: no name declared twice in one file *)
  decls

let die e =
  Printf.eprintf "kan: %s\n" (match e with Failure m -> m | _ -> Printexc.to_string e);
  exit 1

let parse file = load_program file

let do_check file = try Tt.run_decls (load_program file) with e -> die e

let do_run file = try Erase.run (load_program file) with e -> die e

(* `kan explain file` — the Kan lens: render each of the file's own definitions as
   its fiber of the program's initial-model Kan extension (see Tt.describe_decl). *)
let do_explain file =
  try
    let decls = load_program file in
    let entry_tag = Filename.remove_extension (Filename.basename (canon file)) ^ "#0" in
    let prefix = entry_tag ^ "::" in
    let strip s = match String.rindex_opt s ':' with Some i -> String.sub s (i + 1) (String.length s - i - 1) | None -> s in
    let own d = match Tt.describe_decl d with Some (n, _) -> (try String.sub n 0 (String.length prefix) = prefix with Invalid_argument _ -> false) | None -> false in
    print_string
      ("A Kan program is a presentation: each definition is a generator, and the program's\n\
        meaning is its initial model — a left Kan extension of the generators along their\n\
        inclusion. Every definition below is a fiber of that one construction.\n\n");
    List.iter
      (fun d -> if own d then match Tt.describe_decl d with Some (n, desc) -> Printf.printf "  %-12s  %s\n" (strip n) desc | None -> ())
      decls
  with e -> die e

let do_emit_ml file = try print_string (Ocaml_backend.compile (parse file)) with e -> die e
let do_emit_c file = try print_string (C_backend.compile (parse file)) with e -> die e

let default_out file out = match out with Some o -> o | None -> Filename.remove_extension (Filename.basename file)

(* compile to native via OCaml (ocamlopt) *)
let do_build file out =
  try
    let ml_src = Ocaml_backend.compile (parse file) in    (* type-checks and compiles *)
    let out = default_out file out in
    let mlfile = Filename.temp_file "kan_" ".ml" in
    let oc = open_out mlfile in
    output_string oc ml_src;
    close_out oc;
    let base = Filename.remove_extension mlfile in
    let cmd = Printf.sprintf "ocamlopt -w -a %s -o %s 2>/dev/null" (Filename.quote mlfile) (Filename.quote out) in
    let rc = Sys.command cmd in
    List.iter (fun s -> try Sys.remove (base ^ s) with _ -> ()) [ ".ml"; ".cmi"; ".cmx"; ".o" ];
    if rc <> 0 then (Printf.eprintf "kan: native compilation failed (ocamlopt exit %d)\n" rc; exit 1);
    Printf.printf "compiled %s -> %s\n" file out
  with e -> die e

(* compile to native via C (cc) *)
let do_build_c file out =
  try
    let c_src = C_backend.compile (parse file) in         (* type-checks and compiles *)
    let out = default_out file out in
    let cfile = Filename.temp_file "kan_" ".c" in
    let oc = open_out cfile in
    output_string oc c_src;
    close_out oc;
    let cmd = Printf.sprintf "cc -O2 -o %s %s 2>/dev/null" (Filename.quote out) (Filename.quote cfile) in
    let rc = Sys.command cmd in
    (try Sys.remove cfile with _ -> ());
    if rc <> 0 then (Printf.eprintf "kan: C compilation failed (cc exit %d)\n" rc; exit 1);
    Printf.printf "compiled %s -> %s\n" file out
  with e -> die e

let usage () =
  prerr_endline "usage:";
  prerr_endline "  kan check   <file.kan>            type-check and report the types";
  prerr_endline "  kan run     <file.kan>            type-check, then run the program";
  prerr_endline "  kan build   <file.kan> [-o out]   type-check, then compile to a native binary (OCaml)";
  prerr_endline "  kan build -c <file.kan> [-o out]  compile to a native binary via C";
  prerr_endline "  kan emit-ml <file.kan>            print the generated OCaml";
  prerr_endline "  kan emit-c  <file.kan>            print the generated C";
  exit 1

(* Parsing and checking recurse over the input's structure; a large Nat literal
   is a unary tower `suc (suc … zero)` as deep as its value, so `100000` needs a
   ~100k-deep traversal — more than the default 8 MB stack. Re-exec ourselves
   once under a raised stack limit so deep-but-bounded work doesn't overflow.
   (Kan is total, so this only ever accommodates finite, input-bounded depth.)

   Unix only: the trick shells out to /bin/sh + ulimit, neither of which exists
   on Windows (there the stack is fixed at link time and can't be raised at
   startup). On Windows we simply skip it, so very deep Nat literals are bounded
   by the default linked stack rather than the machine's hard limit — fine for
   ordinary programs, and `check`/`run` are unaffected otherwise. *)
let ensure_big_stack () =
  if not Sys.win32 && Sys.getenv_opt "KAN_STACK_RAISED" = None then begin
    let self = Filename.quote Sys.executable_name in
    let args = Array.to_list Sys.argv |> List.tl |> List.map Filename.quote |> String.concat " " in
    let script =
      Printf.sprintf
        "export KAN_STACK_RAISED=1; ulimit -s unlimited 2>/dev/null || ulimit -s \"$(ulimit -Hs)\" 2>/dev/null; exec %s %s"
        self args
    in
    exit (Sys.command ("/bin/sh -c " ^ Filename.quote script))
  end

let () =
  ensure_big_stack ();
  match Array.to_list Sys.argv with
  | _ :: "check" :: [ file ] -> do_check file
  | _ :: "run" :: [ file ] -> do_run file
  | _ :: "explain" :: [ file ] -> do_explain file
  | _ :: "emit-ml" :: [ file ] -> do_emit_ml file
  | _ :: "emit-c" :: [ file ] -> do_emit_c file
  | _ :: "build" :: rest ->
      let rec parse_args f o c = function
        | [] -> (f, o, c)
        | ("-c" | "--c") :: r -> parse_args f o true r
        | "-o" :: v :: r -> parse_args f (Some v) c r
        | x :: r -> parse_args (Some x) o c r
      in
      (match parse_args None None false rest with
       | Some file, out, true -> do_build_c file out
       | Some file, out, false -> do_build file out
       | None, _, _ -> usage ())
  | _ :: [ file ] when Filename.check_suffix file ".kan" -> do_check file
  | _ -> usage ()
