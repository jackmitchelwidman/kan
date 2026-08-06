(* ============================================================================
   kan — command-line driver.
     kan run    <file.kan>            interpret a program (default)
     kan build  <file.kan> [-o out]   compile to a native binary via C
     kan emit-c <file.kan>            print the generated C to stdout
     kan        <file.kan>            same as `run`
   ========================================================================== *)

let read_file file =
  let ic = open_in_bin file in
  let len = in_channel_length ic in
  let s = really_input_string ic len in
  close_in ic; s

let parse_file file = Syntax.parse_string (read_file file)

let die e =
  Printf.eprintf "kan: %s\n" (match e with Failure m -> m | _ -> Printexc.to_string e);
  exit 1

let do_run file = try Interp.run (parse_file file) with e -> die e

let do_check file = try Tt.run (read_file file) with e -> die e

let do_exec file = try Erase.run (Tt.parse (Tt.tokenize (read_file file))) with e -> die e

let do_emit_c file =
  try print_string (Compile.compile (parse_file file)) with e -> die e

let default_out file out = match out with Some o -> o | None -> Filename.remove_extension (Filename.basename file)

(* compile a .kan (fill language) to native via C *)
let do_build_c file out =
  try
    let c_src = Compile.compile (parse_file file) in
    let out = default_out file out in
    let cfile = Filename.temp_file "kan_" ".c" in
    let oc = open_out cfile in
    output_string oc c_src; close_out oc;
    let cmd = Printf.sprintf "cc -O2 -o %s %s" (Filename.quote out) (Filename.quote cfile) in
    let rc = Sys.command cmd in
    (try Sys.remove cfile with _ -> ());
    if rc <> 0 then (Printf.eprintf "kan: C compilation failed (cc exit %d)\n" rc; exit 1);
    Printf.printf "compiled %s -> %s\n" file out
  with e -> die e

(* compile a .ktt (typed language) to native via OCaml *)
let do_build_ml file out =
  try
    let decls = Tt.parse (Tt.tokenize (read_file file)) in
    let ml_src = Ocaml_backend.compile decls in
    let out = default_out file out in
    let mlfile = Filename.temp_file "kan_" ".ml" in
    let oc = open_out mlfile in
    output_string oc ml_src; close_out oc;
    let base = Filename.remove_extension mlfile in
    let cmd = Printf.sprintf "ocamlopt -w -a %s -o %s 2>/dev/null" (Filename.quote mlfile) (Filename.quote out) in
    let rc = Sys.command cmd in
    List.iter (fun s -> try Sys.remove (base ^ s) with _ -> ()) [ ".ml"; ".cmi"; ".cmx"; ".o" ];
    if rc <> 0 then (Printf.eprintf "kan: OCaml compilation failed (ocamlopt exit %d)\n" rc; exit 1);
    Printf.printf "compiled %s -> %s\n" file out
  with e -> die e

let do_build file out =
  if Filename.check_suffix file ".ktt" then do_build_ml file out else do_build_c file out

let usage () =
  prerr_endline "usage:";
  prerr_endline "  kan run    <file.kan>";
  prerr_endline "  kan build  <file.kan> [-o out]";
  prerr_endline "  kan emit-c <file.kan>";
  prerr_endline "  kan check  <file.ktt>     (dependent type theory)";
  prerr_endline "  kan exec   <file.ktt>     (run via type erasure)";
  exit 1

let () =
  match Array.to_list Sys.argv with
  | _ :: "run" :: [ file ] -> do_run file
  | _ :: "check" :: [ file ] -> do_check file
  | _ :: "exec" :: [ file ] -> do_exec file
  | _ :: "emit-c" :: [ file ] -> do_emit_c file
  | _ :: "build" :: rest ->
      let rec parse f o = function
        | [] -> (f, o)
        | "-o" :: v :: r -> parse f (Some v) r
        | x :: r -> parse (Some x) o r
      in
      (match parse None None rest with
       | Some file, out -> do_build file out
       | None, _ -> usage ())
  | _ :: [ file ] when Filename.check_suffix file ".kan" -> do_run file
  | _ -> usage ()
