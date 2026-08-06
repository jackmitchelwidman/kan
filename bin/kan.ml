(* ============================================================================
   kan — the Kan command-line driver.

   Kan is a dependently typed language; its files are .kan.
     kan check <file.kan>            type-check and report the types
     kan run   <file.kan>            type-check, then run the program
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

let parse file = Tt.parse (Tt.tokenize (read_file file))

let die e =
  Printf.eprintf "kan: %s\n" (match e with Failure m -> m | _ -> Printexc.to_string e);
  exit 1

let do_check file = try Tt.run (read_file file) with e -> die e

let do_run file = try Erase.run (parse file) with e -> die e

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

let () =
  match Array.to_list Sys.argv with
  | _ :: "check" :: [ file ] -> do_check file
  | _ :: "run" :: [ file ] -> do_run file
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
