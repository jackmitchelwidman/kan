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

let do_build file out =
  try
    let ml_src = Ocaml_backend.compile (parse file) in    (* type-checks and compiles *)
    let out = match out with Some o -> o | None -> Filename.remove_extension (Filename.basename file) in
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

let usage () =
  prerr_endline "usage:";
  prerr_endline "  kan check   <file.kan>            type-check and report the types";
  prerr_endline "  kan run     <file.kan>            type-check, then run the program";
  prerr_endline "  kan build   <file.kan> [-o out]   type-check, then compile to a native binary";
  prerr_endline "  kan emit-ml <file.kan>            print the generated OCaml";
  exit 1

let () =
  match Array.to_list Sys.argv with
  | _ :: "check" :: [ file ] -> do_check file
  | _ :: "run" :: [ file ] -> do_run file
  | _ :: "emit-ml" :: [ file ] -> do_emit_ml file
  | _ :: "build" :: rest ->
      let rec parse_args f o = function
        | [] -> (f, o)
        | "-o" :: v :: r -> parse_args f (Some v) r
        | x :: r -> parse_args (Some x) o r
      in
      (match parse_args None None rest with Some file, out -> do_build file out | None, _ -> usage ())
  | _ :: [ file ] when Filename.check_suffix file ".kan" -> do_check file
  | _ -> usage ()
