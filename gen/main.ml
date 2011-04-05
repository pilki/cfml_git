open Format
open Parse_type
open Normalize
open Mytools

(*#########################################################################*)

let is_tracing = ref false

let trace s =
  if !is_tracing 
     then (print_string s; print_newline())

let ppf = Format.std_formatter

let onlycmi = ref false

let no_mystd_include = ref false

(* err_formatter *)

(*#########################################################################*)

let _ =
   Clflags.strict_value_restriction := true;
   Clflags.no_std_include := true;

   (*---------------------------------------------------*)
   trace "1) parsing of command line";
   let files = ref [] in
   Arg.parse  
     [ ("-I", Arg.String (fun i -> Clflags.include_dirs := i::!Clflags.include_dirs), 
                      "includes a directory where to look for interface files");
       ("-pure", Arg.Set Characteristic.pure_mode, "generate formulae for purely-functional code");
       ("-rectypes", Arg.Set Clflags.recursive_types, "activates recursive types");
       ("-nostdlib", Arg.Set no_mystd_include, "do not include standard library");
       ("-nopervasives", Arg.Set Clflags.nopervasives, "do not include standard pervasives file");
       ("-onlycmi", Arg.Set onlycmi, "only generate the cmi file, not the coq file");
       ("-debug", Arg.Set is_tracing, "trace the various steps") ]
     (fun f -> files := f::!files)
     ("usage: [-I dir] [..other options..] file.ml");
   (*
   let args = Sys.argv in
   if Array.length args < 2 then
      failwith "Expects one argument: the filename of the ML source file";
   let sourcefile = args.(1) in
   *)

   (* todo: improve the path to mystdlib *)
   let gen_dir = Filename.dirname Sys.argv.(0) in
   if not !no_mystd_include 
      then Clflags.include_dirs := (gen_dir ^ "/camllib")::!Clflags.include_dirs;

   trace "1) parsing of command line";
   if List.length !files <> 1 then
      failwith "Expects one argument: the filename of the ML source file";
   let sourcefile = List.hd !files in
   let basename = String.sub sourcefile 0 (String.length sourcefile - 3) in
   let outputfile = basename ^ "_ml.v" in
   let dirname = Filename.dirname sourcefile in
   let debugdir = dirname ^ "/output/" in
   (*  FAILURE ON WINDOWS
   let cmd = Printf.sprintf "test -d %s || mkdir 640 %s" debugdir debugdir in
   begin try ignore (Sys.command cmd)
         with _ -> Printf.printf "Could not create debug directory\n" end;
     *)

   (*---------------------------------------------------*)
   if sourcefile = "imper/MyLib.ml" then exit 0;

   (*---------------------------------------------------*)
   trace "2) reading and typing source file";
   let (opt,inputfile) = process_implementation_file ppf sourcefile in
   let parsetree1 : Parsetree.structure =
      match opt with
      | None -> failwith "Could not read and typecheck input file"
      | Some (parsetree1, typedtree1) -> parsetree1
      in
   file_put_contents (debugdir ^ "_original.ml") (Print_past.string_of_structure parsetree1); 

   (*---------------------------------------------------*)
   trace "3) normalizing source code";
   let parsetree2 : Parsetree.structure = normalize_structure parsetree1 in
   file_put_contents (debugdir ^ "_normalized.ml") (Print_past.string_of_structure parsetree2); 

   (*---------------------------------------------------*)
   trace "4) typing normalized code";
   let (typedtree2, _ : Typedtree.structure * Typedtree.module_coercion) = 
      match typecheck_implementation_file ppf sourcefile parsetree2 with
      | None -> failwith "Could not typecheck the normalized source code\nCheck out the file output/_normalized.ml." 
      | Some typedtree2 -> typedtree2
      in
   file_put_contents (debugdir ^ "_normalized_typed.ml") (Print_tast.string_of_structure typedtree2); 
   ignore (typedtree2);

   if !onlycmi then begin
      trace "5) exiting after cmi has been generated";
      exit 0;
   end;


   (*---------------------------------------------------*)
   trace "5) constructing caracteristic formula ast";
   let cftops = Characteristic.cfg_file typedtree2 in

   (*---------------------------------------------------*)
   trace "6) converting caracteristic formula ast to coq ast";
   let coq_to_cf = if !Characteristic.pure_mode 
      then Formula.coq_of_pure_cf
      else Formula.coq_of_imp_cf in
   let coqtops = Formula.coqtops_of_cftops coq_to_cf cftops in

   (*---------------------------------------------------*)
   trace "7) printing coq ast";
   let result = Coq.string_of_coqtops coqtops in
   file_put_contents (debugdir ^ "_formulae.ml") result; 
   file_put_contents outputfile (cutlines 50 result); 

   (*---------------------------------------------------*)
   trace "8) characteristic formulae successfully generated\n"


(*########################################################
todo:
- top level functions should not be named
- fun p1 p2   transformation only works for exhaustive patterns
  => check   | Texp_function of (pattern * expression) list * partial
     always partial !!
*)

(*
"Require Import FuncDefs.\n\n"coqtop_set_implicit_arguments
*)
(*
Clflags.no_std_include := true;
*)
