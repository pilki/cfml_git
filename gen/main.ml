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

(*
let is_making_cmi = ref false
*)

(* err_formatter *)

(*#########################################################################*)

let _ =
   (*
   Clflags.include_dirs := [ "./okasaki" ];
   Clflags.recursive_types := true;
  
   Clflags.no_std_include := true;
   *)

   (*---------------------------------------------------*)
   trace "1) parsing of command line";
   let files = ref [] in
   Arg.parse  
     [ ("-I", Arg.String (fun i -> Clflags.include_dirs := i::!Clflags.include_dirs), 
                      "includes a directory where to look for interface files");
       ("-rectypes", Arg.Set Clflags.recursive_types, "activates recursive types");
       ("-debug", Arg.Set is_tracing, "trace the various steps") ]
     (fun f -> files := f::!files)
     ("usage: -I dir -rectypes file.ml");
   (*
   let args = Sys.argv in
   if Array.length args < 2 then
      failwith "Expects one argument: the filename of the ML source file";
   let sourcefile = args.(1) in
   *)
   trace "1) parsing of command line";
   if List.length !files <> 1 then
      failwith "Expects one argument: the filename of the ML source file";
   let sourcefile = List.hd !files in
   let basename = String.sub sourcefile 0 (String.length sourcefile - 3) in
   let outputfile = basename ^ "_ml.v" in
   let dirname = Filename.dirname sourcefile in
   let debugdir = dirname ^ "/output/" in

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

   (*---------------------------------------------------*)
   trace "5) constructing caracteristic formula ast";
   let cftops = Characteristic.cfg_file typedtree2 in

   (*---------------------------------------------------*)
   trace "6) converting caracteristic formula ast to coq ast";
   let coqtops = Formula.coqtops_of_cftops cftops in

   (*---------------------------------------------------*)
   trace "7) printing coq ast";
   let result = Coq.string_of_coqtops coqtops in
   file_put_contents (debugdir ^ "_formulae.ml") result; 
   file_put_contents outputfile (cutlines 50 result); 

   (*---------------------------------------------------*)
   print_string "*) characteristic formulae successfully generated\n"





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
