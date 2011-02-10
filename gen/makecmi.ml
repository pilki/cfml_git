open Format
open Parse_type
open Normalize
open Mytools

(*#########################################################################*)

let ppf = Format.std_formatter

let no_mystd_include = ref false

(*#########################################################################*)


let _ =
   Clflags.strict_value_restriction := true;
   Clflags.no_std_include := true;

   (*---------------------------------------------------*)
   let files = ref [] in
   Arg.parse  
     [ ("-I", Arg.String (fun i -> Clflags.include_dirs := i::!Clflags.include_dirs), 
                      "includes a directory where to look for interface files");
       ("-rectypes", Arg.Set Clflags.recursive_types, "activates recursive types");
       ("-nostdlib", Arg.Set no_mystd_include, "do not include standard library");
       ("-nopervasives", Arg.Set Clflags.nopervasives, "do not include standard pervasives file") ]
     (fun f -> files := f::!files)
     ("usage: [-I dir] [..other options..] file.mli");

   (* todo: improve the path to mystdlib *)
   let gen_dir = Filename.dirname Sys.argv.(0) in
   if not !no_mystd_include 
      then Clflags.include_dirs := (gen_dir ^ "/stdlib/")::!Clflags.include_dirs;

   if List.length !files <> 1 
      then failwith "Expects one argument: the filename of the MLI file";
   let sourcefile = List.hd !files in
   let extension = String.sub sourcefile (String.length sourcefile - 3) 3 in
   if extension <> "mli"  
      then failwith "Extension should be .mli";
   let _basename = String.sub sourcefile 0 (String.length sourcefile - 4) in
   let output_prefix =  Misc.chop_extension_if_any sourcefile (* _basename ^ ".cmi"*) in
   typecheck_interface_file ppf sourcefile output_prefix;
   Printf.printf "Wrote %s.cmi\n" output_prefix
