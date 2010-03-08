open Misc
open Asttypes
open Types
open Parsetree
open Mytools
open Longident
open Format


(*#########################################################################*)
(* Printing of base values *)

let string_of_ident s = 
   Ident.name s

let string_of_lident idt =
   let names = Longident.flatten idt in
   String.concat "." names

let string_of_constant = function
  | Const_int n -> string_of_int n
  | Const_char c -> String.make 1 c
  | Const_string s -> s
  | Const_float f -> f
  | Const_int32 _ -> unsupported "int32 type"
  | Const_int64 _ -> unsupported "int64 type"
  | Const_nativeint _ -> unsupported "native int type"

let string_of_recflag = function
  | Nonrecursive -> ""
  | Recursive -> " rec" 
  | Default -> " DEFAULT"


(*#########################################################################*)
(* Printing of patterns *)

let string_of_pattern par p =
   let rec aux par p =
     match p.ppat_desc with
     | Ppat_any -> "_"
     | Ppat_var s -> s
     | Ppat_alias (p, s) -> 
         show_par par (sprintf "%s as %s" (aux false p) s)
     | Ppat_constant c -> 
         sprintf "%s" (string_of_constant c)
     | Ppat_tuple l -> 
         show_par true (sprintf "%s" (show_list (aux false) "," l))
     | Ppat_construct (li, po, b) -> 
         if (b != false) then unsupported "construct with options";
         let s = sprintf "%s%s" 
           (string_of_lident li)
           (show_option (aux true) po) in
         show_par par s
     | Ppat_lazy p1 -> 
        show_par par (sprintf "lazy %s" (aux true p1))
     | Ppat_variant (_,_) -> unsupported "variant patterns"
     | Ppat_record _ -> unsupported "record patterns"
     | Ppat_array pats -> unsupported "array patterns"
     | Ppat_or (p1,p2) -> 
         show_par par (sprintf "%s | %s" (aux false p1) (aux false p2))
     | Ppat_constraint (p,t) -> sprintf "(%s : _)" (aux false p)
     | Ppat_type t -> unsupported "type patterns"
     in
  aux false p


(*#########################################################################*)
(* Printing of expression *)

let rec string_of_expression par e =
   let aux ?par e =
      string_of_expression (bool_of_option par) e in
   let aux_pat ?par e =
      string_of_pattern (bool_of_option par) e in
   let string_of_branch (p,e) =
      Format.sprintf "@[@[%s@] ->@ @[%s@]@]" (aux_pat p) (aux e) in
  
   match e.pexp_desc with
   | Pexp_ident li -> string_of_lident li
   | Pexp_constant c -> string_of_constant c
   | Pexp_let (rf, l, e) -> 
       Format.sprintf "@[let%s %s in@ @[%s@]@]" 
         (string_of_recflag rf)
         (show_list (fun (p,e) -> Format.sprintf "%s =@ @[%s@]" (aux_pat p) (aux e)) " and " l)
         (aux e)     
   | Pexp_function (pf, None, (p1,e1)::[]) -> 
       let rec explore pats e =
          match e.pexp_desc with 
          | Pexp_function (pf, None, (p1,e1)::[]) ->
             explore (p1::pats) e1
          | _ -> List.rev pats, e
          in
       let pats,body = explore [] e in
       let s = Format.sprintf "@[fun @[%s@] ->@ @[%a@]@]" 
         (show_list aux_pat " " pats)
         (fun () -> aux ~par:false) body in
      show_par par s
   | Pexp_function (p1, None, l) ->  
       Format.sprintf "@[function %s@]" (show_listp string_of_branch "\n  | " l)
   | Pexp_function (p, Some _, l) -> unsupported "function with optional expression"
   | Pexp_apply (e, l) ->       (* todo: afficher les infixes correctement *)
      let s = (aux ~par:true e) ^ " " ^ (show_list (aux ~par:true) " " (List.map snd l)) in
      show_par par s
   | Pexp_match (e, l) -> 
       let s = Format.sprintf "@[match@ @[%s@] with@ @[%s@]@]" 
          (aux e) (show_list string_of_branch " | " l) in
       show_par par s
   | Pexp_try (e,l) -> unsupported "exceptions"
   | Pexp_tuple l -> 
       show_par true (show_list aux ", " l)
   | Pexp_construct (li, eo, b) -> 
       if (b != false)
         then unsupported "data constructor with option";
       let s = Format.sprintf "@[%s%s@]" (string_of_lident li)
                 (show_option (aux ~par:true) eo) in
       show_par par s
   | Pexp_variant (l,eo) -> unsupported "variants"
   | Pexp_record (l,Some eo) -> unsupported "record-with"
   | Pexp_record (l,None) -> unsupported "record"
      (* 
      let l',bi = List.split (List.map (fun (i,e) -> let e',b = aux e in ((i,e'),b)) l) in
      Pexp_record (l', None), bi
      *)
   | Pexp_field (e,i) -> unsupported "record"
       (* let e',b = aux e in
       Pexp_field (e', i), b *)
   | Pexp_setfield (e,i,e2) -> unsupported "record"
       (* let e',b = aux e in
       let e2',b2 = aux e2 in
       Pexp_setfield (e', i, e2'), b2 @ b  *)
   | Pexp_array l -> unsupported "array expression" (* Pexp_array (List.map aux l)*)
   | Pexp_ifthenelse (e1, e2, None) -> unsupported "if-without-else-clause expressions"
   | Pexp_ifthenelse (e1, e2, Some e3) ->
       let s = Format.sprintf "@[if %s@ then %s@ %s@]" (aux e1) (aux e2) (aux e3) in
       show_par par s
   | Pexp_sequence (e1,e2) -> unsupported "sequence expression"  (* Pexp_sequence (aux e1, aux e2)*)
   | Pexp_while (e1,e2) -> unsupported "while expression"  (* Pexp_while (aux e1, aux e2)*)
   | Pexp_for (s,e1,e2,d,e3) -> unsupported "for expression"  (*Pexp_for (s, aux e1, aux e2, d, aux e3) *)
   | Pexp_constraint (e,to1,to2) -> 
       let s = Format.sprintf "@[(%s@ : _)]" (aux e) in
       show_par par s
   | Pexp_when (e1,e2) ->  (*todo:better printing so that compiles *)
       Format.sprintf "<< when %s >> %s" (aux e1) (aux e2) 
   | Pexp_send (_,_) -> unsupported "send expression"
   | Pexp_new _ -> unsupported "new expression"
   | Pexp_setinstvar (_,_) -> unsupported "set-inst-var expression"
   | Pexp_override _ -> unsupported "Pexp_override expression"
   | Pexp_letmodule (_,_,_) -> unsupported "let-module expression"
   | Pexp_assert e -> unsupported "assertions other than [assert false]"          
   | Pexp_assertfalse -> 
       show_par par "assert false"
   | Pexp_lazy e -> 
       let s = Format.sprintf "@[lazy %s]" (aux e) in
       show_par par s
   | Pexp_poly (_,_) -> unsupported "poly expression"
   | Pexp_object _ -> unsupported "objects"
   

(*#########################################################################*)
(* Normalization of modules and top-level phrases *)

let rec string_of_module m =
   match m.pmod_desc with
   | Pmod_ident li -> string_of_lident li
   | Pmod_structure s -> sprintf "struct\n%s\nend\n" (string_of_structure s) 
   | Pmod_functor (s,mt,me) -> sprintf "%s : _ ==>%s\n" s (string_of_module me) 
   | Pmod_apply (me1,me2) -> sprintf "%s %s" (string_of_module me1) (string_of_module me2)
   | Pmod_constraint (me,mt) -> sprintf "(%s : _)" (string_of_module me)

and string_of_structure s =
  show_list string_of_structure_item lin2 s

and string_of_structure_item si =
   match si.pstr_desc with
   | Pstr_eval e -> sprintf "let _ = %s" (string_of_expression false e)
   | Pstr_value (r,l) -> 
       let show_pe (p,e) =
          let sp = string_of_pattern false p in
          let se = string_of_expression false e in
          Format.sprintf "%s =@ @[%s@]" sp se in
       let sl = show_list show_pe " and " l in
       Format.sprintf "@[let%s %s]" (string_of_recflag r) sl 
   | Pstr_primitive (s,v) -> sprintf "val %s : _" s 
   | Pstr_type l -> sprintf "type _ = _"
   | Pstr_exception (s,e) -> sprintf "exception %s = _" s
   | Pstr_exn_rebind (s,i) -> unsupported "exception-rebind"
   | Pstr_module (s,m) -> Format.sprintf "@[module %s =@ @[<2>%s] @]" s (string_of_module m)
   | Pstr_recmodule _ -> unsupported "recursive modules"
   | Pstr_modtype (s,mt) -> sprintf "module type %s = _" s
   | Pstr_open li -> sprintf "open %s = _" (string_of_lident li)
   | Pstr_class _ -> unsupported "objects"
   | Pstr_class_type _ -> unsupported "objects"
   | Pstr_include m -> sprintf "include %s" (string_of_module m)

and string_of_toplevel_phrase p =
  match p with
  | Ptop_def s -> string_of_structure s
  | Ptop_dir (s,d) -> ""

and string_of_source s =
  show_list string_of_toplevel_phrase lin2 s

