open Misc
open Asttypes
open Types
open Typedtree
open Mytools
open Longident
open Format
open Print_past
open Print_type

(** Printing facility for typed abstract syntax trees produced by the 
    type-checker*)

(*#########################################################################*)
(* ** Printing of items *)

let string_of_typed_var s t =
   sprintf "(%s : %s)" s (string_of_type_exp t)

let string_of_path p = 
   Path.name p

let string_of_constructor cd =
   string_of_path (cd.ctrs_path)


(*#########################################################################*)
(* ** Printing of patterns *)

let string_of_pattern par p =
   let rec aux par p =
     match p.pat_desc with
     | Tpat_any -> "_"
     | Tpat_var id -> string_of_typed_var (string_of_ident id) p.pat_type
     | Tpat_alias (p, id) -> 
         show_par par (sprintf "%s as %s" (aux false p) (string_of_typed_var (string_of_ident id) p.pat_type))
     | Tpat_constant c -> 
         sprintf "%s" (string_of_constant c)
     | Tpat_tuple l -> 
         show_par true (sprintf "%s" (show_list (aux false) "," l))
     | Tpat_construct (cd,ps) -> 
         let c = string_of_constructor cd in
         if ps = []
            then c
         else if List.length ps = 1 
            then show_par par (c ^ " " ^ aux true (List.hd ps))
         else
            show_par par (sprintf "%s (%s)" c (show_list (aux false) "," ps))
     | Tpat_or (p1,p2,_) -> 
         show_par par (sprintf "%s | %s" (aux false p1) (aux false p2))
     | Tpat_lazy p1 -> 
        show_par par (sprintf "lazy %s" (aux true p1))
     | Tpat_variant (_,_,_) -> unsupported "variant patterns"
     | Tpat_record _ -> unsupported "record patterns"
     | Tpat_array pats -> unsupported "array patterns"
     in
  aux false p

let string_of_let_pattern par fvs p =
   let typ = p.pat_type in
   let styp = string_of_type_sch fvs typ in
   sprintf "%s : %s" (string_of_pattern par p) styp
   (* 
   match p.pat_desc with
   | Tpat_var id -> 
      let typ = p.pat_type in
      sprintf "%s : %s" (string_of_ident id) (string_of_type_sch fvs typ)
   | _ -> unsupported "let-pattern not reduced to a variable"
   *)  

(*#########################################################################*)
(* ** Printing of expression *)

let rec string_of_expression par e =
   let aux ?par e =
      string_of_expression (bool_of_option par) e in
   let aux_pat ?par e =
      string_of_pattern (bool_of_option par) e in
   let string_of_branch (p,e) =
      Format.sprintf "@[@[%s@] ->@ @[%s@]@]" (aux_pat p) (aux e) in
   (*let typ = e.exp_type in*)
   match e.exp_desc with
   | Texp_ident (p,vd) -> string_of_path p (*  string_of_typed_var (string_of_path p) vd.val_type*)
   | Texp_constant c -> string_of_constant c
   | Texp_let (rf, fvs, l, e) ->  (* TODO FVS *)
       let show_pe (p,e) =
          let sp = (string_of_let_pattern false fvs p) in
          let se = aux e in
          Format.sprintf "%s =@ @[%s@]" sp se in
       let sl = show_list show_pe " and " l in
       let se = aux e in
       Format.sprintf "@[let%s %s in@ @[%s@]@]" (string_of_recflag rf) sl se 
   | Texp_function ((p1,e1)::[], pa) ->
       let rec explore pats e =
          match e.exp_desc with 
          | Texp_function ((p1,e1)::[], pa) ->
             explore (p1::pats) e1
          | _ -> List.rev pats, e
          in
       let pats,body = explore [] e in
       let sp = show_list aux_pat " " pats in
       let sb = aux ~par:false body in
       let s = Format.sprintf "@[fun @[%s@] ->@ @[%s@]@]" sp sb in
      show_par par s
   | Texp_function (l, pa) ->  
       Format.sprintf "@[function %s@]" (show_listp string_of_branch "\n  | " l)
   | Texp_apply (e, l) -> (* todo: afficher les infixes correctement *)
      let l = List.map (fun (eo,opt) -> match eo with None -> unsupported "optional apply arguments" | Some ei -> ei) l in
      let se = aux ~par:true e in
      let show_arg ei =
         let s_ei = aux ~par:false ei in
         let t_ei = string_of_type_exp ei.exp_type in
         sprintf "(%s : %s)" s_ei t_ei in
      let sl = show_list show_arg " " l in
      let s = sprintf "%s %s" se sl in
      show_par par s
   | Texp_match (e, l, pa) -> 
       let se = aux e in
       let s = Format.sprintf "@[match@ @[%s@] with@ @[%s@]@]" 
          se (show_list string_of_branch " | " l) in
       show_par par s
   | Texp_try (e,l) -> unsupported "exceptions"
   | Texp_tuple l -> 
       show_par true (show_list aux ", " l)
   | Texp_construct (cd, es) -> 
         let c = string_of_constructor cd in
         if es = []
            then c
         else if List.length es = 1 
            then show_par par (c ^ " " ^ aux ~par:true (List.hd es))
         else
            show_par par (sprintf "%s (%s)" c (show_list aux "," es))
   | Texp_variant (l,eo) -> unsupported "variants"
   | Texp_record (l,Some eo) -> unsupported "record-with"
   | Texp_record (l,None) ->        
       let print_item (li,ei) = 
          Format.sprintf "%s = %s" (li.lbl_name) (aux ei) in
       let s = Format.sprintf "@[{%s}@]" (show_list print_item "; " l) in
       show_par par s
   | Texp_field (e,i) -> 
       let s = Format.sprintf "@[%s.%s@]" (aux e) (i.lbl_name) in
       show_par par s
   | Texp_setfield (e,i,e2) -> 
       let s = Format.sprintf "@[%s.%s <- %s@]" (aux e) (i.lbl_name) (aux e2) in
       show_par par s
   | Texp_array l -> unsupported "array expression" (* Texp_array (List.map aux l)*)
   | Texp_ifthenelse (e1, e2, None) ->
       let s = Format.sprintf "@[if %s@ then %s@]" (aux e1) (aux e2) in
       show_par par s
   | Texp_ifthenelse (e1, e2, Some e3) ->
       let s = Format.sprintf "@[if %s@ then %s@ else %s@]" (aux e1) (aux e2) (aux e3) in
       show_par par s
   | Texp_when (e1,e2) ->  (*todo:better printing so that compiles *)
       Format.sprintf "<< when %s >> %s" (aux e1) (aux e2) 
   | Texp_sequence (e1,e2) -> 
       let s = Format.sprintf "@[%s@ ; %s@]" (aux e1) (aux e2) in
       show_par par s
   | Texp_while (e1,e2) -> 
       let s = Format.sprintf "@[while %s@ do %s@ done@]" (aux e1) (aux e2) in
       show_par par s
   | Texp_for (i,e1,e2,d,e3) -> 
       let s = Format.sprintf "@[for %s = %s to %s do@ %s@ done@]" (Ident.name i) (aux e1) (aux e2) (aux e3) in
       show_par par s
   | Texp_send (_,_) -> unsupported "send expression"
   | Texp_new _ -> unsupported "new expression"
   | Texp_instvar (_,_) -> unsupported "inst-var expression"
   | Texp_setinstvar (_,_,_) -> unsupported "set-inst-var expression"
   | Texp_override _ -> unsupported "Pexp_override expression"
   | Texp_letmodule (_,_,_) -> unsupported "let-module expression"
   | Texp_assert e -> unsupported "assertions other than [assert false]"          
   | Texp_assertfalse -> 
       show_par par "assert false"
   | Texp_lazy e -> 
       let s = Format.sprintf "@[lazy %s@]" (aux e) in
       show_par par s
   | Texp_object _ -> unsupported "objects"
   

(*#########################################################################*)
(* ** Normalization of modules and top-level phrases *)

let rec string_of_module m =
   match m.mod_desc with
   | Tmod_ident p -> string_of_path p
   | Tmod_structure s -> sprintf "struct\n%s\nend\n" (string_of_structure s) 
   | Tmod_functor (id,mt,me) -> sprintf "%s : _ ==>%s\n" (string_of_ident id) (string_of_module me) 
   | Tmod_apply (me1,me2,mc) -> sprintf "%s %s" (string_of_module me1) (string_of_module me2)
   | Tmod_constraint (me,mt,mc) -> sprintf "(%s : _)" (string_of_module me)

and string_of_structure s =
  show_list string_of_structure_item lin2 s

and string_of_structure_item si =
   Printtyp.reset();
   match si with
   | Tstr_eval e -> sprintf "let _ = %s" (string_of_expression false e)
   | Tstr_value (r,fvs,l) -> 
       let show_pe (p,e) =
          let sp = string_of_let_pattern false fvs p in
          let se = string_of_expression false e in
          Format.sprintf "%s =@ @[%s@]" sp se in
       let sl = show_list show_pe " and " l in
       Format.sprintf "@[let%s %s@]" (string_of_recflag r) sl 
      (* Format.sprintf "@[let%s %s =@ @[<2>%s@]@]" *)
   | Tstr_primitive (id,v) -> sprintf "val %s : _" (string_of_ident id)
   | Tstr_type l -> sprintf "type _ = _"
   | Tstr_exception (id,e) -> sprintf "exception %s = _" (string_of_ident id)
   | Tstr_exn_rebind (id,p) -> unsupported "exception-rebind"
   | Tstr_module (id,m) -> Format.sprintf "@[module %s =@ @[<2>%s] @]" (string_of_ident id) (string_of_module m)
   | Tstr_recmodule _ -> unsupported "recursive modules"
   | Tstr_modtype (id,mt) -> sprintf "module type %s = _" (string_of_ident id)
   | Tstr_open p -> sprintf "open %s = _" (string_of_path p)
   | Tstr_class _ -> unsupported "objects"
   | Tstr_cltype _ -> unsupported "objects"
   | Tstr_include (m,ids) -> sprintf "include %s" (string_of_module m)
