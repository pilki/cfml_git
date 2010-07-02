open Misc
open Asttypes
open Types
open Parsetree
open Mytools
open Longident
open Location
open Primitives


(*#########################################################################*)
(* Management of fresh identifiers *)

let name_of_lident idt =
  let words = Longident.flatten idt in
  let name = List.hd (List.rev words) in
  name

let fullname_of_lident idt =
  let words = Longident.flatten idt in
  String.concat "." words

let check_var loc x =
   if loc.loc_ghost then () else (* todo: avoid this hack *)
   if String.length x > 1 && x.[0] = '_' 
      then unsupported ("variables cannot be prefixed with underscore: " ^ x)

let check_lident loc idt =
   check_var loc (name_of_lident idt)

(*#########################################################################*)
(* Detection of primitive and exception-raising functions *)

(* todo: forbid rebinding of primitive names *)

let is_inlined_primitive e largs =
    let args = List.map snd largs in (* todo: check no labels*)
    match e.pexp_desc, args with 
    | Pexp_ident f, [n; {pexp_desc = Pexp_constant (Const_int m)}]  
        when m > 0 && let x = name_of_lident f in x = "mod" || x = "/" -> 
        is_inlined_primitive_name (fullname_of_lident f) primitive_special
    | Pexp_ident f,_ -> 
        is_inlined_primitive_name (fullname_of_lident f) (List.length args)
    | _ -> false

let is_failwith_function e =
   match e.pexp_desc with
   | Pexp_ident li ->
      begin match Longident.flatten li with
      | f::[] -> (f = "failwith") || (f = "invalid_arg") || (f = "raise") 
      | _ -> false
      end
   | _ -> false

(*#########################################################################*)
(* Normalization of patterns *)

let normalize_pattern p =
   let i = ref (-1) in
   let next_name () =
      incr i; ("_p" ^ string_of_int !i) in
   let rec aux p =
     let loc = p.ppat_loc in
     { p with ppat_desc = match p.ppat_desc with
     | Ppat_any -> Ppat_var (next_name())
     | Ppat_var s -> check_var loc s; Ppat_var s
     | Ppat_alias (p, s) -> check_var loc s; Ppat_alias (aux p, s)
     | Ppat_constant c -> Ppat_constant c
     | Ppat_tuple l -> Ppat_tuple (List.map aux l)
     | Ppat_construct (li, po, b) -> Ppat_construct (li, option_map aux po, b)
     | Ppat_variant (_,_) -> unsupported "variant patterns"
     | Ppat_record l -> Ppat_record (List.map (fun (li,pi) -> (li, aux pi)) l)
     | Ppat_array pats -> unsupported "array patterns"
     | Ppat_or (p1,p2) -> unsupported "or patterns are only supported at pattern root"
     | Ppat_constraint (p,t) -> Ppat_constraint (aux p,t) 
     | Ppat_type t -> Ppat_type t
     | Ppat_lazy p1 -> Ppat_lazy (aux p1)
     } in
  aux p


(*#########################################################################*)
(* Free variables of patterns and values *)

let rec pattern_variables p =
   let aux = pattern_variables in
   match p.ppat_desc with
   | Ppat_any -> []
   | Ppat_var s -> [s]
   | Ppat_alias (p, s) -> s::(aux p)
   | Ppat_constant c -> []
   | Ppat_tuple l -> list_concat_map aux l
   | Ppat_construct (li, po, b) -> option_app [] aux po
   | Ppat_variant (_,_) -> unsupported "variant patterns"
   | Ppat_record l -> list_concat_map (fun (li,pi) -> aux pi) l
   | Ppat_array pats -> unsupported "array patterns"
   | Ppat_or (p1,p2) -> unsupported "or patterns are only supported at pattern root"
   | Ppat_constraint (p,t) -> aux p
   | Ppat_type t -> []
   | Ppat_lazy p1 -> aux p1

let rec values_variables e =
   let aux = values_variables in
   match e.pexp_desc with
   | Pexp_ident (Lident x) -> [x]
   | Pexp_ident li -> []
   | Pexp_constant c -> []
   | Pexp_apply (e0, l) when is_inlined_primitive e0 l -> 
      list_concat_map aux (List.map snd l)
   | Pexp_tuple l -> 
      list_concat_map aux l
   | Pexp_construct (li, eo, b) -> 
      option_app [] aux eo
   | Pexp_field (e,i) -> 
      aux e
   | Pexp_constraint (e,to1,to2) -> 
      aux e
   | Pexp_assertfalse -> 
      []
   | Pexp_lazy e ->
      aux e
   | _ -> failwith "Bug in normalization: values_variables called on a non-atomic value"
   (*  
   | Pexp_record (l,Some eo) -> unsupported "record-with"
   | Pexp_record (l,None) -> 
      let l',bi = List.split (List.map (fun (i,(e,b)) -> ((i,e),b)) (assoc_list_map (aux false) l)) in
      return (Pexp_record (l', None)), List.flatten bi
   | Pexp_array l -> unsupported "array expression" (* Pexp_array (List.map aux l)*)
   *)


(*#########################################################################*)
(* Normalization of expression *)

type bindings = (pattern*expression) list

let create_let loc (bs:bindings) (e:expression) =
   let rec aux = function
      | [] -> e
      | b::bs ->
         { pexp_loc = loc; 
           pexp_desc = Pexp_let (Nonrecursive, [b], aux bs) } in
   aux bs

let create_match_one loc exp pat body =
   { pexp_loc = loc; 
     pexp_desc = Pexp_match (exp,[pat,body]) }


let get_assign_fct loc already_named new_name : expression -> bindings -> expression * bindings =
   if already_named 
      then fun e b -> e,b
      else let x = new_name() in
           fun e b ->
              let p = { ppat_loc = Location.none; ppat_desc = Ppat_var x } in
              let e' = { pexp_loc = Location.none; pexp_desc = Pexp_ident (Lident x) } in
              e', b @ [ p, e ]

(* todo: check eval order *)
let normalize_expression named e =
   let i = ref (-1) in
   let next_var () =
      incr i; ("_x" ^ string_of_int !i) in
   let j = ref (-1) in
   let next_func () =
      incr j; ("_f" ^ string_of_int !j) in
   let rec aux named (e:expression) : expression * bindings = 
     let loc = e.pexp_loc in
     let return edesc' = 
       { e with pexp_desc = edesc' } in
     let assign_fct pick_var = 
         get_assign_fct loc named pick_var in
     match e.pexp_desc with
      | Pexp_ident li -> check_lident loc li; return (Pexp_ident li), []
      | Pexp_constant c -> return (Pexp_constant c), []
      | Pexp_let (Recursive, l, b) -> 
          let assign = assign_fct next_var in
          let l' = List.map protect_branch l in
          let b' = protect true b in
          let e' = Pexp_let (Recursive, l', b') in
          assign (return e') []
      | Pexp_let (rf, [], e2) -> unsupported "let without any binding"
      | Pexp_let (rf, [p1,e1], e2) ->
         begin match p1.ppat_desc with
         | Ppat_var x 
         | Ppat_constraint ({ ppat_desc = Ppat_var x}, _) ->
             let assign = assign_fct next_var in
             let e1',b1 = aux true e1 in
             let e' = create_let loc b1 (
                      create_let loc [normalize_pattern p1, e1'] (
                       protect named e2)) in
             assign e' []
         | _ ->  
             let assign = assign_fct next_var in
             let e1',b1 = aux false e1 in
             let e' = create_let loc b1 (
                      create_match_one loc e1' (normalize_pattern p1) (protect named e2)) in
             assign e' []
         end
      | Pexp_let (rf, l, e) -> 
          let check_is_named_pat p =
             match p.ppat_desc with
             | Ppat_var x 
             | Ppat_constraint ({ ppat_desc = Ppat_var x}, _) -> true
             | _ -> false
             in
          if not (List.for_all check_is_named_pat (List.map fst l))
             then unsupported "let-rec with patterns not reduced to names";
          aux true (List.fold_right (fun (pi,ei) eacc -> create_let loc [pi,ei] eacc) l e)
      | Pexp_function (lab, None, [_]) -> 
          let rec protect_func (ms : (expression * pattern) list) (e : expression) = 
             match e.pexp_desc with 
             | Pexp_function (lab, None, [p, e']) ->  
                 let p' = normalize_pattern p in
                 begin match p'.ppat_desc with
                 | Ppat_var x
                 | Ppat_constraint ({ ppat_desc = Ppat_var x}, _) -> 
                    return (Pexp_function (lab, None, [p', protect_func ms e'])) 
                    (* todo: type annotations in pattern get lost *)
                 | Ppat_construct (li, None, b) when Longident.flatten li = ["()"] -> 
                    let x = next_var() in
                    let px = { ppat_loc = Location.none; ppat_desc = Ppat_var x } in
                    return (Pexp_function (lab, None, [px, protect_func ms e'])) 
                 | _ ->
                    let x = next_var() in
                    let px = { ppat_loc = Location.none; ppat_desc = Ppat_var x } in
                    let vx = { pexp_loc = Location.none; pexp_desc = Pexp_ident (Lident x) } in
                    let ms' = (vx, p')::ms in
                    return (Pexp_function (lab, None, [px, protect_func ms' e']))
                 end
             | _ -> 
                let addmatch eacc (vi,pi) =
                   return (Pexp_match (vi, [pi,eacc])) in
                List.fold_left addmatch (protect true e) ms 
            in
          let assign = assign_fct next_func in
          assign (protect_func [] e) []
      | Pexp_function (lab, None, l) ->
          let x = next_var() in         (* todo: factorize next three lines of code *)
          let px = { ppat_loc = Location.none; ppat_desc = Ppat_var x } in (* todo: better hack to remember created var *)
          let vx = { pexp_loc = Location.none; pexp_desc = Pexp_ident (Lident x) } in
          let e' = return (Pexp_match (vx, l)) in
          aux named (return (Pexp_function (lab, None, [px,e'])))
          (* [function /branches/]  becomes  [fun x => match x with /branches/] *)
      | Pexp_function (p, Some _, l) -> 
         unsupported "function with optional expression"
      | Pexp_apply (e0, l) when is_failwith_function e0 -> 
         return Pexp_assertfalse, []
      | Pexp_apply (e0, l) ->
         let assign = assign_fct next_var in      
         let e0',b0 = aux false e0 in
         let ei',bi = List.split (List.map (fun (lk,ek) -> let ek',bk = aux false ek in (lk, ek'), bk) l) in
         let e' = return (Pexp_apply (e0', ei')) in
         let b' = (List.flatten bi) @ b0 in
         if is_inlined_primitive e0 l
            then e', b'
            else assign e' b'
      | Pexp_match (e0, l) -> 
         let assign = assign_fct next_var in      
         let e0',b0 = aux false e0 in
         let l' =
            let rec or_pats (p,e) = 
               match p.ppat_desc with
               | Ppat_or (p1,p2) -> or_pats (p1, e) @ or_pats (p2, e)
               | _ -> [(p,e)]
               in
            list_concat_map or_pats l in 
         let pat_vars = list_concat_map pattern_variables (List.map fst l') in
         let is_naming_required =
            list_intersect pat_vars (values_variables e0') <> [] in
         let e0',b0 =
            if not is_naming_required then e0',b0 else begin
              let x = next_var() in        
              let px = { ppat_loc = Location.none; ppat_desc = Ppat_var x } in 
              let vx = { pexp_loc = Location.none; pexp_desc = Pexp_ident (Lident x) } in
              vx, b0@[px,e0']       
            end in
         let e' = Pexp_match (e0', List.map protect_branch l') in
         assign (return e') b0
      | Pexp_try (e,l) -> unsupported "exceptions"
      | Pexp_tuple l -> 
         let l',bi = List.split (List.map (aux false) l) in
         return (Pexp_tuple l'), List.flatten bi
      | Pexp_construct (li, None, b) -> 
         return (Pexp_construct (li, None, b)), []
      | Pexp_construct (li, Some e, bh) -> 
         let e',b = aux false e in
         return (Pexp_construct (li, Some e', bh)), b
      | Pexp_variant (l,eo) -> unsupported "variants"
      | Pexp_record (l,Some eo) -> unsupported "record-with"
      | Pexp_record (l,None) -> 
         let l',bi = List.split (List.map (fun (i,(e,b)) -> ((i,e),b)) (assoc_list_map (aux false) l)) in
         return (Pexp_record (l', None)), List.flatten bi
      | Pexp_field (e,i) -> 
          let e',b = aux false e in
          return (Pexp_field (e', i)), b
      | Pexp_setfield (e,i,e2) -> 
          let e',b = aux false e in
          let e2',b2 = aux false e2 in
          return (Pexp_setfield (e', i, e2')), b2 @ b 
      | Pexp_array l -> 
         let l',bi = List.split (List.map (aux false) l) in
         return (Pexp_array l'), List.flatten bi
      | Pexp_ifthenelse (e1, e2, None) ->
          let e1', b = aux false e1 in
          return (Pexp_ifthenelse (e1', protect named e2, Some (return (Pexp_construct (Lident "()", None, false))))), b
      | Pexp_ifthenelse (e1, e2, Some e3) -> 
          let e1', b = aux false e1 in
          return (Pexp_ifthenelse (e1', protect named e2, Some (protect named e3))), b
             (* todo: à tester: if then else fun x -> x *)
      | Pexp_sequence (e1,e2) -> 
          let e1', b = aux true e1 in
          return (Pexp_sequence (e1', protect named e2)), b     
      | Pexp_while (e1,e2) -> 
         return (Pexp_while (protect named e1, protect named e2)), []      
      | Pexp_for (s,e1,e2,d,e3) -> 
          let e1', b1 = aux false e1 in
          let e2', b2 = aux false e2 in
          return (Pexp_for (s, e1', e2', d, protect named e3)), b1 @ b2
      | Pexp_constraint (e,to1,to2) -> 
         let e',b = aux named e in
         return (Pexp_constraint (e',to1,to2)), b
      | Pexp_when (econd,ebody) -> 
         let econd' = protect false econd in
         let ebody' = protect false ebody in
         return (Pexp_when (econd', ebody')), []
      | Pexp_send (_,_) -> unsupported "send expression"
      | Pexp_new _ -> unsupported "new expression"
      | Pexp_setinstvar (_,_) -> unsupported "set-inst-var expression"
      | Pexp_override _ -> unsupported "Pexp_override expression"
      | Pexp_letmodule (_,_,_) -> unsupported "let-module expression"
      | Pexp_assert e -> unsupported "assertions other than [assert false]"          
      | Pexp_assertfalse -> 
          return Pexp_assertfalse, []
      | Pexp_lazy e -> 
          let e',b = aux false e in
          return (Pexp_lazy e'), b
      | Pexp_poly (_,_) -> unsupported "poly expression"
      | Pexp_object _ -> unsupported "objects"
       
   and protect named e =
      let (e',b) = aux named e in
      create_let e.pexp_loc b e'

   and protect_branch (p,e) =
      (normalize_pattern p, protect true e)

   in 
   protect named e


let normalize_pattern_expression (p,e) =
   (normalize_pattern p, normalize_expression true e)


(*#########################################################################*)
(* Normalization of modules and top-level phrases *)

let rec normalize_module m =
   { m with pmod_desc = match m.pmod_desc with
   | Pmod_ident li -> Pmod_ident li
   | Pmod_structure s -> Pmod_structure (normalize_structure s)
   | Pmod_functor (s,mt,me) -> Pmod_functor (s, mt, normalize_module me)
   | Pmod_apply (me1,me2) -> Pmod_apply (normalize_module me1, normalize_module me2)
   | Pmod_constraint (me,mt) -> Pmod_constraint (normalize_module me,mt)
   }

and normalize_structure s =
  List.map normalize_structure_item s

and normalize_structure_item si =
   { si with pstr_desc = match si.pstr_desc with
   | Pstr_eval e -> Pstr_eval (normalize_expression true e)
   | Pstr_value (r,l) -> Pstr_value (r, List.map normalize_pattern_expression l)
   | Pstr_primitive (s,v) -> Pstr_primitive (s,v)
   | Pstr_type l -> Pstr_type l
   | Pstr_exception (s,e) -> Pstr_exception (s,e)
   | Pstr_exn_rebind (s,i) -> Pstr_exn_rebind (s,i)
   | Pstr_module (s,m) -> Pstr_module (s, normalize_module m)
   | Pstr_recmodule _ -> unsupported "recursive modules"
   | Pstr_modtype (s,mt) -> Pstr_modtype (s,mt)
   | Pstr_open li -> Pstr_open li
   | Pstr_class _ -> unsupported "objects"
   | Pstr_class_type _ -> unsupported "objects"
   | Pstr_include m -> Pstr_include (normalize_module m)
   }

and normalize_toplevel_phrase p =
  match p with
  | Ptop_def s -> Ptop_def (normalize_structure s)
  | Ptop_dir (s,d) -> Ptop_dir (s,d)

and normalize_source s =
   List.map normalize_toplevel_phrase s


(*#########################################################################*)

(*
let make_fresh_ident is_used basename =
   let rec trysuffix i =
      if i > 1000 then failwith "but in make_fresh_ident";
      let name = basename ^ (string_of_int i) in
      if is_used name 
          then trysuffix (i+1)
          else name
        in
   let name = trysuffix 0 in
   Ident.create name

let fresh_ident_pat is_used = make_fresh_ident is_used "_p"
let fresh_ident_fun is_used = make_fresh_ident is_used "_f"
let fresh_ident_loc is_used = make_fresh_ident is_used "_x"
*)
