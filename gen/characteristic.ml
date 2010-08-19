open Misc
open Asttypes
open Types
open Typedtree
open Mytools
open Longident
open Print_tast
open Print_type
open Formula
open Coq
open Primitives

exception Not_in_normal_form of string

let not_in_normal_form s =
   raise (Not_in_normal_form s)

(*
Predef.type_lazy_t arg.exp_type
Tconstr(path_lazy_t, [t], ref Mnil)
*)

(* todo: check that primitive functions are not rebound locally ! *)

let pure_mode = ref false

(*#########################################################################*)
(* Lifting of paths *)

open Path

let lift_ident_name id =
   if Ident.persistent id  
      then Ident.name id ^ "_ml"
      else "ML" ^ Ident.name id 

let rec lift_full_path = function
  | Pident id -> Pident (Ident.create (lift_ident_name id))
  | Pdot(p, s, pos) -> Pdot(lift_full_path p, "ML" ^ s, pos) 
  | Papply(p1, p2) -> assert false 

let lift_path = function
  | Pident id -> Pident id
  | Pdot(p, s, pos) -> Pdot(lift_full_path p, s, pos) 
  | Papply(p1, p2) -> assert false 

let lift_path_name p =
  Path.name (lift_path p)

let lift_full_path_name p =
  Path.name (lift_full_path p)


(*#########################################################################*)
(* Lifting of types *)


let loc_type =
  Coq_var "CFHeaps.loc"

let rec fv_btyp ?(through_arrow = true) t =
   let aux = fv_btyp in
   match t with
   | Btyp_val -> []
   | Btyp_arrow (t1,t2) -> if through_arrow then aux t1 @ aux t2 else []
   | Btyp_constr (id,ts) -> list_concat_map aux ts
   | Btyp_tuple ts -> list_concat_map aux ts
   | Btyp_var (b,s) -> [s]
   | Btyp_poly (ss,t) -> unsupported "poly-types"
   | Btyp_alias (t,s) -> s :: aux t 

let rec lift_btyp t =
   let aux = lift_btyp in
   match t with
   | Btyp_val -> 
      val_type
   | Btyp_arrow (t1,t2) -> 
      val_type
   | Btyp_constr (id,[t]) when Path.name id = "ref" || Path.name id = "Pervasives.ref"  
      || Path.name id = "nref" || Path.name id = "MyLib.nref" 
      || Path.name id = "mlist" ->
      loc_type
   | Btyp_constr (id,[t]) when Path.name id = "array" || Path.name id = "Pervasives.array" -> 
      loc_type
   | Btyp_constr (id,[t]) when Path.name id = "heap" || Path.name id = "Heap.heap" -> (* todo generalize *)
      loc_type
   | Btyp_constr (id,[t]) when Path.same id Predef.path_lazy_t || Path.name id = "Lazy.t" -> 
      aux t  (* todo: les Lazy provenant des patterns ne sont pas identique à Predef.path_lazy_t *)
   | Btyp_constr (id,[t]) when Path.name id = "Stream.stream" || Path.name id = "stream" -> 
      Coq_app (Coq_var "list", aux t)
   | Btyp_constr (id,[t]) when Path.name id = "Stream.stream_cell" || Path.name id = "stream_cell" -> 
      Coq_app (Coq_var "list", aux t)
   | Btyp_constr (id,ts) -> 
      coq_apps (Coq_var (lift_path_name id)) (List.map aux ts)
   | Btyp_tuple ts -> 
      coq_prod (List.map aux ts)
   | Btyp_var (b,s) -> 
      if b then unsupported "non-generalizable free type variables (of the form '_a); please add a type annotation";
      Coq_var s
   | Btyp_poly (ss,t) -> 
      unsupported "poly-types"
   | Btyp_alias (t1,s) -> 
      let occ = fv_btyp ~through_arrow:false t1 in
      if List.mem s occ 
        then unsupported ("found a recursive type that is not erased by an arrow:" ^ (print_out_type t));
      aux t1 

let lift_typ_exp ty =
  lift_btyp (btyp_of_typ_exp ty)  

let lift_typ_sch ty =
   mark_loops ty;
   let t = btree_of_typexp true ty in
   let fv = fv_btyp~through_arrow:false t in
   fv, lift_btyp t

let coq_typ e =
   lift_typ_exp (e.exp_type)

let coq_typ_pat p =
   lift_typ_exp (p.pat_type)


(*#########################################################################*)
(* Arity functions *)

let typ_arity_constr c =
   match (c.cstr_res).desc with
   | Tconstr (_,ts,_) -> List.length ts
   | _ -> failwith "typ_arity_constr: result type of constructor is not a type constructor"

let typ_arity_var env x =
   match x with
   | Path.Pident id -> 
      begin try Ident.find_same id env
      with Not_found -> 0 end
   | _ -> 0

let coq_of_constructor c =
   let x = string_of_constructor c in
   match find_builtin_constructor x with
   | None -> coq_app_var_wilds x (typ_arity_constr c) 
   | Some y -> Coq_var y


(*#########################################################################*)
(* Lifting of patterns *)

let rec pattern_variables p : typed_vars = (* ignores aliases *)
   let aux = pattern_variables in
   match p.pat_desc with
   | Tpat_any -> not_in_normal_form "wildcard patterns remain after normalization"
   | Tpat_var s -> [Ident.name s, coq_typ_pat p]
   | Tpat_alias (p, s) -> aux p
   | Tpat_constant c -> []
   | Tpat_tuple l -> list_concat_map aux l
   | Tpat_construct (c, ps) -> list_concat_map aux ps
   | Tpat_lazy p1 -> aux p1
   | Tpat_variant (_,_,_) -> unsupported "variant patterns"
   | Tpat_record _ -> unsupported "record patterns"
   | Tpat_array pats -> unsupported "array patterns"
   | Tpat_or (_,p1,p2) -> unsupported "or patterns"

let rec lift_pat ?(through_aliases=true) p : coq = (* ignores aliases *)
   let aux = lift_pat ~through_aliases:through_aliases in
   match p.pat_desc with
   | Tpat_var s -> 
      Coq_var (Ident.name s)
   | Tpat_constant (Const_int n) -> 
      Coq_int n
   | Tpat_tuple l -> 
      Coq_tuple (List.map aux l)
   | Tpat_construct (c, ps) -> 
      coq_apps (coq_of_constructor c) (List.map aux ps)
   | Tpat_alias (p, s) -> 
      if through_aliases then aux p else Coq_var (Ident.name s)
   | Tpat_lazy p1 ->
      aux p1
   | Tpat_record _ -> unsupported "record patterns" (* todo! *)
   | Tpat_array pats -> unsupported "array patterns" (* todo! *)
   | Tpat_constant _ -> unsupported "only integer constant are supported"
   | Tpat_any -> not_in_normal_form "wildcard patterns remain after normalization"
   | Tpat_variant (_,_,_) -> unsupported "variant patterns"
   | Tpat_or (_,p1,p2) -> unsupported "or patterns in depth"

let rec pattern_aliases_rec p : (typed_var*coq) list = (* returns aliases *)
   let aux = pattern_aliases_rec in
   match p.pat_desc with
   | Tpat_var s -> []
   | Tpat_constant (Const_int n) -> []
   | Tpat_tuple l -> list_concat_map aux l
   | Tpat_construct (c, ps) -> list_concat_map aux ps
   | Tpat_alias (p1, s) -> 
      ((Ident.name s, coq_typ_pat p), lift_pat ~through_aliases:false p1) :: (aux p1)
   | Tpat_lazy p1 ->  aux p1
   | Tpat_record _ -> unsupported "record patterns" (* todo! *)
   | Tpat_array pats -> unsupported "array patterns" (* todo! *)
   | Tpat_constant _ -> unsupported "only integer constant are supported"
   | Tpat_any -> not_in_normal_form "wildcard patterns remain after normalization"
   | Tpat_variant (_,_,_) -> unsupported "variant patterns"
   | Tpat_or (_,p1,p2) -> unsupported "or patterns"   

let pattern_aliases p = 
   List.rev (pattern_aliases_rec p)



(*#########################################################################*)
(* Lifting of values *)

let prefix_for_label typ = 
  match typ.desc with  
  | Tconstr (p, _, _) -> lift_path_name p 
  | _ -> failwith "string_of_label: type of a record should be a Tconstr" 

let string_of_label_with prefix lbl =
  prefix ^ "_" ^ lbl.lbl_name

let string_of_label typ lbl =
  string_of_label_with (prefix_for_label typ) lbl

let simplify_apply_args oargs =
  List.map (function (Some e, Required) -> e | _ -> unsupported "optional arguments") oargs 

let get_inlined_primitive_option e oargs =
   let args = simplify_apply_args oargs in
    match e.exp_desc, args with 
    | Texp_ident (f,d), [n; {exp_desc = Texp_constant (Const_int m)}] 
        when m > 0 && let x = Path.name f in x = "Pervasives.mod" || x = "Pervasives./" -> 
        find_inlined_primitive (Path.name f) primitive_special
    | Texp_ident (f,d), _ -> 
        find_inlined_primitive (Path.name f) (List.length args)
    | _ -> None

let is_inlined_primitive e oargs =
   get_inlined_primitive_option e oargs <> None

let get_inlined_primitive e oargs =
   match get_inlined_primitive_option e oargs with
   | Some x -> x
   | _ -> failwith "get_inlined_primitive: not an inlined primitive"

let lift_exp_path env p =
   match find_primitive (Path.name p) with
   | None -> 
      let x = lift_path_name p in
      coq_app_var_wilds x (typ_arity_var env p)
   | Some y -> Coq_var y 

let rec lift_val env e = 
   let aux = lift_val env in
   match e.exp_desc with
   | Texp_ident (p,d) -> lift_exp_path env p 
   | Texp_constant (Const_int n) ->
      Coq_int n
   | Texp_constant _ -> 
      unsupported "only integer constant are supported"
   | Texp_tuple el -> 
      Coq_tuple (List.map aux el)
   | Texp_construct (c, es) ->
      coq_apps (coq_of_constructor c) (List.map aux es)
   | Texp_record (l, opt_init_expr) ->  
       if opt_init_expr <> None then unsupported "record-with expression"; (* todo *)
       if List.length l < 1 then failwith "record should have at least one field";
       let labels = (fst (List.hd l)).lbl_all in
       let args = Array.make (Array.length labels) (Coq_var "dummy") in
       let register_arg lbl v =
          Array.iteri (fun i lbli -> if lbl.lbl_name = lbli.lbl_name then args.(i) <- v) labels in
       List.iter (fun (lbl,v) -> register_arg lbl (aux v)) l;
       let constr = record_constructor (prefix_for_label (e.exp_type)) in
       coq_apps (Coq_var constr) (Array.to_list args)
       (*bin: Coq_record(List.map (fun (n,v) -> (string_of_label typ n, aux v)) l)*)
   
   (* not a value in imperative ! 
   | Texp_field (e, lbl) ->
       let typ = e.exp_type in
       Coq_app (Coq_var (string_of_label typ lbl), aux e)
   *)
   | Texp_apply (funct, oargs) when is_inlined_primitive funct oargs ->
      let f = get_inlined_primitive funct oargs in
      let args = simplify_apply_args oargs in
      coq_apps (Coq_var f) (List.map aux args)
   | Texp_lazy e -> 
      aux e
   | Texp_array [] -> 
      Coq_var "array_empty"
   | _ -> not_in_normal_form (Print_tast.string_of_expression false e)

   (*
   | Texp_assertfalse -> Texp_assertfalse
   | Texp_try(body, pat_expr_list) -> unsupported "try expression"
   | Texp_variant(l, arg) ->  unsupported "variant expression"
   | Texp_setfield(arg, lbl, newval) -> unsupported "set-field expression"
   | Texp_array expr_list -> unsupported "array expressions"
   | Texp_ifthenelse(cond, ifso, None) -> unsupported "if-then-without-else expressions"
   | Texp_sequence(expr1, expr2) -> unsupported "sequence expressions"
   | Texp_while(cond, body) -> unsupported "while expressions"
   | Texp_for(param, low, high, dir, body) -> unsupported "for expressions"
   | Texp_when(cond, body) -> unsupported "when expressions"
   | Texp_send(expr, met) -> unsupported "send expressions"
   | Texp_new (cl, _) -> unsupported "new expressions"
   | Texp_instvar(path_self, path) -> unsupported "inst-var expressions"
   | Texp_setinstvar(path_self, path, expr) -> unsupported "set-inst-var expressions"
   | Texp_override(path_self, modifs) -> unsupported "override expressions"
   | Texp_letmodule(id, modl, body) -> unsupported "let-module expressions"
   | Texp_assert (cond) -> unsupported "assert expressions"
   | Texp_object (cs, cty, meths) -> unsupported "object expressions"
   *)


(*#########################################################################*)
(* Characteristic formulae for expressions *)

let pattern_ident p =
   match p.pat_desc with
   | Tpat_var s -> s
   | _ -> failwith ("pattern_ident: the pattern is not a name: " ^ (Print_tast.string_of_pattern false p))

let pattern_name p =
   Ident.name (pattern_ident p)

let counter_local_label = 
   ref 0
let get_next_local_label () = 
   incr counter_local_label;
   "_m" ^ (string_of_int !counter_local_label)
let reset_local_labels() = 
   counter_local_label := 0

let used_labels : (var list) ref = 
   ref []
let reset_used_labels () =
   used_labels := []
let add_used_label x =
   if not (List.mem x !used_labels)
      then used_labels := x :: !used_labels

let cfg_extract_labels () =
   let labs = List.rev !used_labels in
   let cft = [ Cftop_coqs (list_mapi (fun i x -> Coqtop_label (x,i+1)) labs) ] in
   reset_used_labels();
   cft

let rec cfg_exp env e =
   let aux = cfg_exp env in
   let lift e = lift_val env e in
   let ret e = Cf_ret (lift e) in
   let not_normal () =
      not_in_normal_form (Print_tast.string_of_expression false e) in
   match e.exp_desc with
   | Texp_ident (x,d) -> ret e
   | Texp_constant cst -> ret e
   | Texp_tuple el -> ret e
   | Texp_construct(cstr, args) -> ret e
   | Texp_record (lbl_expr_list, opt_init_expr) -> ret e
   (*| Texp_field (arg, lbl) -> ret e*)
   | Texp_apply (funct, oargs) when is_inlined_primitive funct oargs -> ret e

   | Texp_function (pat_expr_list, partial) -> not_normal ()

   | Texp_let(rf, fvs, pat_expr_list, body) ->
      
      let is_let_fun = 
         match (snd (List.hd pat_expr_list)).exp_desc with
         | Texp_function (_,_) -> true
         | _ -> false in

      (* binding of functions, possibly mutually-recursive *)
      if is_let_fun then begin
        let env' = match rf with 
           | Nonrecursive -> env
           | Recursive -> env
               (* TODO: gérer la récursion polymorphe 
              List.fold_left (fun (pat,bod) acc -> Ident.add (pattern_ident pat) 0 acc) env pat_expr_list *)
           | Default -> unsupported "Default recursion mode"
           in
        let ncs = List.map (fun (pat,bod) -> (pattern_name pat, cfg_func env' fvs pat bod)) pat_expr_list in
        let cf_body = cfg_exp env' body in (* TODO: gérer la récursion polymorphe *)
        add_used_label (fst (List.hd ncs));
        Cf_letfunc (ncs, cf_body)
        (* TODO: bug avec les types récursifs genre ceux "fixpoint". pour l'instant, on hack avec val *)

      (* let-binding of a single value *)
      end else begin 
        if (List.length pat_expr_list <> 1) then not_normal();
        let (pat,bod) = List.hd pat_expr_list in
        let x = pattern_name pat in
           (* todo: une différence entre pattern_name et pattern_ident utilsé plus bas? *)
        let fvs_typ, typ = lift_typ_sch pat.pat_type in
        let fvs = List.map name_of_type fvs in
        let fvs_strict = list_intersect fvs fvs_typ in
        let fvs_others = list_minus fvs fvs_strict in
            
        (* pure-mode let-binding *)
        if !pure_mode then begin 
       
           let cf1 = cfg_exp env bod in
           let env' = Ident.add (pattern_ident pat) (List.length fvs_strict) env in
           let cf2 = cfg_exp env' body in
           add_used_label x;
           Cf_letpure (x, fvs_strict, fvs_others, typ, cf1, cf2)

        (* value let-binding *)
        end else if Typecore.is_nonexpansive bod then begin 

           let v = 
             try lift_val env bod  
             with Not_in_normal_form s -> 
                raise (Not_in_normal_form (s ^ " (only value can satisfy the value restriction)"))
             in
           let env' = Ident.add (pattern_ident pat) (List.length fvs_strict) env in
           let cf = cfg_exp env' body in
           add_used_label x;
           Cf_letval (x, fvs_strict, fvs_others, typ, v, cf)

        (* term let-binding *)
        end else begin
            
           if fvs_strict <> [] || fvs_others <> [] 
               then not_in_normal_form ("(unsatisfied value restriction) "
                                        ^ (Print_tast.string_of_expression false e));
           let cf1 = cfg_exp env bod in
           let env' = Ident.add (pattern_ident pat) (List.length fvs_strict) env in
           let cf2 = cfg_exp env' body in
           add_used_label x;
           Cf_let ((x,typ), cf1, cf2)

        end
      end

   | Texp_ifthenelse (cond, ifso, Some ifnot) ->
       Cf_caseif (lift cond, aux ifso, aux ifnot)

   | Texp_apply (funct, oargs) ->
      let args = simplify_apply_args oargs in
      let tr = coq_typ e in
      let ts = List.map coq_typ args in
      Cf_app (ts@[tr], lift funct, List.map lift args) 

   | Texp_match (arg, pat_expr_list, partial) ->
      let tested = lift arg in
      let conclu = match partial with Partial -> Cf_fail | Total -> Cf_done in
      let cfg_case (pat,body) acc =
         let whenopt, cfbody =  
            match body.exp_desc with 
            | Texp_when (econd, ebody) ->
                let w = 
                   try lift_val env econd  
                   with Not_in_normal_form s -> 
                      raise (Not_in_normal_form (s ^ " (Only total expressions are allowed in when clauses)"))
                   in
                Some w, aux ebody
            | _ -> None, aux body
            in
         Cf_case (tested, pattern_variables pat, lift_pat pat, whenopt, pattern_aliases pat, cfbody, acc) in
      let label = get_next_local_label() in
      add_used_label label;
      Cf_match (label, List.length pat_expr_list, List.fold_right cfg_case pat_expr_list conclu)

   | Texp_assertfalse -> 
      Cf_fail

   | Texp_lazy e -> 
      aux e

   | Texp_sequence(expr1, expr2) -> 
      Cf_seq (aux expr1, aux expr2)

   | Texp_while(cond, body) -> 
      Cf_while (aux cond, aux body)

   | Texp_for(param, low, high, dir, body) -> 
      begin match dir with 
        | Upto -> Cf_for (Ident.name param, lift low, lift high, aux body)
        | Downto -> unsupported "for-downto expressions" (* todo *)
      end

   | Texp_array expr_list -> unsupported "array expressions" (* todo *)

   | Texp_field (e, lbl) -> unsupported "field expression"
       (*let typ = e.exp_type in
       Coq_app (Coq_var (string_of_label typ lbl), aux e)*)

   | Texp_setfield(arg, lbl, newval) -> unsupported "set-field expression"

   | Texp_try(body, pat_expr_list) -> unsupported "try expression"
   | Texp_variant(l, arg) ->  unsupported "variant expression"
   | Texp_ifthenelse(cond, ifso, None) -> unsupported "if-then-without-else expressions should have been normalized"
   | Texp_when(cond, body) -> unsupported "when expressions outside of pattern matching"
   | Texp_send(expr, met) -> unsupported "send expressions"
   | Texp_new (cl, _) -> unsupported "new expressions"
   | Texp_instvar(path_self, path) -> unsupported "inst-var expressions"
   | Texp_setinstvar(path_self, path, expr) -> unsupported "set-inst-var expressions"
   | Texp_override(path_self, modifs) -> unsupported "override expressions"
   | Texp_letmodule(id, modl, body) -> unsupported "let-module expressions"
   | Texp_assert (cond) -> unsupported "assert expressions"
   | Texp_object (cs, cty, meths) -> unsupported "object expressions"

and cfg_func env fvs pat bod =
   let rec get_typed_args acc e =
      match e.exp_desc with
      | Texp_function ([p1,e1],partial) ->
         if partial <> Total 
            then not_in_normal_form (Print_tast.string_of_expression false e);
         get_typed_args ((pattern_name p1, coq_typ_pat p1)::acc) e1
      | _ -> List.rev acc, e
      in  
   let f = pattern_name pat in
   let targs, body = get_typed_args [] bod in
   let cf_body = cfg_exp env body in
   let fvs = List.map name_of_type fvs in
   Cf_body (f, fvs, targs, cf_body) 
   (* TODO: c'est peut être un peu trop conservatif sur les let-rec:
      on va sans-doute quantifier trop de variables de type; que faire? *)



(*#########################################################################*)
(* Characteristic formulae for modules *)

 let is_algebraic (name,dec) =
    match dec.type_kind with Type_variant _ -> true | _ -> false 
 let is_type_abbrev (name,dec) =
    match dec.type_kind with Type_abstract -> true | _ -> false 
 let is_type_record (name,dec) =
    match dec.type_kind with Type_record _ -> true | _ -> false 

let typ_of ty = lift_typ_exp ty

let rec cfg_structure_item s : cftops = 
  match s with
  | Tstr_value(rf, fvs, pat_expr_list) ->
      reset_local_labels();

      (* TODO: factorize with let in expression *)
      let is_let_fun (pat,exp) = 
         match exp.exp_desc with
         | Texp_function (_,_) -> true
         | _ -> false in

      if List.for_all is_let_fun pat_expr_list then begin
        let env' = match rf with 
           | Nonrecursive -> Ident.empty
           | Recursive -> Ident.empty
               (* TODO: gérer la récursion polymorphe 
              List.fold_left (fun (pat,bod) acc -> Ident.add (pattern_ident pat) 0 acc) env pat_expr_list *)
           | Default -> unsupported "Default recursion mode"
           in
        let ncs = List.map (fun (pat,bod) -> (pattern_name pat, cfg_func env' fvs pat bod)) pat_expr_list in
          (List.map (fun (name,_) -> Cftop_val (name, val_type)) ncs)
        @ (List.map (fun (name,cf_body) -> Cftop_fun_cf (name, cf_body)) ncs)
        @ [Cftop_coqs (List.map (fun (name,_) -> Coqtop_registercf name) ncs)]
   
      (* let-binding of a single value *)
      end else if (List.length pat_expr_list = 1) then begin  (* todo: check it is not a function *)
        (* todo:  avoid copy paste of this block with treatment of expressions *) 
        let (pat,bod) = List.hd pat_expr_list in
        let x = pattern_name pat in
        if (skip_cf_for x) then [] else begin
        let fvs_typ, typ = lift_typ_sch pat.pat_type in
        let fvs = List.map name_of_type fvs in
        let fvs_strict = list_intersect fvs fvs_typ in
        let fvs_others = list_minus fvs fvs_strict in
        
        (* pure-mode let-binding *)
        if !pure_mode then begin 

           let cf_body = cfg_exp (Ident.empty) bod in
           let implicits = 
              match fvs_strict with
              | [] -> []
              | _ ->  [ Coqtop_implicit (x, List.map (fun t -> (t,Coqi_maximal)) fvs_strict) ]
              in
           [ Cftop_val (x, coq_forall_types fvs_strict typ);
             Cftop_coqs implicits;
             Cftop_pure_cf (x, fvs_strict, fvs_others, cf_body); 
             Cftop_coqs [Coqtop_registercf x]; ] 

        (* value let-binding *)
        end else if Typecore.is_nonexpansive bod then begin 

           let v = 
             try lift_val (Ident.empty) bod  
             with Not_in_normal_form s -> 
                raise (Not_in_normal_form (s ^ " (only value can satisfy the value restriction)"))
            in
           let implicits = 
              match fvs_strict with
              | [] -> []
              | _ ->  [ Coqtop_implicit (x, List.map (fun t -> (t,Coqi_maximal)) fvs_strict) ]
              in
           [ Cftop_val (x, coq_forall_types fvs_strict typ);
             Cftop_coqs implicits;
             Cftop_val_cf (x, fvs_strict, fvs_others, v); 
             Cftop_coqs [Coqtop_registercf x]; ] 

        (* term let-binding *)
        end else begin
            
           failwith "unsupported top-level binding of terms that are not values";
           (*
           if fvs_strict <> [] || fvs_others <> [] 
               then not_in_normal_form ("(unsatisfied value restriction) "
                                        ^ (Print_tast.string_of_expression false e));
           let cf1 = cfg_exp env bod in
           let env' = Ident.add (pattern_ident pat) (List.length fvs_strict) env in
           let cf2 = cfg_exp env' body in
           add_used_label x;
           Cf_let ((x,typ), cf1, cf2)
           *)

        end

      end (* for skip_cf *)

     end else
        unsupported ("mutually-recursive values that are not all functions");


  | Tstr_type(decls) -> [ Cftop_coqs (cfg_type_decls decls) ]

  | Tstr_module(id, modl) -> cfg_module id modl 

  | Tstr_modtype(id, decl) -> cfg_modtype id decl

  | Tstr_open path -> 
      if is_primitive_module (Path.name path) then [] else
      [ Cftop_coqs [ Coqtop_require_import (lift_full_path_name path) ] ]

  (* todo: check actually a primitive, sinon conflicts... *)
  | Tstr_primitive(id, descr) ->
      [] 
  | Tstr_exception(id, decl) ->
      [] (* unsupported "exceptions" *)
  | Tstr_exn_rebind(id, path) -> 
      [] (* unsupported "exceptions" *)

  | Tstr_recmodule bindings -> unsupported "recursive modules"
  | Tstr_class cl_list -> unsupported "objects"
  | Tstr_cltype cl_list -> unsupported "objects"
  | Tstr_include(modl, ids) -> unsupported "module-include"
  | Tstr_eval expr -> unsupported "top level eval expression (let _)"

and cfg_type_abbrev (name,dec) =
   let x = Ident.name name in
   let args = List.map name_of_type dec.type_params in
   let sort = coq_impl_types (List.length args) in
   let coqs = match dec.type_manifest with
      | None -> [Coqtop_param (x, sort)]
      | Some t -> [Coqtop_def ((x, sort), coq_fun_types args (typ_of t));
                   Coqtop_hint_unfold ([x],"typeclass_instances") ] in
   coqs 

and cfg_type_record (name,dec) =
   let x = Ident.name name in
   let field lbl = 
      x ^ "_" ^ lbl in
   let branches = match dec.type_kind with Type_record (l,_) -> l | _ -> assert false in
   let params = List.map name_of_type dec.type_params in
   let top = { 
      coqind_name = x;
      coqind_targs = coq_types params;
      coqind_ret = Coq_type;
      coqind_branches = List.map (fun (lbl, mut, typ) -> (field lbl, typ_of typ)) branches } in
   let implicit_decl =
      match params with
      | [] -> []
      | _ -> List.map (fun (lbl,_,_) -> Coqtop_implicit (field lbl, List.map (fun p -> p, Coqi_maximal) params)) branches 
      in
   [ Coqtop_record top ] 
   @ (implicit_decl)
   @ [ Coqtop_hint_constructors ([x], "typeclass_instances") ]


and cfg_algebraic decls =
   (* todo: pb si des variables polymorphes correspondent à des trucs tous remplacés par Val;
      il faudrait en fait modifier l'arité des constructeurs, y compris lorsqu'on les applique *)
   (* todo: uppercase types *)
    let trans_ind (name,dec) =
      let x = Ident.name name in
      let branches = match dec.type_kind with Type_variant l -> l | _ -> assert false in
      let params = List.map name_of_type dec.type_params in
      let ret_typ = coq_apps (Coq_var x) (coq_vars params) in
      let get_typed_constructor (c,ts) =
         (c, coq_impls (List.map typ_of ts) ret_typ) in
      let coqind_decl = 
         if List.length decls = 1 then (* todo: tester aussi récursion non polymorphe ! *)
            {  coqind_name = x;
               coqind_targs = coq_types params;
               coqind_ret = Coq_type;
               coqind_branches = List.map get_typed_constructor branches; } 
          else
            {  coqind_name = x;
               coqind_targs = [];
               coqind_ret = coq_impl_types (List.length params); 
               coqind_branches = List.map 
                  (fun tc -> let (c,t) = get_typed_constructor tc in
                             (c, coq_foralls (coq_types params) t)
                     ) branches; } 
          in
      let implicit_decl =
         match params with
         | [] -> []
         | _ -> List.map (fun (cname,_) -> Coqtop_implicit (cname, List.map (fun p -> p,Coqi_maximal) params)) branches 
         in
      (coqind_decl, implicit_decl)
      in
   let inds,maxiss = List.split (List.map trans_ind decls) in
     [ Coqtop_ind inds ] 
   @ (List.concat maxiss)
   @ [ Coqtop_hint_constructors (List.map (fun i -> i.coqind_name) inds, "typeclass_instances") ]

and cfg_type_decls decls =
    if List.length decls = 1 && is_type_abbrev (List.hd decls)  
       then cfg_type_abbrev (List.hd decls)
    else if List.length decls = 1 && is_type_record (List.hd decls)  
       then cfg_type_record (List.hd decls)
    else if (List.for_all is_algebraic decls)  
       then cfg_algebraic decls
    else
       unsupported "type definitions must be single abbreviations or mutually-recursive inductive definitions (mixing both is not supported in Coq)"


and cfg_structure s =
   reset_used_labels();
   let body = list_concat_map (fun si -> reset_names(); cfg_structure_item si) s in
   cfg_extract_labels() @ body

and cfg_modtype id mt =
   let id = lift_ident_name id in
   let rec aux (bindings:mod_bindings) mt =
      match mt with
      | Tmty_ident p -> Coqtop_module_type (id, bindings, Mod_def_inline [lift_full_path_name p]), None
      | Tmty_signature s -> Coqtop_module_type (id, bindings, Mod_def_declare), Some (cfg_signature s)
      | Tmty_functor (x,mtx,mtr) -> 
          match mtx with
          | Tmty_ident p -> aux (([lift_ident_name x], Mod_typ_var (lift_full_path_name p))::bindings) mtr
          | _ -> unsupported "functor with on-the-fly signature for its argument"
      in
   let mod_typ_dec, sign_opt = aux [] mt in
   match sign_opt with
   | None -> [ Cftop_coqs [ mod_typ_dec ] ]
   | Some sign -> [ Cftop_coqs ( [mod_typ_dec] @ sign @ [Coqtop_end id] ) ]


and cfg_signature_item s =
  match s with

  | Tsig_value (id,vd) -> 
     if vd.val_kind <> Val_reg then unsupported "value in signature which is not a regular value";
     let fv, typ = lift_typ_sch vd.val_type in
     let x = Ident.name id in
     let implicit_decl =
         match fv with
         | [] -> []
         | _ -> [ Coqtop_implicit (x, List.map (fun p -> p, Coqi_maximal) fv) ]
         in
     [Coqtop_param (x, coq_forall_types fv typ)] @ implicit_decl

  | Tsig_type (id, td, rs) -> failwith "should have been treated before"
      (* -- old
      if rs <> Trec_not then unsupported "recursive type definitions in signatures"; 

      begin match td.type_kind with
      | Type_abstract -> cfg_type_abbrev (id,td)
      | Type_variant _ -> cfg_algebraic [id,td]
      | Type_record _ -> unsupported "record types"
      end
      *)

  | Tsig_module (id,mt,rs) ->
      if rs <> Trec_not then unsupported "recursive modules";
      let x = lift_ident_name id in
      let mt' =
         match mt with
         | Tmty_ident p -> Mod_typ_var (lift_full_path_name p)
         | _ -> unsupported "module constraint is not just a name"  
         in
      [Coqtop_declare_module (x, mt')] 

  | Tsig_modtype (id,decl) -> 
      unsupported "module types declared in module signatures"
      (*
      begin match decl with 
      | Tmodtype_abstract -> unsupported "abstract module types"
      | Tmodtype_manifest mt -> cfg_modtype id mt
      end
      *)
  | Tsig_exception _ -> unsupported "exceptions"
  | Tsig_class _ -> unsupported "objects"
  | Tsig_cltype _ -> unsupported "objects"


and cfg_signature s = 
(* --old   list_concat_map cfg_signature_item s  *)
   match s with
   | [] -> []
   | Tsig_type (id, td, Trec_first) :: s0 ->
       let rec find_group acc s' =
          match s' with
          | Tsig_type (id', td', Trec_next) :: s0' ->
             find_group ((id',td')::acc) s0'
          | _ -> List.rev acc, s'
          in
       let decls,s' = find_group [(id,td)] s0 in
       cfg_type_decls decls @ cfg_signature s'
   | si :: s' -> let si1 = cfg_signature_item si in
                 si1 @ cfg_signature s'

and cfg_module id m =
   let id = lift_ident_name id in
   let rec aux bindings cast m =
      let return def =
         Coqtop_module (id, bindings, cast, def) in
      match m.mod_desc with
      | Tmod_ident p -> return (Mod_def_inline [lift_full_path_name p]), None
      | Tmod_structure str -> return Mod_def_declare, Some (cfg_structure str)
      | Tmod_functor (x, mt, m1) -> 
          if cast <> Mod_cast_free then unsupported "cast before arguments in module declaration";
          begin match mt with
          | Tmty_ident p -> aux (([lift_ident_name x], Mod_typ_var (lift_full_path_name p))::bindings) cast m1
          | _ -> unsupported "functor with on-the-fly signature for its argument"
          end
      | Tmod_apply (m1, m2, coercion) ->
          let rec get_apps acc m0 =
             match m0.mod_desc with
             | Tmod_ident p -> lift_full_path_name p :: List.rev acc
             | Tmod_apply (m1, m2, coercion) -> 
                 begin match m2.mod_desc with
                 | Tmod_ident p -> get_apps (lift_full_path_name p :: acc) m1
                 | _ -> unsupported "module application can only be made between module paths"
                 end
             | _ -> unsupported "module application can only be made between module paths"
             in
          return (Mod_def_inline (get_apps [] m)), None
      | Tmod_constraint(m1, mt, coercion) ->
           begin match mt with
           | Tmty_ident p -> aux bindings (Mod_cast_super (Mod_typ_var (lift_full_path_name p))) m1
           | Tmty_signature s -> unsupported "module constraint is not just a name  -- todo: should be supported"  
             (*Printf.printf "%d\n" (List.length s);
             begin match List.hd s with
              | Tsig_value (id,vd) -> unsupported "u" 
              | Tsig_type (id, td, rs) -> unsupported "x" 
              | Tsig_module (id,mt,rs) ->   unsupported "y" 
              | Tsig_modtype (id,decl) ->   unsupported "z"  
              | Tsig_exception _ -> unsupported "exceptions"
              | Tsig_class _ -> unsupported "objects"
              | Tsig_cltype _ -> unsupported "objects"
              end
              *)
           | _ -> unsupported "module constraint is not just a name"  
           end
      in
   let mod_dec, str_opt = aux [] Mod_cast_free m in
   match str_opt with
   | None -> [ Cftop_coqs [ mod_dec ] ]
   | Some str -> [ Cftop_coqs [ mod_dec ] ] @ str @ [ Cftop_coqs [ Coqtop_end id ] ]


let cfg_file str =
   [ Cftop_coqs [ Coqtop_set_implicit_args; Coqtop_require_import (if !pure_mode then "FuncPrim" else "CFPrim") ] ]
   @ cfg_structure str

(*#########################################################################*)
(* BIN

let btyp_of_typ_exp t =
let btyp_of_typ_sch t =


let btyp_of_typ_exp t =
   mark_loops t;
   btree_of_typexp false t

let btyp_of_typ_sch t =
   mark_loops t;
   let typ = btree_of_typexp true t;
   let fvt = extract_occured () in
   let fvtg = List.concat (List.map (function Occ_gen x -> [x] | _ -> []) fvt) in
   let fvta = List.concat (List.map (function Occ_alias x -> [x] | _ -> []) fvt) in
   (fvtg, fvta, typ)


   
      end else if is_one_record then begin
         let d = match l with [(s,d)] -> d | _ -> assert false in
         let branches = match d.atypdec_descr with Atypdescr_record bs -> bs | _ -> assert false in
         let trans_branch (c, mutable_flag, t) =
            (c, lift_typ t)
            in
         let ind = { 
               coqind_name = d.atypdec_name;
               coqind_args = List.map (fun x -> (x, coq_type)) d.atypdec_params;
               coqind_ret = coq_type;
               coqind_branches = List.map trans_branch branches; } in
         let maxis = List.map (fun (c,_,_) -> Coqtop_maximal (c, d.atypdec_params)) branches in
         [ Cft_coqs ([ Coqtop_record ind ] @ maxis) ] 
         
*)
