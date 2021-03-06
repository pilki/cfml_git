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
open Path
open Printf

(*#########################################################################*)
(* ** Switch for generating formulae for purely-functional programs *)

let pure_mode = ref false

(*#########################################################################*)
(* ** Error messages *)

exception Not_in_normal_form of string

let not_in_normal_form s =
   raise (Not_in_normal_form s)


(*#########################################################################*)
(* ** Lifting of paths *)

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

(** Translates a path into a string. A module called "Test" 
    becomes "Test_ml" if it refers to a file, and it becomes
    "MLTest" if it refers to a functor argument. 
    --todo: call them all "Test_ml"? *)

let lift_full_path_name p =
  Path.name (lift_full_path p)

(** Translates a path into a string --todo: why not full? *)

let lift_path_name p =
  Path.name (lift_path p)

(** Convention for naming record types *)

let record_type_name name =
  "_" ^ name

(** Convention for naming record constructors *)

let record_constructor name =
  "_" ^ name ^ "_of"


(*#########################################################################*)
(* ** Lifting of types *)

(** Computes the free variables of a [btyp] *)

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

(** Translates a [btyp] into a Coq type *)

let rec lift_btyp t =
   let aux = lift_btyp in
   match t with
   | Btyp_val -> 
      val_type
   | Btyp_arrow (t1,t2) -> 
      val_type
   | Btyp_constr (id,[t]) when Path.name id = "ref" || Path.name id = "Pervasives.ref"  
      || Path.name id = "mlist" -> (* --todo: not needed anymore *)
      loc_type
   | Btyp_constr (id,[t]) when Path.name id = "array" || Path.name id = "Pervasives.array" -> 
      loc_type
   | Btyp_constr (id,[t]) when Path.name id = "heap" || Path.name id = "Heap.heap" -> (* todo generalize *)
      loc_type
   | Btyp_constr (id,[t]) when Path.same id Predef.path_lazy_t || Path.name id = "Lazy.t" -> 
      aux t  (* todo: les Lazy provenant des patterns ne sont pas identique � Predef.path_lazy_t *)
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

(** Translates a Caml type into a Coq type *)

let lift_typ_exp ty =
  lift_btyp (btyp_of_typ_exp ty)  

(** Translates a Caml type scheme into a Coq type *)

let lift_typ_sch ty =
   mark_loops ty;
   let t = btree_of_typexp true ty in
   let fv = fv_btyp~through_arrow:false t in
   fv, lift_btyp t

(** Translates the type of a Caml expression into a Coq type *)

let coq_typ e =
   lift_typ_exp (e.exp_type)

(** Translates the type of a Caml pattern into a Coq type *)

let coq_typ_pat p =
   lift_typ_exp (p.pat_type)

(** Extracts a record name from a type *)

let get_record_name_for_exp e = 
   let b = btyp_of_typ_exp (e.exp_type) in   
   match b with 
   | Btyp_constr (id,_) -> Path.name id
   | _ -> failwith "illegal argument for get_record_name_for_exp"



(*#########################################################################*)
(* ** Type arity functions *)

(** Get the number of type arguments of a (polymorphic) free variable *)

let typ_arity_var env x =
   match x with
   | Path.Pident id -> 
      begin try Ident.find_same id env
      with Not_found -> 0 end
   | _ -> 0

(** Get the number of type arguments of a (polymorphic) data constructor *)

let typ_arity_constr c =
   match (c.cstr_res).desc with
   | Tconstr (_,ts,_) -> List.length ts
   | _ -> failwith "typ_arity_constr: result type of constructor is not a type constructor"

(** Translate a Caml data constructor into a Coq expression *)

let coq_of_constructor c =
   let x = string_of_constructor c in
   match find_builtin_constructor x with
   | None -> coq_app_var_wilds x (typ_arity_constr c) 
   | Some y -> Coq_var y


(*#########################################################################*)
(* ** Lifting of patterns *)

(** Compute the free variables of a pattern *)

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

(** Translate a Caml pattern into a Coq expression, and
    ignores the aliases found in the pattern *)

let rec lift_pat ?(through_aliases=true) p : coq = 
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

(** Extracts the aliases from a Caml pattern, in the form of an
    association list mapping variables to Coq expressions *)

let pattern_aliases p : (typed_var*coq) list = 
   let rec aux p =
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
      in
   List.rev (aux p)


(*#########################################################################*)
(* ** Helper functions for primitive functions *)

let rec prefix_for_label typ = 
  match typ.desc with  
  | Tconstr (p, _, _) -> lift_path_name p 
  | Tlink t -> prefix_for_label t
  | _ -> failwith "string_of_label: type of a record should be a Tconstr or Tlink"
  (*
  | Tvar -> failwith "x1"
  | Tarrow _ -> failwith "x2"
  | Ttuple  _ -> failwith "x3"
  | Tconstr _ -> failwith "x4"
  | Tobject  _ -> failwith "x5"
  | Tfield _ -> failwith "x6"
  | Tnil _ -> failwith "x7"
  | Tsubst  _ -> failwith "x9"
  | Tvariant  _ -> failwith "x10"
  | Tunivar -> failwith "x11"
  | Tpoly  _ -> failwith "x12"
  *)

let string_of_label_with prefix lbl =
  prefix ^ "_" ^ lbl.lbl_name

let name_for_record_new prefix =
  "_new" ^ prefix

let name_for_record_get lbl =
  "_get_" ^ lbl.lbl_name

let name_for_record_set lbl =
  "_set_" ^ lbl.lbl_name

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


(*#########################################################################*)
(* ** Lifting of values *)

(** Translate a Caml identifier into a Coq identifier, possibly 
    applied to wildcards for taking type applications into account *)

let lift_exp_path env p =
   match find_primitive (Path.name p) with
   | None -> 
      let x = lift_path_name p in
      coq_app_var_wilds x (typ_arity_var env p)
   | Some y -> Coq_var y 

(** Translate a Caml value into a Coq value. Fails if the Coq 
    expression provided is not a value. *)

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
       let typ_args = 
          match btyp_of_typ_exp e.exp_type with
          | Btyp_constr (id,ts) -> List.map lift_btyp ts
          | _ -> failwith "record should have a type-constructor as type"
          in
       coq_apps (coq_var_at constr) (typ_args @ Array.to_list args)
   | Texp_apply (funct, oargs) when is_inlined_primitive funct oargs ->
      let f = get_inlined_primitive funct oargs in
      let args = simplify_apply_args oargs in
      coq_apps (Coq_var f) (List.map aux args)
   | Texp_lazy e -> 
      aux e
   | Texp_array [] -> 
      Coq_var "array_empty"
   | _ -> not_in_normal_form (Print_tast.string_of_expression false e)
   (* --todo: could be a value in a purely-functional setting
   | Texp_field (e, lbl) ->
       let typ = e.exp_type in
       Coq_app (Coq_var (string_of_label typ lbl), aux e) *)
   (* --later: other constructors
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
(* ** Helper functions for producing label names *)

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


(*#########################################################################*)
(* ** Helper functions for names *)

(** Takes a pattern that is expected to be reduced simply to an identifier, 
    and returns this identifier *)

let pattern_ident p =
   match p.pat_desc with
   | Tpat_var s -> s
   | _ -> failwith ("pattern_ident: the pattern is not a name: " ^ (Print_tast.string_of_pattern false p))

(** Takes a pattern that is expected to be reduced simply to an identifier, 
    and returns the name of this identifier *)

let pattern_name p =
   Ident.name (pattern_ident p)


(*#########################################################################*)
(* ** Characteristic formulae for expressions *)

(** Translate a Caml expression into its Coq characteristic formula *)

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
   (* TODO: only in purely function setting:   | Texp_record (lbl_expr_list, opt_init_expr) -> ret e*)

   | Texp_record (lbl_expr_list, opt_init_expr) ->
      if opt_init_expr <> None then unsupported "record-with"; (* TODO *)
      let name = get_record_name_for_exp e in
      let func = Coq_var (name_for_record_new ("_" ^ name)) in (* tood: move the underscore *)
      let args = List.map snd (list_ksort str_cmp (List.map (fun (li,ei) -> (li.lbl_name,ei)) lbl_expr_list)) in
      let tprod = coq_prod (List.map coq_typ args) in
      Cf_app ([tprod;loc_type], func, [Coq_tuple (List.map lift args)]) 

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
              (* --todo: add better support for local polymorphic recursion
              List.fold_left (fun (pat,bod) acc -> Ident.add (pattern_ident pat) 0 acc) env pat_expr_list *)
           | Default -> unsupported "Default recursion mode"
           in
        let ncs = List.map (fun (pat,bod) -> (pattern_name pat, cfg_func env' fvs pat bod)) pat_expr_list in
        let cf_body = cfg_exp env' body in 
        add_used_label (fst (List.hd ncs));
        Cf_letfunc (ncs, cf_body)
        (* --todo: check what happens with recursive types *)

      (* let-binding of a single value *)
      end else begin 
        if (List.length pat_expr_list <> 1) then not_normal();
        let (pat,bod) = List.hd pat_expr_list in
        let x = pattern_name pat in
           (* todo: une diff�rence entre pattern_name et pattern_ident utils� plus bas? *)
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
      (* old: Cf_caseif (aux cond, aux ifso, aux ifnot) *)
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
        | Downto -> unsupported "for-downto expressions" (* later *)
      end

   | Texp_array expr_list -> unsupported "array expressions" (* later *)

   | Texp_field (arg, lbl) -> 
      let tr = coq_typ e in 
      let ts = coq_typ arg in (* todo: check it is always 'loc' *)
      let func = Coq_var (name_for_record_get lbl) in
      Cf_app ([ts;tr], func, [lift arg]) 

   | Texp_setfield(arg, lbl, newval) -> 
      let ts1 = coq_typ arg in (* todo: check it is always 'loc' *)
      let ts2 = coq_typ newval in 
      let func = Coq_var (name_for_record_set lbl) in
      Cf_app ([ts1;ts2;coq_unit], func, [lift arg; lift newval]) 

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
   (* --todo: check if the set of type variables quantified is not too
      conservative. Indeed, some type variables may no longer occur. *)


(*#########################################################################*)
(* ** Characteristic formulae for modules *)

(** Helper functions to find out the kind of a type declaration *)

let is_algebraic (name,dec) =
   match dec.type_kind with Type_variant _ -> true | _ -> false 

let is_type_abbrev (name,dec) =
   match dec.type_kind with Type_abstract -> true | _ -> false 

let is_type_record (name,dec) =
   match dec.type_kind with Type_record _ -> true | _ -> false 

(** Generate the top-level Coq declarations associated with 
    a top-level declaration from a module. *)

let rec cfg_structure_item s : cftops = 
  match s with
  | Tstr_value(rf, fvs, pat_expr_list) ->
      reset_local_labels();

      (* --todo: improve code sharing between local bindings and top-level bindings *)
      let is_let_fun (pat,exp) = 
         match exp.exp_desc with
         | Texp_function (_,_) -> true
         | _ -> false in

      if List.for_all is_let_fun pat_expr_list then begin
        let env' = match rf with 
           | Nonrecursive -> Ident.empty
           | Recursive -> Ident.empty
               (* --todo: better support for polymorphic recursion
              List.fold_left (fun (pat,bod) acc -> Ident.add (pattern_ident pat) 0 acc) env pat_expr_list *)
           | Default -> unsupported "Default recursion mode"
           in
        let ncs = List.map (fun (pat,bod) -> (pattern_name pat, cfg_func env' fvs pat bod)) pat_expr_list in
          (List.map (fun (name,_) -> Cftop_val (name, val_type)) ncs)
        @ (List.map (fun (name,cf_body) -> Cftop_fun_cf (name, cf_body)) ncs)
        @ [Cftop_coqs (List.map (fun (name,_) -> Coqtop_registercf name) ncs)]
   
      (* let-binding of a single value *)
      end else if (List.length pat_expr_list = 1) then begin (* later: check it is not a function *)
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

        (* term let-binding -- later *)
        end else begin
            
           failwith "unsupported top-level binding of terms that are not values";

           (* if fvs_strict <> [] || fvs_others <> [] 
               then not_in_normal_form ("(unsatisfied value restriction) "
                                        ^ (Print_tast.string_of_expression false e));
           let cf1 = cfg_exp env bod in
           let env' = Ident.add (pattern_ident pat) (List.length fvs_strict) env in
           let cf2 = cfg_exp env' body in
           add_used_label x;
           Cf_let ((x,typ), cf1, cf2) *)

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

  (* -- todo: check no name clash occurs here *)
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

(** Generate the top-level Coq declarations associated with 
    a type abbreviation. *)

and cfg_type_abbrev (name,dec) =
   let x = Ident.name name in
   let args = List.map name_of_type dec.type_params in
   let sort = coq_impl_types (List.length args) in
   let coqs = match dec.type_manifest with
      | None -> [Coqtop_param (x, sort)]
      | Some t -> [Coqtop_def ((x, sort), coq_fun_types args (lift_typ_exp t));
                   Coqtop_hint_unfold ([x],"typeclass_instances") ] in
   coqs, [] 

(** Generate the top-level Coq declarations associated with 
    a record definition. *)

and cfg_type_record (name,dec) =
   let x = Ident.name name in
   let name_of_field lbl = 
      "_" ^ lbl in (* "_" ^ x ^ *)
   let record_name = record_type_name x in
   let fields = match dec.type_kind with Type_record (l,_) -> l | _ -> assert false in
   (* let fields_base_names = List.map (fun (lbl,_,_) -> lbl) fields in *)
   let declared_params = List.map name_of_type dec.type_params in
   let branches, branches_params = List.split (List.map (fun (lbl, mut, typ) -> 
      let btyp = btyp_of_typ_exp typ in 
      ((name_of_field lbl, lift_btyp btyp), fv_btyp ~through_arrow:false btyp)) fields) in
          (* todo: use a function to factorize above work *)

   let branches = list_ksort str_cmp branches in
   let fields_names, fields_types = List.split branches in
   (* let remaining_params = List.concat branches_params in *)
   (* todo: assert remaining_params included in declared_params *)
   (* TODO: enlever le polymorphisme inutile : list_intersect remaining_params declared_params *) 
   let params = declared_params in 
   let top = { 
      coqind_name = record_name;
      coqind_targs = coq_types params;
      coqind_ret = Coq_type;
      coqind_branches = branches } in
   let implicit_decl =
      match params with
      | [] -> []
      | _ -> List.map (fun field -> Coqtop_implicit (field, List.map (fun p -> p, Coqi_maximal) params)) fields_names 
      in
   let type_abbrev = Coqtop_def ((x,Coq_wild), coq_fun_types params loc_type) in
   [ type_abbrev ],
   [ Coqtop_record top ] 
   @ (implicit_decl)
   @ [ Coqtop_hint_constructors ([record_name], "typeclass_instances") ]
   @ record_functions record_name (record_name ^ "_of") (make_upper x) params fields_names fields_types
  (*  todo: move le "_of" *)

(** Auxiliary function to generate stuff for records *)

and record_functions record_name record_constr repr_name params fields_names fields_types =
   let nth i l = List.nth l i in
   let n = List.length fields_names in
   let indices = list_nat n in
   let for_indices f = List.map f indices in

   let new_name = name_for_record_new record_name in
   let get_names = for_indices (fun i -> "_get" ^ nth i fields_names) in
   let set_names = for_indices (fun i -> "_set" ^ nth i fields_names) in
   let new_decl = Coqtop_param (new_name, val_type) in
   let get_set_decl i =
      [ Coqtop_param (nth i get_names, val_type); 
        Coqtop_param (nth i set_names, val_type) ] in
   
   let logicals = List.map make_upper_2 fields_names (* for_indices (fun i -> sprintf "A%d" (i+1)) *) in
   let reprs = for_indices (fun i -> sprintf "T%d" (i+1)) in
   let abstracts = for_indices (fun i -> sprintf "X%d" (i+1)) in
   let concretes = for_indices (fun i -> sprintf "x%d" (i+1)) in
   let loc = "l" in

   let vparams = coq_vars params in
   let vlogicals = coq_vars logicals in
   let vreprs = coq_vars reprs in
   let vabstracts = coq_vars abstracts in
   let vconcretes = coq_vars concretes in
   let vloc = coq_var "l" in

   let tparams = coq_types params in
   let tlogicals = coq_types logicals in
   let treprs = List.map (fun i -> nth i reprs, htype (nth i vlogicals) (nth i fields_types)) indices in
   let tabstracts = List.map (fun i -> nth i abstracts, nth i vlogicals) indices in
   let tconcretes = List.map (fun i -> nth i concretes, nth i fields_types) indices in
   let tloc = (loc, loc_type) in

   let repr_args = tparams @ tlogicals @ treprs @ tabstracts @ [tloc] in
   let hcore = heap_is_single vloc (coq_apps (coq_var_at record_constr) (vparams @ vconcretes)) in
   let helems = heap_stars (for_indices (fun i -> hdata (nth i vconcretes) (Coq_app (nth i vreprs, nth i vabstracts)))) in
   let repr_body = heap_star hcore helems in
   let repr_def = coqtop_def_untyped repr_name (coq_funs repr_args (heap_existss tconcretes repr_body)) in

   let repr_folded = hdata vloc (coq_apps (coq_var_at repr_name) (vparams @ vlogicals @ vreprs @ vabstracts)) in
   let repr_unfolded = hdata vloc (coq_apps (coq_var_at repr_name) (vparams @ fields_types @ (list_make n id_repr) @ vconcretes)) in
   let repr_elems = helems in
   let repr_convert_body = coq_eq repr_folded (heap_existss tconcretes (heap_star repr_unfolded repr_elems)) in
   let repr_focus_body = heap_impl repr_folded (heap_existss tconcretes (heap_star repr_unfolded repr_elems)) in
   let repr_unfocus_body = heap_impl (heap_star repr_unfolded repr_elems) repr_folded in
   let repr_convert_quantif = [tloc] @ tparams @ tlogicals @ treprs @ tabstracts in
   let repr_focus_quantif = repr_convert_quantif in
   let repr_unfocus_quantif = [tloc] @ tparams @ tconcretes @ tlogicals @ treprs @ tabstracts in
   let convert_name = repr_name ^ "_convert" in
   let focus_name = repr_name ^ "_focus" in
   let unfocus_name = repr_name ^ "_unfocus" in
   let repr_convert = Coqtop_param (convert_name, coq_foralls repr_convert_quantif repr_convert_body) in
   let repr_focus = Coqtop_param (focus_name, coq_foralls repr_focus_quantif repr_focus_body) in
   let repr_unfocus = Coqtop_param (unfocus_name, coq_foralls repr_unfocus_quantif repr_unfocus_body) in 
   let repr_convert_focus_unfocus = [ repr_convert; repr_focus; repr_unfocus;
      coqtop_noimplicit convert_name; coqtop_noimplicit focus_name; coqtop_noimplicit unfocus_name ] in

   let new_spec =
      let r = "R" in
      let vr = coq_var r in
      let tr = (r, formula_type_of loc_type) in
      let x = "X" in
      let tx = (x, coq_prod fields_types) in
      let data_targs = vparams @ fields_types @ (for_indices (fun _ -> id_repr)) in
      let post = coq_funs [(loc, loc_type)] (hdata vloc (coq_apps (coq_var_at repr_name) (data_targs @ vabstracts))) in
      let body = coq_funs [tx; tr] (Coq_lettuple (coq_vars abstracts, Coq_var x, coq_apps vr [heap_empty; post])) in
      let spec = coq_foralls tparams (coq_apps (Coq_var "spec_1") [body; coq_var new_name]) in
      [ Coqtop_param (new_name ^ "_spec", spec); 
        Coqtop_registerspec new_name; ]
      in
   let get_set_spec i = 
      let get_name = nth i get_names in
      let set_name = nth i set_names in
      let r = "R" in
      let vr = coq_var r in
      let trget = (r, formula_type_of (nth i fields_types)) in
      let trset = (r, formula_type_of coq_unit) in
      let x' = sprintf "X%d'" i in
      let vx' = coq_var x' in
      let tx' = (x', nth i fields_types) in
      let selected_tlogicals = list_remove i tlogicals in
      let replaced_vlogicals = list_replace i (nth i fields_types) vlogicals in
      let replaced_vreprs = list_replace i id_repr vreprs in
      let selected_treprs = list_remove i treprs in
      let replaced_tabstracts = list_replace i (nth i abstracts, nth i fields_types) tabstracts in
      let update_vabstracts = list_replace i vx' vabstracts in
      let data_targs = vparams @ replaced_vlogicals @ replaced_vreprs in
      let data_initial = hdata vloc (coq_apps (coq_var_at repr_name) (data_targs @ vabstracts)) in
      let data_updated = hdata vloc (coq_apps (coq_var_at repr_name) (data_targs @ update_vabstracts)) in
      let post_get = coq_funs [("x", Coq_wild)] (heap_star (heap_pred (coq_eq (Coq_var "x") (nth i vabstracts))) data_initial) in
      let post_set = post_unit data_updated in
      let body_quantif = replaced_tabstracts @ selected_treprs in
      let body_get = coq_funs [tloc; trget] (coq_foralls body_quantif (coq_apps vr [data_initial; post_get])) in
      let body_set = coq_funs [tloc; tx'; trset] (coq_foralls body_quantif (coq_apps vr [data_initial; post_set])) in
      let spec_get = coq_foralls (tparams @ selected_tlogicals) (coq_apps (Coq_var "spec_1") [body_get; coq_var get_name]) in
      let spec_set = coq_foralls (tparams @ selected_tlogicals) (coq_apps (Coq_var "spec_2") [body_set; coq_var set_name]) in
      [ Coqtop_param (get_name ^ "_spec", spec_get); 
        Coqtop_registerspec get_name; 
        Coqtop_param (set_name ^ "_spec", spec_set);
        Coqtop_registerspec set_name; ]
      in

     [ new_decl ]
   @ (List.concat (List.map get_set_decl indices))
   @ [ repr_def ]
   @ repr_convert_focus_unfocus
   @ new_spec
   @ (List.concat (List.map get_set_spec indices))


(** Generate the top-level Coq declarations associated with 
    a algebraic data type definition. *)

and cfg_algebraic decls =
   (* -- todo: data constructor type arity may be reduced when types are erased *)
   (* -- todo: Caml types often clash with Caml program variables, since in Coq
         they get put in the same namespace *)
    let trans_ind (name,dec) =
      let x = Ident.name name in
      let branches = match dec.type_kind with Type_variant l -> l | _ -> assert false in
      let params = List.map name_of_type dec.type_params in
      let ret_typ = coq_apps (Coq_var x) (coq_vars params) in
      let get_typed_constructor (c,ts) =
         (c, coq_impls (List.map lift_typ_exp ts) ret_typ) in
      let coqind_decl = 
         if List.length decls = 1 then
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
   @ [ Coqtop_hint_constructors (List.map (fun i -> i.coqind_name) inds, "typeclass_instances") ],
   []

(** Generate the top-level Coq declarations associated with 
    a type definition. *)

and cfg_type_decls decls =
   let rec aux decls =
       if List.length decls = 1 && is_type_abbrev (List.hd decls)  
          then cfg_type_abbrev (List.hd decls)
       else if List.length decls = 1 && is_type_record (List.hd decls)  
          then cfg_type_record (List.hd decls)
       else if (List.for_all is_algebraic decls)  
          then cfg_algebraic decls
       else (* /todo/ very experimental support: simply break circularity *)
          let (a,b) = List.split (List.map aux (List.map (fun x -> [x]) decls)) in
          (List.concat a, List.concat b)
          (* unsupported "type definitions must be single abbreviations or mutually-recursive inductive definitions (mixing both is not supported in Coq)" *)
      in
   let (a,b) = aux decls in 
   a @ b

(** Generate the top-level Coq declarations associated with 
    the content of a module. *)

and cfg_structure s =
   reset_used_labels();
   let body = list_concat_map (fun si -> reset_names(); cfg_structure_item si) s in
   cfg_extract_labels() @ body

(** Generate the top-level Coq declarations associated with 
    a Caml signature definition. *)

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

(** Generate the top-level Coq declarations associated with 
    a top-level declaration from a signature. *)

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
         | Tmty_signature s -> 
            (*
            Printf.printf "%d\n" (List.length s);
             begin match List.hd s with
              | Tsig_value (id,vd) -> unsupported "u" 
              | Tsig_type (id, td, rs) -> unsupported "x" 
              | Tsig_module (id,mt,rs) ->   unsupported "y" 
              | Tsig_modtype (id,decl) ->   unsupported "z"  
              | Tsig_exception _ -> unsupported "exceptions"
              | Tsig_class _ -> unsupported "objects"
              | Tsig_cltype _ -> unsupported "objects"
              end;
             *) 
            unsupported "module constraint is not just a name (4) -- todo: should be supported"  
         | _ -> unsupported "module constraint is not just a name (2)"  
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
  | Tsig_exception _ -> [] (*unsupported "exceptions"*)
  | Tsig_class _ -> unsupported "objects"
  | Tsig_cltype _ -> unsupported "objects"

(** Generate the top-level Coq declarations associated with 
    a signature. Handles mutually-recursive type definitions
    for algebraic data types. *)

and cfg_signature s = 
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

(** Generate the top-level Coq declarations associated with 
    a Caml module. *)

and cfg_module id m =
   let id = lift_ident_name id in
   let rec aux bindings cast m =
      let return def =
         Coqtop_module (id, bindings, cast, def) in
      match m.mod_desc with
      | Tmod_ident p -> return (Mod_def_inline [lift_full_path_name p]), None
      | Tmod_structure str -> return Mod_def_declare, Some (cfg_structure str)
      | Tmod_functor (x, mt, m1) -> 
          let x = lift_ident_name x in
          if cast <> Mod_cast_free then unsupported "cast before arguments in module declaration";
          begin match mt with
          | Tmty_ident p -> aux (([x], Mod_typ_var (lift_full_path_name p))::bindings) cast m1
          | _ -> 
             (* hack for Dijkstra   Printf.printf "-->%s %s\n" (lift_ident_name x) id; Pident (Ident.create ("PqueueSig") *)
             if id = "MLDijkstra" && x = "MLPqueue" 
             then 
               aux (([x], Mod_typ_with_mod (Mod_typ_var "MLPqueueSig", "MLElement", "MLNextNode"))::bindings) cast m1
             else unsupported "functor with on-the-fly signature for its argument"
            
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
           | Tmty_signature s -> 
             unsupported "module constraint is not just a name (3) -- todo: should be supported"  
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
           | _ -> unsupported "module constraint is not just a name (1)"  
           end
      in
   let mod_dec, str_opt = aux [] Mod_cast_free m in
   match str_opt with
   | None -> [ Cftop_coqs [ mod_dec ] ]
   | Some str -> [ Cftop_coqs [ mod_dec ] ] @ str @ [ Cftop_coqs [ Coqtop_end id ] ]

(** Generate the top-level Coq declarations associated with 
    a Caml file. *)

let cfg_file str =
   [ Cftop_coqs [ Coqtop_set_implicit_args; Coqtop_require_import (if !pure_mode then "FuncPrim" else "CFPrim") ] ]
   @ cfg_structure str

