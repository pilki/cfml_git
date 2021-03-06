open Format
open Mytools

(** This file contains facilities for representing and printing Coq
    expressions. Most of the core language is supported. A subset
    of the top-level declarations are supported. *)

(*#########################################################################*)
(* ** Syntax of Coq expressions *)

(** Coq variables and paths *)

type var = string
and vars = var list

and typed_var = var * coq
and typed_vars = typed_var list

and coq_path =
  | Coqp_var of var
  | Coqp_dot of coq_path * string

(** Coq expressions *)

and coq =
  | Coq_var of var
  | Coq_int of int
  | Coq_app of coq * coq 
  | Coq_impl of coq * coq 
  | Coq_lettuple of coqs * coq * coq
  | Coq_forall of typed_var * coq
  | Coq_fun of typed_var * coq
  | Coq_wild 
  | Coq_prop
  | Coq_type
  | Coq_tuple of coqs
  | Coq_record of (var * coq) list 
  | Coq_tag of string * string option * coq

and coqs = coq list

(** Toplevel declarations *)

type coqtop =
  | Coqtop_def of typed_var * coq
  | Coqtop_param of typed_var
  | Coqtop_instance of typed_var * bool
  | Coqtop_lemma of typed_var
  | Coqtop_proof of string
  | Coqtop_ind of coqind list
  | Coqtop_record of coqind 
  | Coqtop_label of var * int
  | Coqtop_implicit of var * (var * implicit) list
  | Coqtop_registercf of var (* todo: generalize to all hints *)
  | Coqtop_registerspec of var (* todo: generalize to all hints *)
  | Coqtop_hint_constructors of vars * var
  | Coqtop_hint_unfold of vars * var
  | Coqtop_require of string
  | Coqtop_import of string
  | Coqtop_require_import of var
  | Coqtop_set_implicit_args 
  | Coqtop_text of string
  | Coqtop_declare_module of var * mod_typ
  | Coqtop_module of var * mod_bindings * mod_cast * mod_def
  | Coqtop_module_type of var * mod_bindings * mod_def
  | Coqtop_end of var
  
and coqtops = coqtop list

(** Modules and signatures *)

and mod_cast =
   | Mod_cast_exact of mod_typ
   | Mod_cast_super of mod_typ
   | Mod_cast_free

and mod_def =
   | Mod_def_inline of mod_expr
   | Mod_def_declare

and mod_typ =
   | Mod_typ_var of var
   | Mod_typ_app of vars
   | Mod_typ_with_def of mod_typ * var * coq
   | Mod_typ_with_mod of mod_typ * var * var

and mod_expr = vars

and mod_binding = vars * mod_typ

and mod_bindings = mod_binding list

(** Inductive definitions *)

and coqind = {
   coqind_name : var;
   coqind_targs : typed_vars;
   coqind_ret : coq;
   coqind_branches : typed_vars; }

(** Implicit Arguements declarations *)

and implicit =
  | Coqi_maximal
  | Coqi_implicit
  | Coqi_explicit


(*#########################################################################*)
(* ** Helper functions to construct expressions *)

(** Several Coq constants *)

let coq_false =  
  Coq_var "False"
  
let coq_true =  
  Coq_var "True"

let coq_bool_false =  
  Coq_var "false"
  
let coq_bool_true =  
  Coq_var "true"

let coq_tt =
  Coq_var "tt"

let coq_unit =
  Coq_var "unit"

let coq_int =
  Coq_var "int" 

let coq_bool =
  Coq_var "bool"

(** Identifier [x] *)

let coq_var x =
  Coq_var x

(** Identifier [@x] *)

let coq_var_at x =
  coq_var ("@" ^ x)

(** List of identifiers [x1 x2 .. xn] *)

let coq_vars xs =
  List.map coq_var xs

(** List of names [(A1:Type)::(A2::Type)::...::(AN:Type)::nil] *)

let coq_types names =
   List.map (fun n -> (n, Coq_type)) names

(** Application to a list of arguments [c e1 e2 .. eN] *)

let coq_apps c args = 
  List.fold_left (fun acc ci -> Coq_app (acc, ci)) c args

(** Application to wildcards [c _ _ .. _] *)

let coq_app_wilds c n =
   coq_apps c (list_make n Coq_wild) 

(** Applications of an identifier to wildcars [x _ _ .. _] *)

let coq_app_var_wilds x n =
   if n = 0 then Coq_var x else coq_app_wilds (coq_var_at x) n

(** Function [fun (x1:T1) .. (xn:Tn) => c] *)

let coq_funs args c =
  List.fold_right (fun ci acc -> Coq_fun (ci, acc)) args c

(** Function [fun (x1:Type) .. (xn:Type) => c] *)

let coq_fun_types names c =
  coq_funs (coq_types names) c

(** Let binding [let (x:T) := t1 in t2] *)

let coq_foralls args c =
  List.fold_right (fun ci acc -> Coq_forall (ci, acc)) args c

(** Universal [forall (x1:T1) .. (xn:Tn), c] *)

let coq_foralls args c =
  List.fold_right (fun ci acc -> Coq_forall (ci, acc)) args c

(** Universal [forall (x1:Type) .. (xn:Type), c] *)

let coq_forall_types names c =
  coq_foralls (coq_types names) c

(** Universal [forall (x1:_) .. (xn:_), c] *)

let coq_foralls_wild names c =
  coq_foralls (List.map (fun n -> (n, Coq_wild)) names) c

(** Implication [c1 -> c2 -> .. -> cn -> c] *)

let coq_impls cs c =
  List.fold_right (fun ci acc -> Coq_impl (ci, acc)) cs c

(** Implication [Type -> Type -> .. -> Type] *)

let coq_impl_types n = 
   coq_impls (list_make n Coq_type) Coq_type

(** Predicate type [A->Prop] *)

let coq_pred c =
  Coq_impl (c, Coq_prop)

(** Product type [(c1 * c2 * .. * cN)%type] *)

let coq_prod cs =
  match cs with 
  | [] -> coq_unit
  | [c] -> c
  | c0::cs' -> List.fold_left (fun acc c -> coq_apps (Coq_var "prod") [acc;c]) c0 cs'

(** Logic combinators *)

let coq_eq c1 c2 =
  coq_apps (Coq_var "Logic.eq") [ c1; c2 ]

let coq_neq c1 c2 =
  coq_apps (Coq_var "Logic.not") [coq_eq c1 c2]

let coq_disj c1 c2 = 
  coq_apps (Coq_var "Logic.or") [c1; c2]

let coq_conj c1 c2 = 
  coq_apps (Coq_var "Logic.and") [c1; c2]

let coq_neg c =
  Coq_app (Coq_var "LibBool.neg", c)

let coq_exist x c1 c2 = 
  coq_apps (Coq_var "Logic.ex") [Coq_fun ((x, c1), c2)]

(** Iterated logic combinators *)

let coq_conjs cs =
  match List.rev cs with
  | [] -> Coq_var "true"
  | c::cs -> List.fold_left (fun acc ci -> coq_conj ci acc) c cs

let coq_exists xcs c2 = 
  List.fold_right (fun (x,c) acc -> coq_exist x c acc) xcs c2

(** Arithmetic operations *)

let coq_le c1 c2 =
  coq_apps (Coq_var "LibOrder.le") [ c1; c2 ]

let coq_gt c1 c2 =
  coq_apps (Coq_var "LibOrder.gt") [ c1; c2 ]

let coq_plus c1 c2 =
  coq_apps (Coq_var "Zplus") [ c1; c2 ]


(** Toplevel *)

let coqtop_def_untyped x c =
   Coqtop_def ((x,Coq_wild), c)

let coqtop_noimplicit x =
   Coqtop_implicit (x,[])


(*#########################################################################*)
(* ** Representation of labels (notation of the form "'x" := `1`0`1`0) *)

(** --todo: deprecated *)

type label = string

let var_bits_of_int n =
   let rec repr n = 
     if n < 2 then [] else (1+(n mod 2))::(repr (n/2)) in
   List.rev (0::(repr n)) 

let string_of_var_bits vb =
  show_listp (fun b -> string_of_int b) "`" vb

let value_variable n =
  string_of_var_bits (var_bits_of_int n)

let coq_tag (tag : string) ?label (term : coq) =
   Coq_tag (tag, label, term)



(*#########################################################################*)
(* ** Printing of Coq expressions *)

(** Print a Coq expression *)

let rec string_of_coq c = 
  let aux = string_of_coq in
  match c with
  | Coq_var s -> s
  | Coq_int n -> "(" ^ (string_of_int n) ^ ")%Z"
  | Coq_app (c1,c2) -> sprintf "(%s %s)" (aux c1) (aux c2)
  | Coq_impl (c1,c2) -> sprintf "(%s -> %s)" (aux c1) (aux c2)
  | Coq_lettuple (cs,c2,c3) -> sprintf "(let '(%s) := %s in %s)" (show_list aux "," cs) (aux c2) (aux c3)
  | Coq_forall ((n,c1),c2) -> sprintf "(forall %s : %s, %s)" n (aux c1) (aux c2)
  | Coq_fun ((n,c1),c2) -> sprintf "(fun %s : %s => %s)" n (aux c1) (aux c2)
  | Coq_wild -> "_"
  | Coq_prop -> "Prop"
  | Coq_type -> "Type"
  | Coq_tuple [] -> aux coq_tt
  | Coq_tuple cs -> sprintf "(%s)" (show_list aux "," cs)
  | Coq_record lcs -> assert false (* todo: connaitre le constructeur, via une table
                                      sprintf "make_%s" (show_list (fun (l,c) -> sprintf "%s=%s" *)
  | Coq_tag (tag, lab, term) -> 
      let slab = match lab with
         | None -> "_"
         | Some x -> sprintf "(Label_create '%s)" x
         in
        sprintf "(%sCFPrint.tag %s %s _ %s)" "@" tag slab (aux term)

(** Print a typed identifier [(x:T)] *)

let string_of_typed_var ?(par=true) (x,c) =
   show_par par (sprintf "%s : %s" x (string_of_coq c))

(** Print a list of typed identifier [(x1:T1) (x2:T2) .. (xN:TN)]  *)

let string_of_typed_vars ?(par=true) tvs =
  show_list (string_of_typed_var ~par:par) " " tvs

(** Print a top-level declarations *)

let rec string_of_coqtop ct =
  let aux = string_of_coq in 
  match ct with
  | Coqtop_def ((n,c1),c2) -> sprintf "Definition %s : %s := %s." n (aux c1) (aux c2)
  | Coqtop_param (n,c1) -> sprintf "Parameter %s : %s." n (aux c1) 
  | Coqtop_instance ((n,c1),g) -> sprintf "%sInstance %s : %s." (if g then "Global " else "") n (aux c1) 
  | Coqtop_lemma (n,c1) -> sprintf "Lemma %s : %s." n (aux c1) 
  | Coqtop_proof s -> sprintf "Proof. %s Qed." s
  | Coqtop_record r -> sprintf "Record %s %s : %s := %s { \n %s }." 
      r.coqind_name
      (string_of_typed_vars r.coqind_targs)
      (aux r.coqind_ret)
      (r.coqind_name ^ "_of")
      (show_list (string_of_typed_var ~par:false) ";\n" r.coqind_branches)
  | Coqtop_ind rs ->
      let show_ind r =
         sprintf "%s %s : %s := %s" 
            r.coqind_name
            (string_of_typed_vars r.coqind_targs)
            (aux r.coqind_ret)
            (show_listp (string_of_typed_var ~par:false) "\n  | " r.coqind_branches) in
      sprintf "Inductive %s." (show_list show_ind "\n\nwith " rs)
  | Coqtop_label (x,n) ->
      sprintf "Notation \"''%s'\" := (%s) (at level 0) : atom_scope." x (value_variable n)
  | Coqtop_implicit (x,xs) -> 
      let show_implicit (x,i) = 
         match i with
         | Coqi_maximal -> sprintf "[%s]" x
         | Coqi_implicit -> sprintf "%s" x
         | Coqi_explicit -> sprintf "" 
         in
      sprintf "Implicit Arguments %s [ %s]." x (show_list show_implicit " " xs)
  | Coqtop_registercf x ->
      sprintf "Hint Extern 1 (RegisterCf %s) => Provide %s_cf." x x
  | Coqtop_registerspec x ->
      sprintf "Hint Extern 1 (RegisterSpec %s) => Provide %s_spec." x x
  | Coqtop_hint_constructors (xs,base) ->
      sprintf "Hint Constructors %s : %s." (show_list show_str " " xs) base
  | Coqtop_hint_unfold (xs,base) ->
      sprintf "Hint Unfold %s : %s." (show_list show_str " " xs) base
  | Coqtop_require x ->
      sprintf "Require %s." x
  | Coqtop_import x ->
      sprintf "Import %s." x
  | Coqtop_require_import x ->
      sprintf "Require Import %s." x
  | Coqtop_set_implicit_args -> 
      sprintf "Set Implicit Arguments."
  | Coqtop_text s -> 
      s
  | Coqtop_declare_module (x,mt) ->
      sprintf "Declare Module %s : %s." x (string_of_mod_typ mt)
  | Coqtop_module (x,bs,c,d) ->
      sprintf "Module %s %s %s %s" x (string_of_mod_bindings bs) (string_of_mod_cast c) (string_of_mod_def x d)
  | Coqtop_module_type (x,bs,d) ->
      sprintf "Module Type %s %s %s" x (string_of_mod_bindings bs) (string_of_mod_def x d)
  | Coqtop_end x ->
      sprintf "End %s." x

and string_of_coqtops cts =
  show_list string_of_coqtop "\n\n" cts

(** Printing for modules *)

and string_of_mod_def x d =
   match d with
   | Mod_def_inline m -> sprintf ":= %s." (string_of_mod_expr m)
   | Mod_def_declare -> sprintf "." 

and string_of_mod_cast c =
   match c with
   | Mod_cast_exact mt -> sprintf " : %s " (string_of_mod_typ mt)
   | Mod_cast_super mt -> sprintf " <: %s " (string_of_mod_typ mt)
   | Mod_cast_free -> ""

and string_of_mod_typ mt =
   match mt with
   | Mod_typ_var x ->
      x
   | Mod_typ_app xs -> 
      show_list (fun x ->x) " " xs (* todo: pb si nest� ! *)
   | Mod_typ_with_def (mt',x,c) -> 
      sprintf " %s with Definition %s := %s " (string_of_mod_typ mt') x (string_of_coq c)
   | Mod_typ_with_mod (mt',x,y) ->
      sprintf " %s with Module %s := %s " (string_of_mod_typ mt') x y

and string_of_mod_expr vs = 
   show_list (fun x ->x) " " vs

and string_of_mod_binding (vs,mt) = 
   sprintf "(%s : %s)" (show_list (fun x -> x) " " vs) (string_of_mod_typ mt)

and string_of_mod_bindings bs = 
   show_list string_of_mod_binding " " bs

