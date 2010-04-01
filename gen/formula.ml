open Coq
open Mytools

(*#########################################################################*)
(* Syntax of characteristic formulae *)

type cf =
  | Cf_ret of coq 
    (* Ret v *)
  | Cf_fail
    (* Fail *)
  | Cf_done
    (* Done *)
  | Cf_app of coqs * coq * coqs  
    (* App f Ai xi *)
  | Cf_body of var * vars * typed_vars * cf
    (* Body f Ai xi => Q *)
  | Cf_let of var * vars * vars * coq * cf * cf 
    (* Let x [Ai,Bi] := Qi in Q2 *)
  | Cf_letfunc of (var * cf) list * cf 
    (* Let fi := Qi in Q *)
  | Cf_caseif of coq * cf * cf 
    (* If v Then Q1 else Q2 *)
  | Cf_case of coq * typed_vars * coq * coq option * (typed_var*coq) list * cf * cf 
    (* Case v [xi] p [When c] Then (Alias yk = vk in Q1) else Q2 *)
  | Cf_match of var * int * cf
    (* Match ?lab n Q *)

type cftop = 
  | Cftop_val of typed_var
    (* Lemma x_safe : Inhab t. Proof. typeclass. Qed.
       Parameter x : t *)
  | Cftop_val_cf of var * vars * vars * cf 
    (* Parameter x_spec : ... see further on ... *)
  | Cftop_fun_cf of var * cf
    (* Parameter f_spec : Val := H *)
  | Cftop_coqs of coqtops
    (* arbitrary coq top-level commands *)

and cftops = cftop list

(*#########################################################################*)
(* Conversion of characteristic formulae to Coq *)

let wild_to_prop =
   coq_pred Coq_wild

let val_type = Coq_var "val"

let rec coq_of_cf cf =
  let p = Coq_var "P" in
  let funp tag ?label c = 
     match label with 
     | None -> coq_tag tag (coq_funs ["P", wild_to_prop] c) 
     | Some x -> coq_tag tag ~label:x (coq_funs ["P", wild_to_prop] c) 
     in (* todo improve *)

  match cf with

  | Cf_ret v -> funp "tag_ret" (Coq_app (p, v))

  | Cf_fail -> funp "tag_fail" coq_false

  | Cf_done -> funp "tag_done" coq_true

  | Cf_app (ts, f, vs) -> 
      let arity = List.length vs in
      assert (arity > 0);
      let appn = coq_var_at ("app_" ^ (string_of_int arity)) in
      coq_tag "tag_apply" (coq_apps appn (ts @ f::vs))
      (* (!A: (app_2 f x1 x2)) *)

  | Cf_body (f, fvs, targs, cf) ->
      let args = List.map fst targs in
      let type_of_k = coq_impls ((List.map snd targs) @ [coq_pred wild_to_prop]) Coq_prop in
         (* bin: coq_foralls targs (coq_pred (coq_pred wild_to_prop)) *)
      let args_of_k = (List.map coq_var args) @ [ coq_of_cf cf ] in
      let var_k = Coq_var "K" in
      let sarity = string_of_int (List.length targs) in
      let spec_n = Coq_var ("spec_" ^ sarity) in
      let is_spec_k = Coq_app (Coq_var ("is_spec_" ^ sarity), var_k) in
      let hyp_k = coq_foralls targs (coq_apps var_k args_of_k) in
      let concl_k = coq_apps spec_n [var_k; coq_var f] in
      coq_tag "tag_body" (coq_forall_types fvs (coq_foralls ["K", type_of_k] (coq_impls [is_spec_k;hyp_k] concl_k)))       
      (* (!B: (forall A1 K, is_spec_2 K -> 
                 (forall x1 x2, K x1 x2 Q) -> spec_2 K f)) *)

  | Cf_let (x, fvs_strict, fvs_other, typ, cf1, cf2) ->
      let type_of_x = coq_forall_types fvs_strict typ in
      let tvars = coq_vars fvs_strict in
      let p1_on_tvars = if tvars = [] then Coq_var "P1" else coq_apps (coq_var_at "P1") tvars in
      let c1 = coq_forall_types (fvs_strict @ fvs_other) (Coq_app (coq_of_cf cf1, p1_on_tvars)) in
      let x_on_tvars = if tvars = [] then Coq_var x else coq_apps (coq_var_at x) tvars in 
      let hyp_on_x = coq_forall_types fvs_strict (coq_apps (Coq_var "@P1") (tvars @ [ x_on_tvars ])) in
      let c2 = coq_foralls [x,type_of_x] (Coq_impl (hyp_on_x, Coq_app (coq_of_cf cf2, p))) in
      let type_of_p1 = coq_forall_types fvs_strict (coq_pred typ) in
      funp "tag_let" ~label:x (coq_exist "P1" type_of_p1 (coq_conj c1 c2))
      (*(!L a: (fun P => exists (P1:forall A1, T -> Prop), (forall A1 B1, Q1 (P1 A1))
                             /\ forall (x1:forall A1,T), ((forall A1, P1 A1 (x1 A1)) -> Q2 P)) *)
    
  | Cf_letfunc (ncs, cf) ->
      let ns, cs = List.split ncs in
      let p_of n = "P" ^ n in
      let fs = List.map (fun n -> (n, val_type)) ns in
      let ps = List.map (fun n -> (p_of n, coq_pred val_type)) ns in
      let c1hyps = List.map coq_of_cf cs in
      let c1conc = coq_conjs (List.map (fun n -> Coq_app (Coq_var (p_of n), Coq_var n)) ns) in
      let c1 = coq_impls c1hyps c1conc in
      let c2hyps = List.map (fun n -> Coq_app (Coq_var (p_of n), Coq_var n)) ns in
      let c2conc = Coq_app (coq_of_cf cf, p) in
      let c2 = coq_impls c2hyps c2conc in
      let x = List.hd ns in
      funp "tag_letfun" ~label:x (coq_foralls fs (coq_exists ps (coq_conj c1 c2)))
      (* (!F a: fun P => forall f1 f2, exists P1 P2,
              (Q1 -> Q2 -> P1 f1 /\ P2 f2) /\ (P1 f1 -> P2 f2 -> Q P)) *)            

  | Cf_caseif (v,cf1,cf2) ->
      let c1 = Coq_impl (coq_eq v (Coq_var "true"),  Coq_app (coq_of_cf cf1, p)) in
      let c2 = Coq_impl (coq_eq v (Coq_var "false"), Coq_app (coq_of_cf cf2, p)) in
      funp "tag_if" (coq_conj c1 c2)
      (* (!I a: (fun P => (x = true -> Q1 P) /\ (x = false -> Q2 P))) *)

  | Cf_case (v,tps,pat,vwhenopt,aliases,cf1,cf2) ->
      let add_alias ((name,typ),exp) cf : coq =
         funp "tag_alias" (coq_foralls [name,typ] (coq_impls [coq_eq (Coq_var name) exp] (Coq_app (cf, p))))
         (* !L a: (fun P => forall y, y = v -> Q P) *)
         in
      let cf1_aliased = List.fold_right add_alias aliases (coq_of_cf cf1) in
      let same = coq_eq v pat in
      let same_when = match vwhenopt with None -> [same] | Some w -> [same; w] in
      let c1 = coq_foralls tps (coq_impls same_when (Coq_app (cf1_aliased, p))) in
      let diff = coq_neq v pat in
      let diff_when = match vwhenopt with None -> diff | Some w -> coq_disj diff (coq_neg w) in
      let c2 = Coq_impl (coq_foralls tps diff_when, Coq_app (coq_of_cf cf2, p)) in
      let tag = match vwhenopt with None -> "tag_case" | Some w -> "tag_casewhen" in
      funp tag (coq_conj c1 c2)
      (* (!C a: (fun P => (forall x1, x = p [-> trueb w] -> (!L a: y := v in Q1) P) 
                      /\ ((forall x1, x <> p [\/ trueb !w]) -> Q2 P))) 
          where trueb are implicit by coercions *)
  
   | Cf_match (label, n,cf1) ->
      coq_tag (Printf.sprintf "(tag_match %d%snat)" n "%") ~label:label (coq_of_cf cf1)


let coqtops_of_cftop cft =
  match cft with

  | Cftop_val (x,t) ->
     [ Coqtop_instance ((x ^ "_type_inhab", Coq_app (Coq_var "Inhab", t)), true);
       Coqtop_proof "inhab.";
       Coqtop_text "";
       Coqtop_param (x,t) ]
    (* Lemma x_safe : Inhab t. Proof. typeclass. Qed.
       Parameter x : t *)
       (* \*)

  | Cftop_val_cf (x,fvs_strict,fvs_other,cf) -> 
      let type_of_p = coq_forall_types fvs_strict wild_to_prop in
      let p_applied = if fvs_strict = [] then Coq_var "P" else coq_apps (Coq_var "@P") (coq_vars fvs_strict) in
      let x_applied = if fvs_strict = [] then Coq_var x else coq_apps (Coq_var ("@" ^ x)) (coq_vars fvs_strict) in
      let cf_body = coq_foralls ["P", type_of_p] (Coq_impl (Coq_app (coq_of_cf cf, p_applied), Coq_app (p_applied, x_applied))) in
      let hyp = coq_forall_types (fvs_strict @ fvs_other) cf_body in
      let t = coq_tag "tag_toplet" hyp in
      [ Coqtop_param (x ^ "_cf", t)]
      (* Parameter x_cf : (!T label: forall Ai Bi, (forall P:_->Prop, R (P Ai) -> P Ai (x Ai))) *)

  | Cftop_fun_cf (x,cf) -> 
      let t = coq_tag "tag_topfun" (coq_of_cf cf) in
      [ Coqtop_param (x ^ "_cf", t) ]
      (* Parameter x_cf : (!TF a: H) *)

  | Cftop_coqs cmds -> cmds


let coqtops_of_cftops cfts =
   list_concat_map coqtops_of_cftop cfts


(*#########################################################################*)
(* Printing of characteristic formulae as Coq term *)

let string_of_cftop cftop =
   string_of_coqtops (coqtops_of_cftop cftop)

let string_of_coqtops cftops =
   string_of_coqtops (list_concat_map coqtops_of_cftop cftops)


(*#########################################################################*)
(* BIN

if xs = [] then "" else
          | Coqtop_implicit (x,xs) -> 

*)
