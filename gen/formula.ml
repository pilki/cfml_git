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
  | Cf_let of typed_var * cf * cf 
    (* Let x := Q1 in Q2 *)
  | Cf_letpure of var * vars * vars * coq * cf * cf 
    (* Let x [Ai,Bi] := Q1 in Q2  // where x : forall Ai.T *)
  | Cf_letval of var * vars * vars * coq * coq * cf 
    (* Let x [Ai,Bi] := v in Q2  // where x : forall Ai.T *)
  | Cf_letfunc of (var * cf) list * cf 
    (* Let fi := Qi in Q *)
  | Cf_caseif of coq * cf * cf 
    (* If v Then Q1 else Q2 *)
  | Cf_case of coq * typed_vars * coq * coq option * (typed_var*coq) list * cf * cf 
    (* Case v [xi] p [When c] Then (Alias yk = vk in Q1) else Q2 *)
  | Cf_match of var * int * cf
    (* Match ?lab n Q *)
  | Cf_seq of cf * cf
    (* Q1 ;; Q2 *)
  | Cf_for of var * coq * coq * cf 
    (* for i = v1 to v2 do Q done *)
  | Cf_while of cf * cf
    (* while Q1 do Q2 done *)

type cftop = 
  | Cftop_val of typed_var
    (* Lemma x_safe : Inhab t. Proof. typeclass. Qed.
       Parameter x : t. *)
  | Cftop_heap of var
    (* Parameter h : heap. *)
  | Cftop_val_cf of var * vars * vars * cf 
    (* Parameter x_cf : forall Ai Bi P, F (P Ai) -> P Ai (x Ai) *)
  | Cftop_let_cf of var * var * var * cf 
    (* Parameter x_cf : forall H Q, H h -> F H Q -> Q x h' *)
  | Cftop_fun_cf of var * cf
    (* Parameter f_cf : Val := H *)
  | Cftop_coqs of coqtops
    (* arbitrary coq top-level commands *)

and cftops = cftop list

(*#########################################################################*)
(* Shared functions *)

let val_type = Coq_var "val"


(*#########################################################################*)
(* Conversion of PURE characteristic formulae to Coq *)

let wild_to_prop =
   coq_pred Coq_wild

let rec coq_of_pure_cf cf =
  let coq_of_cf = coq_of_pure_cf in
  let p = Coq_var "P" in
  let funp tag ?label c =
     let f = coq_funs ["P", wild_to_prop] c in
     match label with 
     | None -> coq_tag tag f
     | Some x -> coq_tag tag ~label:x f
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
      let type_of_k = coq_impls ((List.map snd targs) @ [coq_pred wild_to_prop]) Coq_prop in
      let args = List.map fst targs in
      let args_of_k = (List.map coq_var args) @ [ coq_of_cf cf ] in
      let var_k = Coq_var "K" in
      let sarity = string_of_int (List.length targs) in
      let spec_n = Coq_var ("spec_" ^ sarity) in
      let is_spec_k = Coq_app (Coq_var ("is_spec_" ^ sarity), var_k) in
      let hyp_k = coq_foralls targs (coq_apps var_k args_of_k) in
      let concl_k = coq_apps spec_n [var_k; coq_var f] in
      coq_tag "tag_body" (coq_forall_types fvs (coq_foralls ["K", type_of_k] (coq_impls [is_spec_k;hyp_k] concl_k)))       
      (* (!B: (forall Ai K, is_spec_2 K -> 
                 (forall x1 x2, K x1 x2 Q) -> spec_2 K f)) *)

  | Cf_letpure (x, fvs_strict, fvs_other, typ, cf1, cf2) ->
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

  | Cf_seq _ -> unsupported "seq-expression in pure mode"
  | Cf_for _ -> unsupported "for-expression in pure mode"
  | Cf_while _ -> unsupported "while-expression in pure mode"
  | Cf_let _ -> unsupported "let-expression in pure mode"
  | Cf_letval _ -> unsupported "letval-expression in pure mode"


(*#########################################################################*)
(* Conversion of IMPERATIVE characteristic formulae to Coq *)

let heap =
   Coq_var "heap"

let hprop =
   Coq_var "hprop"

let wild_to_hprop =
   Coq_impl (Coq_wild, hprop)

let formula_type =
   coq_impls [hprop; wild_to_hprop] Coq_prop

let heap_empty =
   Coq_var "heap_empty"

let rec coq_of_imp_cf cf =
  let coq_of_cf = coq_of_imp_cf in
  let h = Coq_var "H" in
  let q = Coq_var "Q" in
  let funhq tag ?label c = 
     let f = coq_funs [("H", hprop);("Q", wild_to_hprop)] c in
     match label with 
     | None -> coq_tag tag f 
     | Some x -> coq_tag tag ~label:x f 
     in (* todo improve *)

  match cf with

  | Cf_ret v -> funhq "tag_ret" (coq_conj (Coq_app (h,heap_empty)) (coq_apps q [v;heap_empty]))
     (* (!R: fun H Q => H empty /\ Q v empty *)

  | Cf_fail -> funhq "tag_fail" coq_false

  | Cf_done -> funhq "tag_done" coq_true

  | Cf_app (ts, f, vs) -> 
      (* the following is the same as for pure *)
      let arity = List.length vs in
      assert (arity > 0);
      let appn = coq_var_at ("app_" ^ (string_of_int arity)) in
      coq_tag "tag_apply" (coq_apps appn (ts @ f::vs))
      (* (!A: (app_2 f x1 x2)) *)

  | Cf_body (f, fvs, targs, cf) ->
      let type_of_k = coq_impls ((List.map snd targs) @ [formula_type]) Coq_prop in
      (* the following is the same as for pure *)
      let args = List.map fst targs in
      let args_of_k = (List.map coq_var args) @ [ coq_of_cf cf ] in
      let var_k = Coq_var "K" in
      let sarity = string_of_int (List.length targs) in
      let spec_n = Coq_var ("spec_" ^ sarity) in
      let is_spec_k = Coq_app (Coq_var ("is_spec_" ^ sarity), var_k) in
      let hyp_k = coq_foralls targs (coq_apps var_k args_of_k) in
      let concl_k = coq_apps spec_n [var_k; coq_var f] in
      coq_tag "tag_body" (coq_forall_types fvs (coq_foralls ["K", type_of_k] (coq_impls [is_spec_k;hyp_k] concl_k)))       
      (* (!B: (forall Ai K, is_spec_2 K -> 
                 (forall x1 x2, K x1 x2 F) -> spec_2 K f)) *)

  | Cf_let ((x,typ), cf1, cf2) ->
      let q1 = Coq_var "Q1" in
      let type_of_q1 = Coq_impl (typ, hprop) in
      let c1 = coq_apps (coq_of_cf cf1) [h; q1] in
      let c2 = coq_foralls [x,typ] (coq_apps (coq_of_cf cf2) [(Coq_app (q1, Coq_var x)); q]) in
      funhq "tag_let" ~label:x (coq_exist "Q1" type_of_q1 (coq_conj c1 c2))
      (* !L: fun H Q => exists Q1, F1 H Q1 /\ forall (x:T), F2 (Q1 x) Q *)

  | Cf_letval (x, fvs_strict, fvs_other, typ, v, cf) ->
      let type_of_x = coq_forall_types fvs_strict typ in
      let equ = coq_eq x v in
      let conc = coq_apps (coq_of_cf cf) [h;q] in
      funhq "tag_val" ~label:x (Coq_forall ((x, type_of_x), Coq_impl (equ, conc)))
      (*(!L a: (fun H Q => forall (x:forall Ai,T), x = v -> F H Q)) *)

      (* DEPRECATED
      let type_of_x = coq_forall_types fvs_strict typ in
      let tvars = coq_vars fvs_strict in
      let p1_on_tvars = if tvars = [] then Coq_var "P1" else coq_apps (coq_var_at "P1") tvars in
      let c1 = coq_forall_types (fvs_strict @ fvs_other) (Coq_app (p1_on_tvars, v)) in
      let x_on_tvars = if tvars = [] then Coq_var x else coq_apps (coq_var_at x) tvars in 
      let hyp_on_x = coq_forall_types fvs_strict (coq_apps (Coq_var "@P1") (tvars @ [ x_on_tvars ])) in
      let c2 = coq_foralls [x,type_of_x] (Coq_impl (hyp_on_x, coq_apps (coq_of_cf cf) [h;q])) in
      let type_of_p1 = coq_forall_types fvs_strict (coq_pred typ) in
      funhq "tag_val" ~label:x (coq_exist "P1" type_of_p1 (coq_conj c1 c2))
      (*(!L a: (fun H Q => exists (P1:forall Ai, T -> Prop), (forall Ai Bj, P1 A1 v)
                             /\ forall (x1:forall Ai,T), ((forall Ai, P1 Ai (x1 Ai)) -> F H Q)) *)
      *)
    
  | Cf_letfunc (ncs, cf) ->
      let ns, cs = List.split ncs in
      let p_of n = "P" ^ n in
      let fs = List.map (fun n -> (n, val_type)) ns in
      let ps = List.map (fun n -> (p_of n, coq_pred val_type)) ns in
      let c1hyps = List.map coq_of_cf cs in
      let c1conc = coq_conjs (List.map (fun n -> Coq_app (Coq_var (p_of n), Coq_var n)) ns) in
      let c1 = coq_impls c1hyps c1conc in
      let c2hyps = List.map (fun n -> Coq_app (Coq_var (p_of n), Coq_var n)) ns in
      let c2conc = coq_apps (coq_of_cf cf) [h;q] in
      let c2 = coq_impls c2hyps c2conc in
      let x = List.hd ns in
      funhq "tag_letfun" ~label:x (coq_foralls fs (coq_exists ps (coq_conj c1 c2)))
      (* (!F a: fun H Q => forall f1 f2, exists P1 P2,
              (B1 -> B2 -> P1 f1 /\ P2 f2) /\ (P1 f1 -> P2 f2 -> F H Q)) *)            

  | Cf_caseif (v,cf1,cf2) ->
      let c1 = Coq_impl (coq_eq v (Coq_var "true"),  coq_apps (coq_of_cf cf1) [h;q]) in
      let c2 = Coq_impl (coq_eq v (Coq_var "false"), coq_apps (coq_of_cf cf2) [h;q]) in
      funhq "tag_if" (coq_conj c1 c2)
      (* (!I a: (fun H Q => (x = true -> Q1 H Q) /\ (x = false -> Q2 H Q))) *)

  | Cf_case (v,tps,pat,vwhenopt,aliases,cf1,cf2) ->
      let add_alias ((name,typ),exp) cf : coq =
         funhq "tag_alias" (coq_foralls [name,typ] (coq_impls [coq_eq (Coq_var name) exp] (coq_apps cf [h;q])))
         (* !L a: (fun H Q => forall y, y = v -> F H Q) *)
         in
      let cf1_aliased = List.fold_right add_alias aliases (coq_of_cf cf1) in
      let same = coq_eq v pat in
      let same_when = match vwhenopt with None -> [same] | Some w -> [same; w] in
      let c1 = coq_foralls tps (coq_impls same_when (coq_apps (cf1_aliased) [h;q])) in
      let diff = coq_neq v pat in
      let diff_when = match vwhenopt with None -> diff | Some w -> coq_disj diff (coq_neg w) in
      let c2 = Coq_impl (coq_foralls tps diff_when, coq_apps (coq_of_cf cf2) [h;q]) in
      let tag = match vwhenopt with None -> "tag_case" | Some w -> "tag_casewhen" in
      funhq tag (coq_conj c1 c2)
      (* (!C a: (fun H Q => (forall x1, x = p [-> trueb w] -> (!L a: y := v in F1) H Q) 
                      /\ ((forall x1, x <> p [\/ trueb !w]) -> F2 H Q))) 
          where trueb are implicit by coercions *)
  
  | Cf_match (label, n,cf1) ->
     coq_tag (Printf.sprintf "(tag_match %d%snat)" n "%") ~label:label (coq_of_cf cf1)

  | Cf_seq (cf1,cf2) -> 
      let q1_type = Coq_impl (Coq_var "unit", hprop) in
      let c1 = coq_apps (coq_of_cf cf1) [h; Coq_var "Q1"] in
      let c2 = coq_apps (coq_of_cf cf2) [Coq_app (Coq_var "Q1", coq_tt); Coq_var "Q"]  in
      funhq "tag_seq" (coq_exist "Q1" q1_type (coq_conj c1 c2))
      (* (!S: fun H Q => exists Q1, F1 H Q1 /\ F2 (Q1 tt) Q *)

  | Cf_for (i,v1,v2,cf) -> unsupported "for-expression not yet supported" (* todo *)
      
  | Cf_while (cf1,cf2) -> unsupported "while-expression not yet supported" (* todo *)

  | Cf_letpure _ -> unsupported "letpure-expression in imperative mode"


(*#########################################################################*)
(* Characteristic formulae for top level declarations *)

let coqtops_of_cftop coq_of_cf cft =
  match cft with

  | Cftop_val (x,t) ->
      (* the following is the same as for pure *)
     [ Coqtop_instance ((x ^ "_type_inhab", Coq_app (Coq_var "Inhab", t)), true);
       Coqtop_proof "inhab.";
       Coqtop_text "";
       Coqtop_param (x,t) ]
     (* Lemma x_safe : Inhab t. Proof. typeclass. Qed.
       Parameter x : t *)

  | Cftop_val_cf (x,fvs_strict,fvs_other,cf) -> 
      let type_of_p = coq_forall_types fvs_strict wild_to_prop in
      let p_applied = if fvs_strict = [] then Coq_var "P" else coq_apps (Coq_var "@P") (coq_vars fvs_strict) in
      let x_applied = if fvs_strict = [] then Coq_var x else coq_apps (Coq_var ("@" ^ x)) (coq_vars fvs_strict) in
      let cf_body = coq_foralls ["P", type_of_p] (Coq_impl (Coq_app (coq_of_cf cf, p_applied), Coq_app (p_applied, x_applied))) in
      let hyp = coq_forall_types (fvs_strict @ fvs_other) cf_body in
      let t = coq_tag "tag_topval" hyp in
      [ Coqtop_param (x ^ "_cf", t)]
      (* Parameter x_cf : (!TV label: forall Ai Bi, (forall P:_->Prop, R (P Ai) -> P Ai (x Ai))) *)

  | Cftop_fun_cf (x,cf) -> 
      (* the following is the same as for pure *)
      let t = coq_tag "tag_topfun" (coq_of_cf cf) in
      [ Coqtop_param (x ^ "_cf", t) ]
      (* Parameter x_cf : (!TF a: H) *)

  | Cftop_heap h ->
      [ Coqtop_param (h, heap) ]
      (* Parameter h : heap. *)

  | Cftop_let_cf (x,h,h',cf) ->   
      let conc = coq_apps (Coq_var "Q") [Coq_var x; Coq_var h'] in
      let hyp1 = Coq_app (Coq_var "H", Coq_var h) in
      let hyp2 = coq_apps (coq_of_cf cf) [Coq_var "H"; Coq_var "Q"] in
      let cf_body = coq_foralls [("H",hprop); ("Q",wild_to_hprop)] (coq_impls [hyp1;hyp2] conc) in
      let t = coq_tag "tag_toplet" cf_body in 
      [ Coqtop_param (x ^ "_cf", t) ]
      (* Parameter x_cf : (!TL: forall H Q, H h -> F H Q -> Q x h') *)

  | Cftop_coqs cmds -> cmds


let coqtops_of_cftops coq_of_cf cfts =
   list_concat_map (coqtops_of_cftop coq_of_cf) cfts


(*#########################################################################*)
(* Printing of characteristic formulae as Coq term 

let string_of_cftop cftop =
   string_of_coqtops (coqtops_of_cftop) cftop

let string_of_coqtops cftops =
   string_of_coqtops (list_concat_map coqtops_of_cftop cftops)

*)