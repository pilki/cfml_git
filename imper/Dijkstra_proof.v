Set Implicit Arguments.
Require Import CFLib Dijkstra_ml.
Open Scope comp_scope.

(*
Module Type MLOrderedPairInt :=
  MLOrdered with Definition t := (int*int)%type.
Module MLNextNode' :  MLOrdered with Definition t := (int*int)%type.
*)

(*************************************************************)


(*-----------------------------------------------------------*)

Definition Min A (f:A->int) (P:A->Prop) :=  
  epsilon (fun n => (exists x, P x /\ n = f x)
                 /\ (forall x, P x -> n <= f x)).

Definition MinBar A (f:A->int) (P:A->Prop) :=  
  If (exists x, P x) then Finite(Min f P) else Infinite.

Lemma Min_eq : forall A x (f:A->int) (P:A->Prop),
  P x -> (forall y, P y -> f x <= f y) -> Min f P = f x.
Proof.
  intros. unfold Min.
  spec_epsilon* as y [(?&?&?) Sy]. clearbody y. subst y.
  forwards*: Sy x. forwards*: H0 x0. apply* le_antisym.
Qed.

Lemma Min_exists_nonneg : forall A (f:A->int) (P:A->Prop),
  (exists x, P x) -> 
  (forall x, P x -> f x >= 0) ->
  exists n, (exists x, P x /\ n = f x)
          /\ (forall x, P x -> n <= f x).
Proof.
(*
  introv [a Pa] Pos. 
  match goal with |- ?G' => set (G := G') end.
  cuts: (forall m:nat, G \/ (forall x, P x -> f x <= m -> False)).
    destruct (H (abs (f a))) as [?|M].
      auto.
      false~ (M a). rewrite~ abs_pos. apply le_refl.
  induction m.
  destruct (classic (exists x, P x /\ f x = 0)) as [(y&Py&Hy)|M].
    left. exists* 0.
    right. intros x Px Non. rew_classic in M. specializes M x.
     rew_classic in M. destruct M as [?|H]. false. apply H. 
      apply~ le_antisym. rewrite le_is_flip_ge. unfold flip. auto.
  destruct IHm as [?|N]. eauto. right. intros x Px Le.
    destruct (classic (exists x, P x /\ f x = m)) as [(y&Py&Hy)|M].
*)
Admitted.

Lemma Min_inv : forall A x (f:A->int) (P:A->Prop),
  (forall x, P x -> f x >= 0) ->
  P x -> 
  Min f P <= f x.
Proof.
(*
  unfold Min. introv H Px. 
  spec_epsilon as z Hz. exists (f x). 
*)
Admitted.

Lemma MinBar_Infinite : forall A (f:A->int) (P:A->Prop),
  (forall x, ~ P x) -> MinBar f P = Infinite.
Proof.
  intros. unfold MinBar. case_if~. destruct e as [x ?]. false*.
Qed.

Lemma MinBar_Finite : forall A x (f:A->int) (P:A->Prop),
  P x -> (forall y, P y -> f x <= f y) ->
  MinBar f P = Finite (f x).
Proof. 
  intros. unfold MinBar. case_if. 
  fequal. apply~ Min_eq. 
  rew_classic in n. false*.
Qed.

Lemma MinBar_Finite_inv : forall A n x (f:A->int) (P:A->Prop),
  MinBar f P = Finite n -> (forall x, P x -> f x >= 0) -> P x -> n <= f x.
Proof.
  unfold MinBar. introv H Pos Px. case_if.
  destruct e as [y ?]. invert H as M. apply~ Min_inv.
  false.
Qed.

Lemma MinBar_Infinite_inv : forall A x (f:A->int) (P:A->Prop),
  MinBar f P = Infinite -> ~ P x.
Proof. 
  unfold MinBar. introv H Px. case_if.
  false.
  rew_classic in n. false*.
Qed.

(*-----------------------------------------------------------*)

Parameter graph : Type -> Type.
Parameter nodes : forall A, graph A -> set int.
Parameter edges : forall A, graph A -> set (int*int*A).
  
Definition has_edge A (g:graph A) x y w :=
  (x,y,w) \in edges g.

Parameter edges_are_nodes : forall A (g : graph A) x y w,
  has_edge g x y w -> x \in nodes g /\ y \in nodes g.

Definition nonnegative_edges (g:graph int) :=
  forall x y w, has_edge g x y w -> w >= 0.

(*-----------------------------------------------------------*)

Definition path A := list (int*int*A).

Inductive is_path A (g:graph A) : int -> int -> path A -> Prop :=
  | is_path_nil : forall x, 
      is_path g x x nil
  | is_path_cons : forall x y z w p,
      is_path g x y p ->
      has_edge g y z w ->
      is_path g x z ((y,z,w)::p).

Definition weight (p:path int) :=
  nosimpl (fold_right (fun e acc => let '(_,_,w) := e in w+acc) 0 p).

Definition dist (g:graph int) x y :=  
  MinBar weight (is_path g x y).


Lemma weight_nil : 
  weight (nil : path int) = 0.
Proof. auto. Qed.

Lemma weight_cons : forall (p:path int) x y w, 
  weight ((x,y,w)::p) = w + weight p.
Proof. intros. unfold weight. rew_list~. Qed.

(*-----------------------------------------------------------*)

Parameter range : int -> int -> set int.

Definition GraphAdjList (G:graph int) (g:loc) :=
  Hexists N, g ~> Array Id N
         \* [nodes G = range 0 (LibArray.length N)]
         \* [forall_ x \in (nodes G), forall y w, 
               Mem (y,w) (N\(x)) = has_edge G x y w].


(*************************************************************)

Module Type OrderedSigSpec.

Declare Module O : MLOrdered.
Import O.
Parameter T : Type.
Parameter S : htype T t.

Global Instance le_inst : Le T.
Global Instance le_order : Le_total_order.

Parameter le_spec : Spec le (x:t) (y:t) |R>> forall X Y,  
  keep R (x ~> S X \* y ~> S Y) (\= istrue (LibOrder.le X Y)).

Hint Extern 1 (RegisterSpec le) => Provide le_spec.

End OrderedSigSpec.


(*************************************************************)

(** Definition of the minimum of a multiset *)

Definition is_min_of `{Le A} (E:multiset A) (X:A) := 
  X \in E /\ forall_ Y \in E, X <= Y.

(*************************************************************)

Module Type HeapSigSpec.

Declare Module H : MLHeapSig.
Declare Module OS : OrderedSigSpec with Module O := H.MLElement.
Import H MLElement OS. 

Parameter Heap : htype T t -> htype (multiset T) heap.

Parameter create_spec :
  Spec create () |R>> 
    R [] (~> Heap S \{}).

Parameter is_empty_spec : 
  Spec is_empty (h:heap) |R>> forall E,
    keep R (h ~> Heap S E) (\= istrue (E = \{})).

Parameter push_spec : 
  Spec push (x:t) (h:heap) |R>> forall E X,
    R (h ~> Heap S E \* x ~> S X) (# h ~> Heap S (\{X} \u E)).

Parameter pop_spec : 
  Spec pop (h:heap) |R>> forall E,
    R (h ~> Heap S E) (fun x => Hexists X F, 
      [is_min_of E X] \* [E = \{X} \u F] \* x ~> S X \* h ~> Heap S F).

Hint Extern 1 (RegisterSpec create) => Provide create_spec.
Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.
Hint Extern 1 (RegisterSpec push) => Provide push_spec.
Hint Extern 1 (RegisterSpec pop) => Provide pop_spec.
End HeapSigSpec.


(*************************************************************)

Module NextNodeSpec <: OrderedSigSpec with Module O := MLNextNode.
Module O := MLNextNode.
Import O.
Definition T : Type := (int*int)%type.
Definition S : htype T t := Id.

Global Instance le_inst : Le T.
Proof.
  constructor.
  exact (fun (p1 p2 : int*int) => snd p1 <= snd p2).
Defined.
  
Global Instance le_order : Le_total_order.
Admitted. (* todo :order prod *)

Lemma le_spec : Spec le (x:t) (y:t) |R>> forall X Y, 
  keep R (x ~> S X \* y ~> S Y) (\= istrue (LibOrder.le X Y)).
Proof.
  xcf. unfold S. intros x y X Y. xextract. intros. subst. xgo~.
Qed.

Hint Extern 1 (RegisterSpec le) => Provide le_spec.

End NextNodeSpec.

(*************************************************************)

Global Instance len_inhab : Inhab len.
Proof. constructor. exact Infinite. Qed.


(*************************************************************)
Require Import LibArray LibMap.

Module DijkstraSpec.
Declare Module MLHeap : MLHeapSig with Module MLElement := MLNextNode.
Import NextNodeSpec.
Module Dijkstra := MLDijkstra MLHeap.
Import Dijkstra.



(*-----------------------------------------------------------*)

Hint Constructors Mem.

Hint Extern 1 (index _ _) => skip.

Axiom bool_test' : forall b,
  b = true \/ b = false.

Hint Constructors is_path.

Tactic Notation "rew_array" "~" :=
  rew_array; auto_tilde.
Tactic Notation "rew_array" "~" "in" hyp(H) :=
  rew_array in H; auto_tilde.



Implicit Arguments eq_trans' [A].

Axiom array_make_read : forall `{Inhab A} (i n:int) (v:A),
  index n i -> (make n v)\(i) = v.

Hint Rewrite @array_make_read : rew_array.

Ltac multiset_in_inv_base H M ::=
  match type of H with
  | _ \in \{} => false; apply (@in_empty_inv _ _ H)  
  | _ \in \{_} => 
    generalize (in_single_inv H); try clear H; try intro_subst_hyp
  | _ \in _ \u _ => 
    let H' := fresh "TEMP" in
    destruct (in_union_inv H) as [H'|H']; 
    try clear H; multiset_in_inv_base H' M
  | _ => rename H into M
  end.

Ltac auto_star ::= try solve [ auto | jauto ].


(*-----------------------------------------------------------*)

Implicit Types V : array bool.
Implicit Types B : array len.
Implicit Types H : multiset (int*int).
Implicit Types p : path int.

Section Invariants.
Variables (G:graph int) (s:int).

(*-----------------------------------------------------------*)

Definition dist_ok V B H reach := forall z, 
  If (z = s) \/ V\(z) = true
    then B\(z) = dist G s z
    else B\(z) = MinBar weight (reach z).

Definition heap_correct V B H reach := forall z d,
   V\(z) = false -> z <> s -> (z,d) \in H -> 
    exists p, reach z p /\ weight p = d.

Definition heap_complete V B H reach := forall z p,
   reach z p -> exists d, (z,d) \in H /\ d <= weight p. 

Record inv V B H reach : Prop :=
  { inv_dist  : dist_ok V B H reach;
    inv_hcorr : heap_correct V B H reach;
    inv_hcomp : heap_complete V B H reach }.


Definition from_out V z p :=
  is_path G s z p /\ V\(z) = false.

Definition enters V z p :=
  from_out V z p /\ (p = nil \/ exists q y w, p = (y,z,w)::q /\ V\(y) = true).

Definition enters_via x L V z p :=
  from_out V z p /\ exists q w, p = (x,z,w)::q /\ Mem (z,w) L.

Definition new_enters x L V z p :=
  enters V z p \/ enters_via x L V z p.


(*-----------------------------------------------------------*)

Lemma new_enters_grows : forall x L V z p y w,
  new_enters x L V z p -> new_enters x ((y,w)::L) V z p.
Proof. introv [H|(q&w'&?&?&M)]. left~. right. split*. Qed.

Lemma new_enters_inv : forall x L V z p y w,
  new_enters x ((y,w)::L) V z p -> 
      new_enters x L V z p 
   \/ (from_out V z p /\ exists q, p = (x,y,w)::q).
Proof.
  introv [H|(P&(q&w'&E&M))]. left. left~.
  inverts M. right*. left; right; split*.
Qed.

(* todo: seul un sens est nécessaire *)
Lemma enters_step : forall L V x z p, V\(x) = false -> z <> x ->
  (forall y w, Mem (y,w) L = has_edge G x y w) ->
  enters (V\(x:=true)) z p = new_enters x L V z p.
Proof.
  introv Vx Nvx EQ.
  asserts EF: (from_out (V\(x:=true)) z p = from_out V z p).
    intros. unfold from_out. rew_array~.
  extens. iff H. hnf in H.
  destruct H as (F&[N|(q&y&w&E&Vy)]).
   rewrite~ EF in F. subst. left. split~.
   rewrite~ EF in F. tests (y = x).
    right. split~. exists q w. split~. rewrite EQ. 
     lets: (proj1 F). subst p. inverts* H.
    left. rew_array~ in Vy. splits~. right*.
  destruct H as [(F&[N|(q&y&w&E&Vy)])|(P&(q&w&E&M))];
   (split; [ rewrite~ EF | ]).
     auto.
     right. exists q y w. split~. rew_array~. intro_subst; false.
     right. exists q x w. split~. rew_array~.
Qed.

Lemma enters_shorter : forall V z p, 
  nonnegative_edges G ->
  is_path G s z p -> V\(z) = false -> 
  exists x q, enters V x q /\ weight q <= weight p.
Proof.
  introv NG P. set_eq s': s in P. set_eq G': G in P. 
  induction P; intros; subst. 
  exists s (nil:path int). splits_all~. apply le_refl.
  destruct (bool_test' (V\(y))).
    exists z ((y,z,w)::p). split. 
      split. split~.
      right. exists p y w. split~. apply le_refl.
    forwards~ (x&q&E&L): IHP. exists x q. split~.
     rewrite weight_cons. forwards: NG H. math.    
Qed.

Lemma enters_best : forall V x p,
  nonnegative_edges G ->
  V\(x) = false -> enters V x p ->
  (forall y q, enters V y q -> weight p <= weight q) ->
  dist G s x = Finite (weight p).
Proof.
  introv NG Vx E BE.
  unfold dist.
  lets ((?&_)&_): E. applys~ (@MinBar_Finite (path int)) p.
  intros p' P'. forwards~ (y&q&E'&L): enters_shorter V P'.
   forwards: BE E'. math.
Qed.

Lemma nonnegative_path : forall p x y, 
  nonnegative_edges G -> is_path G x y p -> 0 <= weight p.
Proof.
  introv NG H. induction H. 
  rewrite weight_nil. apply le_refl.
  rewrite weight_cons. forwards: NG H0. math.
Qed.


(*-----------------------------------------------------------*)

Lemma cases_or_l : forall (P Q:Prop),
  P \/ (~ P /\ Q) \/ (~ P /\ ~ Q).
Proof. intros. tautoB P Q. Qed.

Ltac apply_to_If cont :=
  match goal with 
  | |- context [If ?B then _ else _] => cont B
  | K: context [If ?B then _ else _] |- _ => cont B
  end.

Ltac case_If_core B I1 I2:=
  let H1 := fresh "TEMP" in let H2 := fresh "TEMP" in
  destruct (classicT B) as [H1|H2]; 
  [ rew_logic in H1; revert H1; intros I1
  | rew_logic in H2; revert H2; intros I2 ].

Tactic Notation "case_If" "as" simple_intropattern(I1) simple_intropattern(I2) :=
  apply_to_If ltac:(fun B => case_If_core B I1 I2).

Tactic Notation "case_If" "as" simple_intropattern(I) :=
  apply_to_If ltac:(fun B => case_If_core B I I).


(*-----------------------------------------------------------*)

Ltac my_cases :=
  apply_to_If ltac:(fun B =>
    match B with ?P \/ ?Q =>
     destruct (cases_or_l P Q) as [So|[[So Vi]|[So Vi]]] end).

Lemma dist_source : 
  nonnegative_edges G -> dist G s s = Finite 0.
Proof.
  introv NG. applys~ (MinBar_Finite (nil:path int)).
  intros. apply* nonnegative_path.
Qed.


Lemma inv_start : forall n, nonnegative_edges G -> 
  inv (make n false) (make n Infinite\(s:=Finite 0)) 
      ('{(s, 0)}) (enters (make n false)).
Proof.
  introv NG. constructor; unfolds.
  intros. case_If as I [So _]. destruct (case_classic_l I) as [So|[So Vi]].
    subst. rew_array~. rewrite~ dist_source.
    rew_array~ in Vi. false.
    rew_array~. rewrite~ MinBar_Infinite.
     intros p (P&[Pn|(q&y&w&_&E)]).
       subst. destruct P as [H _]. inverts H. false.
       rew_array~ in E.
  introv _ Ns E. multiset_in E. intros E. inverts E. false.
  introv (P&[Pn|(q&y&w&_&E)]). 
    exists 0. subst p. destruct P as [H _]. inverts H. split.
     auto. apply le_refl. (* todo: auto le_refl *)
    rew_array~ in E. false.  
Qed.

Axiom bool_neq_true_eq_false : forall b,
  b <> true -> b = false.
Hint Resolve bool_neq_true_eq_false.


Lemma inv_end_elim : forall e V B,
  nonnegative_edges G -> 
  inv V B \{} (enters V) -> B\(e) = dist G s e.
Proof.
  introv [Dok Hcorr Hcomp].
  specializes Dok e. case_If as E [So Vf]. auto.
  asserts Ne: (forall z p, ~ enters V z p).
    introv P. forwards (d&N&_): Hcomp P. multiset_in N.
  unfold dist. rewrite Dok.
  apply (eq_trans' Infinite); rewrite~ MinBar_Infinite.
  intros p P. forwards* (z&q&Q&?): enters_shorter P. 
Qed.

(*
Lemma inv_step : 

: forall L V x z p, V\(x) = false -> z <> x ->
  (forall y w, Mem (y,w) L = has_edge G x y w) ->
  enters (V\(x:=true)) z p = new_enters x L V z p.
Proof.
*)


(*-----------------------------------------------------------*)

End Invariants.

Import MLHeap.

Parameter Heap : htype (multiset (int*int)) heap.

Parameter create_spec :
  Spec create () |R>> 
    R [] (~> Heap \{}).

Parameter is_empty_spec : 
  Spec is_empty (h:heap) |R>> forall E,
    keep R (h ~> Heap E) (\= istrue (E = \{})).

Parameter push_spec : 
  Spec push (x:int*int) (h:heap) |R>> forall E X,
    R (h ~> Heap E \* x ~> S X) (# h ~> Heap (\{X} \u E)).

Parameter pop_spec : 
  Spec pop (h:heap) |R>> forall E,
    R (h ~> Heap E) (fun x => Hexists X F, 
      [is_min_of E X] \* [E = \{X} \u F] \* x ~> Id X \* h ~> Heap F).

Hint Extern 1 (RegisterSpec create) => Provide create_spec.
Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.
Hint Extern 1 (RegisterSpec push) => Provide push_spec.
Hint Extern 1 (RegisterSpec pop) => Provide pop_spec.


(*-----------------------------------------------------------*)


Ltac xwhile_inv_core W I :=
  match type of W with
  | wf _ => eapply (@while_loop_cf_to_inv _ I _ W)
  | _ -> nat => eapply (@while_loop_cf_to_inv _ I (measure W))
  | _ => eapply (@while_loop_cf_to_inv _ I W)
  end.


Tactic Notation "xwhile_inv" constr(W) constr(I) :=
  xwhile_pre ltac:(fun _ => xwhile_inv_core W I).


Ltac xfun_mg_core tt :=
  apply local_erase;
  intro; let f := get_last_hyp tt in let H := fresh "S" f in
  esplit; split; intros H; [ pattern f in H; eexact H | ].
Tactic Notation "xfun_mg" := xfun_mg_core tt.


Lemma shortest_path_spec :
  Spec shortest_path g a b |R>> forall G,
    nonnegative_edges G ->
    a \in nodes G ->
    b \in nodes G ->
    keep R (g ~> GraphAdjList G) (\= dist G a b).
Proof.
  xcf. introv Pos Ds De. unfold GraphAdjList at 1. hdata_simpl.
  xextract as N NG Adj. xapps. xapps. xapps. xapps. xapps~. xapps. (* todo: xgo loop *)
  set (data := fun B V H =>
    g ~> Array Id N \* v ~> Array Id V \* b ~> Array Id B \* h ~> Heap H).
  set (hinv := fun H:multiset(int*int) => 
    Hexists B V, data B V H \* [inv G s V B H (enters G s V)]).
  xseq (# hinv \{}). xwhile_inv (fun H:multiset(int*int) => 0%nat) hinv. 
    skip. (* todo: termination *)
    (* -- initial state satisfies invariant -- *)
    esplit. unfold hinv,data. hsimpl. 
     applys_eq~ inv_start 2. permut_simpl.
    (* -- verification of the loop body -- *) 
    intros H. unfold hinv. xextract as B V [Dok Hcorr Hcomp]. 
     apply local_erase. esplit. splits.
    (* ---- loop condition -- *) 
    unfold data. xapps. xret.
    (* ---- loop body -- *) 
    xextract as HN. xapp. intros [x d] H' Mi HE. intro_subst. xmatch.
    xapps~. xif; [ skip: (V\(x) = false) | ].
    (* ------ node treated -- *) 
    xapps~. xfun_mg. xapps~. 
Lemma ml_list_iter_spec : forall a,
  Spec ml_list_iter f l |R>> forall (I:list a->hprop),
    (Spec f x |R>> forall t, R (I (x::t)) (# I t)) -> 
    R (I l) (# I nil).
Admitted.
Hint Extern 1 (RegisterSpec  ml_list_iter) => Provide ml_list_iter_spec.
sets V': (V\(x:=true)).
    sets I: (fun L => Hexists L', Hexists B H, data B V' H (* todo bug si Hexists *)
        \* [inv G s V B H (new_enters G s x L' V) ] \* [N\(x) = L'++L]).
    xapp_manual. xapply (KR I); clear KR; match goal with |- context [update] => idtac | _ => clears update end.
    (* -------- verification of update -- *) 
    apply Supdate. xisspec. clears update.  (* todo tactic *)
    unfold I at 1. hide I. unfold data. clears B H. 
    intros [y w] L. xextract as L' B H [Dok Hcorr Hcomp] EQ.
    xmatch. xlet. xret. (* todo xret does xlet *)
    xapps~. xlet. skip. (*  xframe - []. xmatch. xret. hsimpl. -- todo post of let *) 
    xif. 
    xapps~. skip. xapps~. skip.
    skip.
    xret. skip.
    skip.
...
    (* -------- iter pre-condition -- *) 
    unfold I. unfold data. hsimpl (nil:list (int*int)).
    auto. constructors~.
    skip.  (* if x = z then lemma enters_best else Tok *)
    skip. (* if x = z then absurd else Uok *)
    skip. (* if x = z then absurd else Hcorr *)
    (* -------- iter post-condition -- *) 
    xok. clears update. subst I. hsimpl~. hsimpl. 
    skip. (* termination *)
    unfold V'.  skip. (* inv_step *)
    (* ------ node ignored -- *) 
    xret. unfold data. hsimpl.
      skip. (*termination*) skip: (V\(x) = true) .
      constructors~.
        introv Vz Nzs In. apply~ Hcorr. rewrite HE. auto. (* mset *)
        introv E. lets ((_&?)&_): E. tests (z = x); tryfalse.
          forwards (d'&R&?): Hcomp E. exists d'. split~.
           rewrite HE in R. multiset_in R; auto_false.
    (* ---- loop post-condition -- *) 
    hextract as He. fold_bool. rew_logic in He. subst H.
     unfold data. xsimpl. constructor~.
  (* ---- return value -- *) 
  unfold hinv, data. xextract as B V Inv. 
  xapp~. intros l. hdata_simpl GraphAdjList. xsimpl~.
  subst l. apply* inv_at_end_correct.
Qed.

(* todo: prettyprint for  "let (x,y) =" and "fun (x,y) ="




Definition from_out V z p :=
  is_path G s z p /\ V\(z) = false.

Definition enters V z p :=
  from_out V z p /\ (exists q y w, p = (y,z,w)::q /\ V\(y) = true).


Record inv V B H reach : Prop :=
  { source_ok     : B\(s) = Finite 0;
    treated_ok    : forall z, V\(z) = true -> B\(z) = dist G s z;
    untreated_ok  : forall z, V\(z) = false -> z <> s -> 
                      B\(z) = MinBar weight (reach z);
    heap_correct  : forall z d, V\(z) = false -> z <> s -> (z,d) \in H -> 
                      exists p, reach z p /\ weight p = d;
    heap_complete : forall z p, reach z p -> 
                      exists d, (z,d) \in H /\ d <= weight p }.  



(*-----------------------------------------------------------*)

End DijkstraSpec. 
