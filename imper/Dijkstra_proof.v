Set Implicit Arguments.
Require Import CFLib Dijkstra_ml.
Open Scope comp_scope.

(*
Module Type MLOrderedPairInt :=
  MLOrdered with Definition t := (int*int)%type.
Module MLNextNode' :  MLOrdered with Definition t := (int*int)%type.
*)


Lemma not_True_to_False : ~ True -> False.
Proof. intros. rew_logic in *. auto. Qed.
Hint Immediate not_True_to_False.


(*************************************************************)


Definition value_nonneg A (f:A->int) (P:A->Prop) :=
  forall x, P x -> f x >= 0.  

(*-----------------------------------------------------------*)

Definition min A (f:A->int) (P:A->Prop) :=  
  epsilon (fun n => (exists x, P x /\ n = f x)
                 /\ (forall x, P x -> n <= f x)).

Lemma min_eq : forall A x (f:A->int) (P:A->Prop),
  P x -> (forall y, P y -> f x <= f y) -> min f P = f x.
Proof.
  intros. unfold min.
  spec_epsilon* as y [(?&?&?) Sy]. clearbody y. subst y.
  forwards*: Sy x. forwards*: H0 x0. apply* le_antisym.
Qed.

Lemma min_exists_nonneg : forall A (f:A->int) (P:A->Prop),
  (exists x, P x) -> 
  value_nonneg f P ->
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

Lemma min_inv : forall A (f:A->int) (P:A->Prop),
  (exists x, P x) -> value_nonneg f P -> 
  exists x, P x /\ min f P = f x /\ (forall y, P y -> f x <= f y).
Proof.
  intros. forwards* (n&(y&Py&Ey)&My): min_exists_nonneg.
  unfold min. spec_epsilon* as z' ((z&Pz&Ez)&Hz). rewrite* Ez in Hz.
Qed.

Lemma min_elim : forall A x (f:A->int) (P:A->Prop),
  value_nonneg f P ->
  P x -> 
  min f P <= f x.
Proof. intros. forwards* (y&Py&Ey&My): min_inv. rewrite~ Ey. Qed.


(*-----------------------------------------------------------*)

Definition mininf A (f:A->int) (P:A->Prop) :=  
  If (exists x, P x) then Finite(min f P) else Infinite.

Lemma mininf_infinite : forall A (f:A->int) (P:A->Prop),
  (forall x, ~ P x) -> mininf f P = Infinite.
Proof.
  intros. unfold mininf. case_if~. destruct e as [x ?]. false*.
Qed.

Lemma mininf_finite : forall A x (f:A->int) (P:A->Prop),
  P x -> (forall y, P y -> f x <= f y) -> mininf f P = Finite (f x).
Proof. 
  intros. unfold mininf. case_if. 
  fequal. apply~ min_eq. 
  rew_classic in n. false*.
Qed.

Lemma mininf_finite_inv : forall A n (f:A->int) (P:A->Prop),
  mininf f P = Finite n -> value_nonneg f P ->
   exists x, P x /\ f x = n /\ (forall y, P y -> n <= f y).
Proof.
  introv E N. unfold mininf in E. case_If. inverts E. 
  forwards* (x&Px&Ex&Mx): min_inv. rewrite* <- Ex in Mx.
Qed.

Lemma mininf_finite_elim : forall A n x (f:A->int) (P:A->Prop),
  mininf f P = Finite n -> value_nonneg f P -> P x -> n <= f x.
Proof.
  unfold mininf. introv H Pos Px. case_if.
  destruct e as [y ?]. invert H as M. apply~ min_elim.
  false.
Qed.

Lemma mininf_infinite_inv: forall A (f:A->int) (P:A->Prop),
  mininf f P = Infinite -> (forall x, ~ P x).
Proof. 
  unfold mininf. introv H Px. case_if.
  false.
  rew_classic in n. false*.
Qed.

Lemma mininf_infinite_elim : forall A x (f:A->int) (P:A->Prop),
  mininf f P = Infinite -> ~ P x.
Proof. intros. apply* mininf_infinite_inv. Qed.

(*-----------------------------------------------------------*)

Definition len_gt l d :=
  match l with Finite d' => d < d' | Infinite => True end.

Lemma mininf_len_gt : forall d A (f:A->int) (P:A->Prop),
  len_gt (mininf f P) d ->
  value_nonneg f P ->
  forall x, P x -> d < f x.
Proof.
  unfold len_gt. introv H NE. sets_eq l:(mininf f P).  (* todo: case_eq*)
  intros. destruct l.
    forwards*: (@mininf_finite_elim A). math.
    forwards*: (@mininf_infinite_elim A) x.
Qed.

Lemma mininf_len_gt_not : forall d A (f:A->int) (P:A->Prop),
  ~ (len_gt (mininf f P) d) ->
  value_nonneg f P ->
  exists d', mininf f P = Finite d' /\ d' <= d.
Proof. 
  unfold len_gt. introv H N. cases (mininf f P); tryfalse~.
  forwards* (x&Px&Ex&Mx): mininf_finite_inv. eauto with maths.
Qed.
Lemma mininf_len_gt_not_elim : forall d A (f:A->int) (P:A->Prop),
  ~ (len_gt (mininf f P) d) ->
  value_nonneg f P ->
  exists x, P x /\ f x <= d.
Proof.
  introv H N. forwards~ (d'&E&L): mininf_len_gt_not H.
  forwards~ (x&Px&Lx&_): mininf_finite_inv E. eauto with maths.
Qed.

(*-----------------------------------------------------------*)

Parameter graph : Type -> Type.
Parameter nodes : forall A, graph A -> set int.
Parameter edges : forall A, graph A -> set (int*int*A).
  
Definition has_edge A (g:graph A) x y w :=
  (x,y,w) \in edges g.

Parameter has_edge_nodes : forall A (g : graph A) x y w,
  has_edge g x y w -> x \in nodes g /\ y \in nodes g.

Lemma has_edge_in_nodes_l : forall A (g : graph A) x y w,
  has_edge g x y w -> x \in nodes g.
Proof. intros. forwards*: has_edge_nodes. Qed.

Lemma has_edge_in_nodes_r : forall A (g : graph A) x y w,
  has_edge g x y w -> y \in nodes g.
Proof. intros. forwards*: has_edge_nodes. Qed.

Definition nonneg_edges (g:graph int) :=
  forall x y w, has_edge g x y w -> w >= 0.
  (* forall x y, value_nonneg id (has_edge g x y) *)

(*-----------------------------------------------------------*)

Definition path A := list (int*int*A).

Inductive is_path A (g:graph A) : int -> int -> path A -> Prop :=
  | is_path_nil : forall x, 
      x \in nodes g ->
      is_path g x x nil
  | is_path_cons : forall x y z w p,
      is_path g x y p ->
      has_edge g y z w ->
      is_path g x z ((y,z,w)::p).

Definition weight (p:path int) :=
  nosimpl (fold_right (fun e acc => let '(_,_,w) := e in w+acc) 0 p).

Definition dist (g:graph int) x y :=  
  mininf weight (is_path g x y).

Lemma weight_nil : 
  weight (nil : path int) = 0.
Proof. auto. Qed.

Lemma weight_cons : forall (p:path int) x y w, 
  weight ((x,y,w)::p) = w + weight p.
Proof. intros. unfold weight. rew_list~. Qed.

Lemma nonneg_edges_to_path : forall g x y, 
  nonneg_edges g ->
  value_nonneg weight (is_path g x y).
Proof.
  introv NG H. induction H. 
  rewrite weight_nil. math. 
  rewrite weight_cons. forwards: NG H0. math.
Qed.

Lemma is_path_cons_has_edge : forall A (g:graph A) x y z w p,
  is_path g x z ((y,z,w)::p) -> has_edge g y z w.
Proof. introv H. inverts~ H. Qed.

Lemma is_path_in_nodes_l : forall A (g:graph A) x y p,
  is_path g x y p -> x \in nodes g.
Proof. introv H. induction~ H. Qed.

Lemma is_path_in_nodes_r : forall A (g:graph A) x y p,
  is_path g x y p -> y \in nodes g.
Proof. introv H. inverts~ H. apply* has_edge_in_nodes_r. Qed. 
     
Parameter edges_are_nodes : forall A (g : graph A) x y w,
  has_edge g x y w -> x \in nodes g /\ y \in nodes g.



(*-----------------------------------------------------------*)

Parameter range : int -> int -> set int.

Definition GraphAdjList (G:graph int) (g:loc) :=
  Hexists N, g ~> Array Id N
   \* [forall x, x \in nodes G = index (LibArray.length N) x]
   \* [forall x y w, x \in nodes G ->
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

Import MLHeap.

(*-----------------------------------------------------------*)
(* todo : fix *)

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

Hint Constructors Mem.

Axiom bool_test' : forall b,
  b = true \/ b = false.

Hint Constructors is_path.

Axiom bool_neq_true_eq_false : forall b,
  b <> true -> b = false.
Hint Resolve bool_neq_true_eq_false.

Ltac auto_star ::= try solve [ auto | jauto ]. 
  (* todo: congruence *)

Hint Resolve istrue_True.

(*
Hint Extern 3 (_ \in _) => in_union_extract.
Hint Extern 3 (_ \in _ \u _) => in_union_get.
*)



(*-----------------------------------------------------------*)

Hint Rewrite @array_update_read_eq : rew_arr.

Tactic Notation "rew_arr" := 
  autorewrite with rew_arr.
Tactic Notation "rew_arr" "in" hyp(H) := 
  autorewrite with rew_arr in H.
Tactic Notation "rew_arr" "in" "*" := 
  autorewrite with rew_arr in *.

Tactic Notation "rew_arr" "~" :=
  rew_arr; auto_tilde.
Tactic Notation "rew_arr" "*" :=
  rew_arr; auto_star.
Tactic Notation "rew_arr" "~" "in" hyp(H) :=
  rew_arr in H; auto_tilde.
Tactic Notation "rew_arr" "*" "in" hyp(H) :=
  rew_arr in H; auto_star.


Axiom make_index : forall `{Inhab A} n i (v:A),
  index n i -> index (make n v) i.
Hint Resolve @make_index.
Hint Resolve len_inhab.

Lemma pred_ext_elim_l_0 : forall A (P Q:A->Prop),
  (forall x, P x = Q x) -> (forall x, P x -> Q x).
Proof. introv H. intros. rewrite~ <- H. Qed.
Implicit Arguments pred_ext_elim_l_0 [A P Q].

Axiom index_update : forall `{Inhab A} (T:array A) n i j (v:A),
  index n i -> index (T\(j:=v)) i.
Hint Resolve @index_update.

Axiom index_array_length : forall A (t : array A) i,
  index (length t) i -> index t i.

Hint Resolve index_array_length.

Hint Resolve bool_inhab.

Lemma conj_dup_r : forall P Q : Prop,
  Q -> (Q -> P) -> P /\ Q.
Proof. auto*. Qed.



(*-----------------------------------------------------------*)

Implicit Types V : array bool.
Implicit Types B : array len.
Implicit Types H : multiset (int*int).
Implicit Types p : path int.

Section Invariants.
Variables (G:graph int) (s:int).

(*-----------------------------------------------------------*)

Definition size_ok `{Inhab A} (T:array A) :=
  forall x, x \in nodes G -> index T x.

Hint Unfold size_ok.

(*-----------------------------------------------------------*)
Record inv_of z V B H reach : Prop := {
  Bdist: V\(z) = true -> B\(z) = dist G s z;
  Bbest: V\(z) = false -> B\(z) = mininf weight (reach z); 
  Hcorr: forall d, V\(z) = false -> (z,d) \in H -> exists p, reach z p /\ weight p = d;
  Hcomp: forall p, reach z p -> exists d, (z,d) \in H /\ d <= weight p }.

Record inv V B H reach : Prop := {
  Invof: forall z, z \in nodes G -> inv_of z V B H reach;
  SizeV: size_ok V;
  SizeB: size_ok B }.

Definition from_out V z p :=
  is_path G s z p /\ V\(z) = false.

Definition enters V z p :=
  from_out V z p /\ (p = nil \/ exists q y w, p = (y,z,w)::q /\ V\(y) = true).

Definition enters_via x L V z p :=
  from_out V z p /\ exists q w, p = (x,z,w)::q /\ Mem (z,w) L.

Definition new_enters x L V z p :=
  z <> x /\ (enters V z p \/ enters_via x L V z p).

Definition outgoing_edges x L :=
  forall y w, Mem (y,w) L = has_edge G x y w.

(*-----------------------------------------------------------*)

Section NewEnters.
Hint Unfold new_enters enters_via.

Lemma new_enters_nil : forall x V z, z <> x -> 
  new_enters x nil V z = enters V z.
Proof.
  intros. extens. intros p. unfold new_enters.
  iff (?&[?|((P&Vz)&(q&w&E&M))]) ?; auto*. inverts M.
Qed.
Lemma new_enters_not : forall x L V z y w, y <> z ->
  new_enters x ((y,w)::L) V z = new_enters x L V z.
Proof.
  intros. extens. intros p. iff (?&[?|(?&(q&w'&?&M))]).
   eauto 10. inverts M. false. eauto 10. eauto 10. eauto 10.
Qed.

Lemma new_enters_grows : forall x L V z p y w,
  new_enters x L V z p -> new_enters x ((y,w)::L) V z p.
Proof. introv (N&[H|(q&w'&?&?&M)]); eauto 10. Qed.

Lemma new_enters_inv : forall x L V z p y w,
  new_enters x ((y,w)::L) V z p -> 
      new_enters x L V z p 
   \/ (from_out V z p /\ exists q, p = (x,y,w)::q).
Proof. introv (N&[H|(P&(q&w'&E&M))]). eauto. inverts M; eauto 10. Qed.

End NewEnters.

(*-----------------------------------------------------------*)


Variables (NG:nonneg_edges G) (Ns:s \in nodes G).


Lemma value_nonneg_new_enters : forall x L V y,
  value_nonneg weight (new_enters x L V y).
Proof. introv [_ [((F&_)&_)|((F&_)&_)]]; apply* nonneg_edges_to_path. Qed.

Hint Resolve value_nonneg_new_enters.
Hint Resolve nonneg_edges_to_path.

Lemma from_out_in_nodes : forall V z p,
  from_out V z p -> z \in nodes G.
Proof. introv [F _]. apply* is_path_in_nodes_r. Qed.

Lemma from_out_cons_in_nodes : forall V z p y w q, 
  from_out V z p -> p = (y,z,w)::q -> y \in nodes G.
Proof. introv [F _] E. subst. inverts F. apply* is_path_in_nodes_r. Qed.

Lemma enters_in_nodes : forall V z p, 
  enters V z p -> z \in nodes G.
Proof. introv [F _]. apply* from_out_in_nodes. Qed.

Hint Resolve from_out_in_nodes from_out_cons_in_nodes enters_in_nodes.

Lemma enters_step : forall L V x, 
  V\(x) = false -> size_ok V -> x \in nodes G ->
  outgoing_edges x L ->
  new_enters x L V = enters (V\(x:=true)).
Proof.
  introv Vx SV Nx EQ. extens. intros z p. 
  asserts EF: (z \in nodes G -> z <> x -> from_out (V\(x:=true)) z p = from_out V z p).
    intros. unfold from_out. rew_array~.
  iff (Nzx&H) H.
   hnf in H. destruct H as [(F&[N|(q&y&w&E&Vy)])|(P&(q&w&E&M))];
    (split; [ rewrite* EF | ]).
     auto.
     right. exists q y w. split~. rew_array*. auto_false.
     right. exists q x w. rew_arr~.     
   asserts: (z <> x).
     intro_subst. lets ((_&E)&_): H. rew_arr~ in E. false.
    destruct H as (F&[N|(q&y&w&E&Vy)]).
      rewrite* EF in F. subst. split~. left. split~.
      rewrite* EF in F. tests (y = x); split~.
        right. split~. exists q w. split~. rewrite EQ. 
         subst p. applys* is_path_cons_has_edge (proj1 F).
        left. subst p. rew_array* in Vy. splits~. right*.
Qed.

Lemma enters_shorter : forall V z p, 
  is_path G s z p -> V\(z) = false -> 
  exists x q, enters V x q /\ weight q <= weight p.
Proof.
  introv P. set_eq s': s in P. set_eq G': G in P. 
  induction P; intros; subst. 
  exists s (nil:path int). splits_all~. apply le_refl.
  destruct (bool_test' (V\(y))).
    exists z ((y,z,w)::p). split. 
      split. split~.
      right. exists p y w. split~. math.
    forwards~ (x&q&E&L): IHP. exists x q. split~.
     rewrite weight_cons. forwards: NG H. math.    
Qed.

Lemma enters_best : forall V x p,
  V\(x) = false -> enters V x p -> 
  (forall y q, enters V y q -> weight p <= weight q) ->
  dist G s x = Finite (weight p).
Proof.
  introv Vx En BE. unfold dist.
  lets ((?&_)&_): En. applys~ (@mininf_finite (path int)) p.
  intros p' P'. forwards~ (y&q&E'&L): enters_shorter V P'.
   forwards: BE E'. math.
Qed.

Lemma dist_source : dist G s s = Finite 0.
Proof.
  applys~ (mininf_finite (nil:path int)).
  intros. apply* nonneg_edges_to_path.
Qed.

(*-----------------------------------------------------------*)

Lemma inv_start : forall n, 
  (forall x, x \in nodes G -> index n x) ->
  inv (make n false) (make n Infinite\(s:=Finite 0)) 
      ('{(s, 0)}) (enters (make n false)).
Proof.
  introv EQ.
  asserts Es: (enters (make n false) s nil).  splits~. splits~. rew_array~.
  constructors~; [| skip (*todo: size_ok*)].
  introv Nz. constructors~.
  introv Vi. rew_array~ in Vi. false.
  introv Vi. tests (z = s).
    rew_arr~. rewrite~ (mininf_finite (nil:path int)).    
     intros p ((?&?)&?). apply* nonneg_edges_to_path.
    rew_array~. rewrite~ mininf_infinite.
     intros p (P&[Pn|(q&y&w&Py&Ey)]).
       subst. destruct P as [P _]. inverts P. false.
       rew_array* in Ey.
  introv Vi E. multiset_in E. intros E. inverts E. exists~ (nil:path int).
  introv (P&[Pn|(q&y&w&Py&Ey)]). 
    exists 0. subst p. destruct P as [P _]. inverts P.
     split. multiset_in. rewrite weight_nil. math.
    rew_array* in Ey. false. 
Qed.

Axiom boolneg : forall b, !b -> b = false.
Hint Resolve boolneg.

Lemma inv_end_elim : forall x V B,
  inv V B \{} (enters V) -> 
  x \in nodes G ->
  B\(x) = dist G s x.
Proof.
  introv [Inv SB SV] Nx.
  tests (V\(x)) as C. applys* (Bdist (Inv _ Nx)).
  rewrite~ (Bbest (Inv _ Nx)). unfold dist.
  asserts Ne: (forall z p, z \in nodes G -> ~ enters V z p).
    introv Nz P. forwards* (d&N&_): (Hcomp (Inv _ Nz)). multiset_in N.
  apply (eq_trans' Infinite); rewrite~ mininf_infinite.
  intros p P. forwards* (z&q&Q&?): enters_shorter P. 
Qed.

Lemma size_ok_elim : forall `{Inhab A} (T:array A) x,
  size_ok T -> x \in nodes G -> index T x.
Proof. unfolds~ size_ok. Qed.
Hint Extern 1 (index _ _) => apply size_ok_elim.


Lemma inv_begin_loop : forall x d V B H H',
  H = '{(x,d)} \u H' -> 
  is_min_of H (x,d) ->
  x \in nodes G ->
  V\(x) = false ->
  inv V B H (enters V) ->
     inv (V\(x:=true)) B H' (new_enters x nil V)
  /\ Finite d = dist G s x.
Proof.
  introv EQ [In Mi] Nx Vx [Inv SB SV]. 
  asserts: (forall y q, enters V y q -> d <= weight q). 
    introv Ey. lets ((_&?)&_): Ey. specializes~ Inv (>> y __).  
    forwards* (d'&In'&?): (Hcomp Inv) Ey.
    lets Sy: Mi In'. skip: (d <= d'). math. (* todo with modules *)
  forwards* (p&En&W): Hcorr (Inv _ Nx).
  apply conj_dup_r. subst d. rewrite~ (@enters_best V x p).
  introv Dx. constructors~. introv Nz. forwards [Bd Bb Hc Hk]: Inv Nz.
  tests (z = x). constructors; rew_arr~; try solve[auto_false].
    intros _. rewrite~ Bb. subst d. rewrite* (mininf_finite p).
    introv En'. false~ (proj1 En').
  constructors; rew_array~.
    introv Vi. rewrite~ new_enters_nil.
    introv Vi Iz. rewrite~ new_enters_nil. 
     apply~ Hc. subst H. multiset_in.
    introv En'. lets: (proj1 En'). rewrite~ new_enters_nil in En'.
     forwards~ (dz&Hz&?): Hk En'. exists~ dz.
     subst H. multiset_in Hz; intros; tryfalse. split~.
Qed.

Lemma inv_end_loop : forall V x H B L,
  outgoing_edges x L ->
  x \in nodes G ->
  V\(x) = false ->
  inv (V\(x:=true)) B H (new_enters x L V) ->
  inv (V\(x:=true)) B H (enters (V\(x:=true))).
Proof.
  introv EL Nx Vx [Inv SB SV]. constructors~.
  introv Nz. lets [Bd Bb Hc Hk]: Inv Nz. tests (x = z).
  constructors.
    auto.
    rew_arr~; auto_false.
    rew_arr~; auto_false.
    introv En. lets ((_&N)&_): En. rew_arr~ in N. false.
  constructors.
    auto.
    rewrite~ enters_step in Bb.
     introv Vi Hzd. forwards~ (p&M&?): Hc Hzd. 
      exists p. split~. rewrite~ enters_step in M.
     introv En. apply Hk. rewrite~ enters_step.
Qed.

Lemma inv_update_le : forall L x y w dx dy V B H,
  x \in nodes G ->
  has_edge G x y w ->
  dy = dx + w ->
  Finite dx = dist G s x ->
  inv (V\(x:=true)) B H (new_enters x L V) -> 
  If len_gt (B\(y)) dy 
    then inv (V\(x:=true)) (B\(y:=Finite dy)) ('{(y, dy)} \u H) (new_enters x ((y,w)::L) V)
    else inv (V\(x:=true)) B H (new_enters x ((y, w)::L) V).
Proof.
  introv Nx Ed Dy Eq [Inv SB SV]. sets_eq V': (V\(x:=true)).
  cuts K: (forall_ z \in nodes G, 
    If len_gt (B\(y)) dy 
    then inv_of z V' (B\(y:=Finite dy)) ('{(y, dy)} \u H) (new_enters x ((y,w)::L) V)
    else inv_of z V' B H (new_enters x ((y, w)::L) V)).
    case_If; constructors~.
  introv Nz. lets [Bd Bb Hc Hk]: Inv Nz. tests (z = y).
  (* case z = y *)
  forwards~ (px&Px&Wx&Mx): (@mininf_finite_inv (path int)) (eq_sym Eq).
  sets p: ((x,y,w)::px). 
  asserts W: (weight p = dy). subst p. rewrite weight_cons. math. 
  tests (V'\(y)) as C; case_If as Nlt.
  (* subcase y visisted, distance improved *)
  false. rewrite~ Bd in Nlt. forwards M: mininf_len_gt Nlt p; subst p; auto.
   rewrite weight_cons in M. math.
  (* subcase y visisted, distance not improved *)
 (*
  rewrite Bb in Nlt. forwards~ (d&Md&Ld): mininf_len_gt_not Nlt.
  constructors.

  intros. auto.
 intros.
   forwards~ (q&Q&Wq&Mq): (@mininf_finite_inv (path int)) Md.
     rewrite~ Bd. .. rewrite~ (mininf_finite q).
      rewrite~ Wq. apply~ new_enters_grows.
      intros p Ep. rewrite Wq. lets [E|[(P'&Vy') (p'&Ep')]]: (new_enters_inv Ep).
        apply~ Mq.
        subst p. inverts P' as P' W. rewrite weight_cons. 
         forwards~ M: (@mininf_finite_elim (path int)) p' (eq_sym Eq). 
         math.

  false. rewrite~ Bd in Nlt. forwards M: mininf_len_gt Nlt p; subst p; auto.
   rewrite weight_cons in M. math.
*)
(*
  cuts_rewrite~ (new_enters x ((y,w)::L) V = new_enters x L V).
clears p.
   extens. intros z q. iff M. 
   destruct (new_enters_inv M) as [M'|M']. auto.
    inverts M'. inverts H0. destruct H1. subst q. inverts H2.
   tests (x= y). . rew_array~ in C. false.  
   apply~ new_enters_grows.
 *)

  skip.
  (* subcase y not visisted, distance improved *)
  asserts P: (new_enters x ((y, w) :: L) V y p).
    subst p. split. intro_subst. subst V'. rew_arr~ in C.
    right. split. split. auto.
    subst V'. tests (x = y). rew_arr~ in C. rew_array~ in C. exists___~. 
  constructors.
    intros. false. destruct (V'\(y)); false. (* todo fix *)
    introv Vi. rew_arr~. rewrite~ (mininf_finite p). rewrite~ W.
     intros q Enq. lets [E|[(P'&Vy') (p'&Ep)]]: (new_enters_inv Enq).
       rewrite~ Bb in Nlt. forwards~: mininf_len_gt Nlt E. math.
       subst q. rewrite weight_cons. inverts P' as Q' _. forwards: Mx Q'. math.
    introv Vi Iy. multiset_in Iy.
      introv E. inverts E. exists~ p.
      lets~ (p'&P'&Wp'): Hc H0. exists p'. split~. apply~ new_enters_grows.   
    intros py Ey. lets [E|[(P'&Vy') (p'&Ep)]]: (new_enters_inv Ey).
      forwards~ (d&D'&In'): Hcomp E. exists d. split~. multiset_in.
      subst py. inverts P' as P' W. rewrite weight_cons.
       exists dy. split~. multiset_in.
       forwards~ M: (@mininf_finite_elim (path int)) p' (eq_sym Eq). math.
  (* subcase y not visisted, distance not improved *)
  constructors.
    intros. false. destruct (V'\(y)); false. (* todo fix *)
    intros Vi. rewrite~ Bb in Nlt. forwards~ (d&Md&Ld): mininf_len_gt_not Nlt.
     forwards~ (q&Q&Wq&Mq): (@mininf_finite_inv (path int)) Md.
     rewrite~ Bb. rewrite Md. rewrite~ (mininf_finite q).
      rewrite~ Wq. apply~ new_enters_grows.
      intros p0 Ep0. rewrite Wq. lets [E|[(P'&Vy') (p'&Ep')]]: (new_enters_inv Ep0).
        apply~ Mq.
        subst p0. inverts P' as P' W. rewrite weight_cons. 
         forwards~ M: (@mininf_finite_elim (path int)) p' (eq_sym Eq). 
         math.
    introv Vi Iy. forwards~ (p0&P&Wp0): Hc Iy. exists p0. split~.
     apply~ new_enters_grows.   
    introv Ey. lets [E|[(P'&Vy') (p'&Ep)]]: (new_enters_inv Ey).
      applys Hk E.
      subst p0. inverts P' as P' W. rewrite weight_cons.
       forwards~ M: (@mininf_finite_elim (path int)) p' (eq_sym Eq). 
        rewrite~ Bb in Nlt. forwards~ (q&Q&Wq): mininf_len_gt_not_elim Nlt.
        lets (dy'&Iy&Wy): Hk Q. exists dy'. split~. math.    
  (* case z <> y *)
  case_If.
  constructors.
    intros. rew_array~.
    intros. rew_array~. rewrite~ new_enters_not. 
    introv Vi In. multiset_in In. auto_false. rewrite~ new_enters_not.
    introv En. rewrite~ new_enters_not in En. forwards (dz&Hz&?): Hk En.
     exists~ dz. split~. multiset_in.
  constructors; try solve [ auto | rewrite~ new_enters_not ].
Qed.

Lemma inv_no_update : forall V' B H x d,
  V'\(x) = true ->
  inv V' B ('{(x,d)}\u H) (enters V') ->
  inv V' B H (enters V').
Proof.
  introv Vx [Inv SB SV]. constructors~. introv Nz.
  lets [Bd Bb Hc Hk]: Inv Nz. constructors~.
    introv Vi In. apply~ Hcorr. multiset_in.
    introv En. forwards (d'&In&?): Hk En. lets ((_&?)&?): En.
     exists d'. split~. multiset_in In; auto_false.
Qed.

End Invariants.

(*-----------------------------------------------------------*)

Hint Unfold size_ok.


Lemma shortest_path_spec :
  Spec shortest_path g a b |R>> forall G,
    nonneg_edges G ->
    a \in nodes G ->
    b \in nodes G ->
    keep R (g ~> GraphAdjList G) (\= dist G a b).
Proof.
  xcf. introv Pos Ds De. unfold GraphAdjList at 1. hdata_simpl.
  xextract as N NG Adj. lets NG': (pred_ext_elim_l_0 NG).
  xapps. xapps. xapps. xapps. xapps*. xapps.
  set (data := fun B V H =>
    g ~> Array Id N \* v ~> Array Id V \* b ~> Array Id B \* h ~> Heap H
    \* [size_ok G B] \* [size_ok G V]).
  set (hinv := fun H:multiset(int*int) => 
    Hexists B V, data B V H \* [inv G s V B H (enters G s V)]).
  xseq (# hinv \{}). xwhile_inv (fun H:multiset(int*int) => 0%nat) hinv. 
    skip. (* todo: termination *)
    (* -- initial state satisfies invariant -- *)
    esplit. unfold hinv,data. hsimpl*. 
      applys_eq~ inv_start 2. permut_simpl.
    (* -- verification of the loop body -- *) 
    intros H. unfold hinv. xextract as B V Inv. 
     apply local_erase. esplit. splits.
    (* ---- loop condition -- *) 
    unfold data. xextract as SB SV. xframe ([size_ok G B] \*  [size_ok G V]); auto. (* todo *)
    xapps. xret.
    (* ---- loop body -- *) 
    xextract as HN SB SV. xapp. intros [x d] H' Mi HE. intro_subst.
    asserts: (x \in nodes G). (* todo : move *)
      lets: (Inv x). skip. (* todo: extract heap_complete *)
    xmatch. xapps~. xif; [ skip: (V\(x) = false) | ]. (* todo: cleanup *)
    (* ------ node treated -- *) 
    forwards~ [Inv' Dx]: inv_begin_loop HE Inv.
    xapps~. xfun_mg. xapps~.
    sets V': (V\(x:=true)).
    sets I: (fun L => Hexists L', Hexists B H, data B V' H (* todo bug when writing Hexists *)
        \* [inv G s V' B H (new_enters G s x L' V) ] \* [N\(x) = rev(L')++L]).
    xapp_manual. xapply (KR I); clear KR; match goal with |- context [update] => idtac | _ => clears update end.
    (* -------- verification of update -- *) 
    apply Supdate. xisspec. clears update. clear hinv. (* todo tactic *)
    unfold I at 1. hide I. unfold data. hide data. clears B H. 
    intros [y w] L. xextract as L' B H SB SV' Inv EQ.
    xmatch.
    asserts Ew: (has_edge G x y w). rewrite~ <- Adj. rewrite EQ. applys* Mem_app_or.
    asserts Ny: (y \in nodes G). applys~ has_edge_in_nodes_r x w. 
    xlet. xret. xextract as Dy. (* todo xret does xlet *)
    xapps~. xlet.
    xframe - []. xpost (\= istrue (len_gt (B\(y)) dy)).
    destruct (B\(y)); xgo~. 
    xok. xextracts. rewrite app_last in EQ. rewrite <- rev_cons in EQ.
    show_all. unfold I, data. xif.
    (* ---------- case smaller dist -- *) 
    xapps~. xapps~. hsimpl;eauto. applys* inv_update_gt d.
    (* ---------- case not smaller dist -- *)  
    xret. hsimpl;eauto. subst dy. applys~ inv_update_le d. 
    (* -------- iter pre-condition -- *) 
    unfold I. unfold data. hsimpl~ (nil:list (int*int)). xok.
    (* -------- iter post-condition -- *) 
    clears update. subst I.
    hextract as L B' H'' I' Leq. skip: (size_ok G B'). (* todo extract from data *)
     hsimpl~ H'' B' V'.
    skip. (* termination *)
    rew_app in Leq. applys~ inv_end_loop I'.
      hnf. intros. rewrite~ <- Adj. rewrite Leq. skip. (*apply Mem_rev.*)
    (* ------ node ignored -- *) 
    xret. unfold data. hsimpl*.
      skip. (*termination*) 
      skip: (V\(x) = true) . (* cleanup*)
    subst H. apply* inv_no_update. 
    (* ---- loop post-condition -- *) 
    hextract as He SB SV. fold_bool. rew_logic in He. subst H.
     unfold data. xsimpl~.
  (* ---- return value -- *) 
  unfold hinv, data. xextract as B V SB SV Inv.  
  xapp~. intros l. hdata_simpl GraphAdjList. xsimpl~.
  subst l. apply* inv_end_elim.
Qed.


(*-----------------------------------------------------------*)

(* todo: cleanup the boolean equalities *)
(* todo: prettyprint for  "let (x,y) =" and "fun (x,y) ="
(* todo: automate multiset_in *)
(* todo: try intro_subst_hyp should deal with tuples *)
(* todo: exists___~ into exists~. *)

(*-----------------------------------------------------------*)

End DijkstraSpec. 


