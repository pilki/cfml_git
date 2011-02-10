Set Implicit Arguments.
Require Import CFLib Dijkstra_ml.
Open Scope comp_scope.
Require Import LibArray LibGraph MinInf.

(*************************************************************)
(** * More on graphs *)

Definition dist (g:graph int) x y :=  
  mininf weight (is_path g x y).

Definition nodes_index A (G:graph A) n :=
  forall x, x \in nodes G = index n x.

(** Representation predicate for graphs *)

Definition GraphAdjList (G:graph int) (g:loc) :=
  Hexists N, g ~> Array N
   \* [nodes_index G (LibArray.length N)]
   \* [forall x y w, x \in nodes G ->
         Mem (y,w) (N\(x)) = has_edge G x y w].


(*************************************************************)
(** Specification of ordered types *)

Module Type OrderedSigSpec.

Declare Module O : MLOrdered.
Import O.
Parameter T : Type.
Parameter S : htype T t.

Global Instance le_inst : Le T.
Global Instance le_order : Le_total_preorder.

Parameter le_spec : Spec le (x:t) (y:t) |R>> forall X Y,  
  keep R (x ~> S X \* y ~> S Y) (\= istrue (LibOrder.le X Y)).

Hint Extern 1 (RegisterSpec le) => Provide le_spec.

End OrderedSigSpec.


(*************************************************************)
(** Specification of priority queues *)

Definition is_min_of `{Le A} (E:multiset A) (X:A) := 
  X \in E /\ forall_ Y \in E, X <= Y.

Module Type MLPqueueSigSpec.

Declare Module Q : MLPqueueSig.
Declare Module OS : OrderedSigSpec with Module O := Q.MLElement.
Import Q MLElement OS. 

Parameter HeapOf : htype T t -> htype (multiset T) heap.

Notation "'Heap'" := (HeapOf Id).

Parameter create_spec :
  Spec create () |R>> 
    R [] (~> HeapOf S \{}).

Parameter is_empty_spec : 
  Spec is_empty (h:heap) |R>> forall E,
    keep R (h ~> HeapOf S E) (\= istrue (E = \{})).

Parameter push_spec : 
  Spec push (x:t) (h:heap) |R>> forall E X,
    R (h ~> HeapOf S E \* x ~> S X) (# h ~> HeapOf S (\{X} \u E)).

Parameter pop_spec : 
  Spec pop (h:heap) |R>> forall E,
    R (h ~> HeapOf S E) (fun x => Hexists X F, 
      [is_min_of E X] \* [E = \{X} \u F] \* x ~> S X \* h ~> HeapOf S F).

Hint Extern 1 (RegisterSpec create) => Provide create_spec.
Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.
Hint Extern 1 (RegisterSpec push) => Provide push_spec.
Hint Extern 1 (RegisterSpec pop) => Provide pop_spec.
End MLPqueueSigSpec.


(*************************************************************)
(** Verification of the module describing elements of the Pqueue *) 

Module MLNextNodeSpec <: OrderedSigSpec with Module O := MLNextNode.
Module O := MLNextNode.
Import O.
Definition T : Type := (int*int)%type.
Definition S : htype T t := Id.

Global Instance le_inst : Le T.
Proof.
  constructor.
  exact (fun (p1 p2 : int*int) => snd p1 <= snd p2).
Defined.
  
Global Instance le_order : Le_total_preorder.
Proof.
  constructors. constructors. 
  intros [x1 y1] [x2 y2] [x3 y3]. rapply (le_trans (A:=int)).
  intros [x1 y1] [x2 y2]. destruct~ (le_total y1 y2). 
Qed.

Lemma le_spec : Spec le (x:t) (y:t) |R>> forall X Y, 
  keep R (x ~> S X \* y ~> S Y) (\= istrue (LibOrder.le X Y)).
Proof.
  xcf. unfold S. intros x y X Y. xextract. intros. subst. xgo~.
Qed.

Hint Extern 1 (RegisterSpec le) => Provide le_spec.

End MLNextNodeSpec.

(*************************************************************)
(** Properties of [len], the data type representing distances *)

Global Instance len_inhab : Inhab len.
Proof. constructor. exact Infinite. Qed.
Hint Resolve len_inhab.


(*************************************************************)
(** Verification of Dijkstra's algorithm *)

Module DijkstraSpec.
Declare Module MLPqueue 
  : MLPqueueSig with Module MLElement := MLNextNode.
Declare Module MLPqueueSpec 
  : MLPqueueSigSpec with Module Q := MLPqueue
                    with Module OS := MLNextNodeSpec.
Import MLPqueue MLPqueueSpec MLNextNodeSpec.
Module Import Dijkstra := MLDijkstra MLPqueue.


(*-----------------------------------------------------------*)
(** ** Hints *)

(** Definition of the [~] and of the [*] symbols *)

Ltac auto_tilde ::= try solve [ auto ]. 
Ltac auto_star ::= try solve [ auto | jauto ]. 

(** Hints for multisets *)

Lemma multiset_in_union_single_eq_l : forall A (x:A) E F,
  E = \{x} \u F -> x \in E.
Proof. intros. subst. multiset_in. Qed.

Lemma multiset_in_union_single_eq_r : forall A (x y:A) E F,
  E = \{x} \u F -> y \in F-> y \in E.
Proof. introv M N. subst. multiset_in. Qed.

Hint Resolve multiset_in_union_single_eq_l multiset_in_union_single_eq_r.

Hint Extern 1 (_ \in _ \u _) => multiset_in.
Hint Extern 1 (_ \in \{_}) => multiset_in.

(** Hints for indices *)

Lemma graph_adj_index : forall B (G:graph B) n m x,
  nodes_index G n -> x \in nodes G -> n = m -> index m x.
Proof. introv N Nx L. subst. rewrite~ <- N. Qed.

Hint Resolve @index_array_length_eq @index_make @index_update.
Hint Extern 1 (nodes_index _ _) => congruence.
Hint Extern 1 (index ?n ?x) =>
  eapply graph_adj_index; 
  [ try eassumption 
  | instantiate; try eassumption
  | instantiate; try congruence ].

(** Other hints *)

Hint Constructors Mem is_path.

(*-----------------------------------------------------------*)
(** ** Implicit types and implicit parameters *)

Implicit Types V : array bool.
Implicit Types B : array len.
Implicit Types Q : multiset (int*int).
Implicit Types p : path int.

Section Invariants.
Variables (G:graph int) (n:int) (s:int).
Variables (Neg:nonneg_edges G) (Ind: nodes_index G n) (Ns:s \in nodes G).

(*-----------------------------------------------------------*)
(** ** Definition of the invariants *)

Record inv_of z V B Q reach : Prop := {
  Bdist: z \in nodes G -> isTrue (V\(z)) -> B\(z) = dist G s z;
  Bbest: z \in nodes G -> ~ isTrue (V\(z)) -> B\(z) = mininf weight (reach z); 
  Hcorr: forall d, (z,d) \in Q -> z \in nodes G /\
           (~ isTrue (V\(z)) -> exists p, reach z p /\ weight p = d);
  Hcomp: forall p, z \in nodes G -> reach z p -> exists d, (z,d) \in Q /\ d <= weight p }.

Record inv V B Q reach : Prop := {
  Invof: forall z, inv_of z V B Q reach;
  SizeV: length V = n;
  SizeB: length B = n }.

Definition from_out V z p :=
  is_path G s z p /\ ~ isTrue(V\(z)).

Definition crossing V z p :=
     from_out V z p 
  /\ (p = nil \/ exists q y w, p = (y,z,w)::q /\ isTrue(V\(y))).

Definition crossing_via x L V z p :=
  from_out V z p /\ exists q w, p = (x,z,w)::q /\ Mem (z,w) L.

Definition new_crossing x L V z p :=
  z <> x /\ (crossing V z p \/ crossing_via x L V z p).

Definition outgoing_edges x L :=
  forall y w, Mem (y,w) L = has_edge G x y w.

(*-----------------------------------------------------------*)
(** Properties of [dist], [crossing] and [new_crossing] *)

Lemma dist_source : dist G s s = Finite 0.
Proof.
  applys~ (mininf_finite (nil:path int)).
  intros. apply* nonneg_edges_to_path.
Qed.

Section NewCrossing.
Hint Unfold new_crossing crossing_via.

Lemma new_crossing_nil : forall x V z, z <> x -> 
  new_crossing x nil V z = crossing V z.
Proof.
  intros. extens. intros p. unfold new_crossing.
  iff (?&[?|((P&Vz)&(q&w&E&M))]) ?; auto*. inverts M.
Qed.
Lemma new_crossing_not : forall x L V z y w, y <> z ->
  new_crossing x ((y,w)::L) V z = new_crossing x L V z.
Proof.
  intros. extens. intros p. iff (?&[?|(?&(q&w'&?&M))]).
   eauto 10. inverts M. false. eauto 10. eauto 10. eauto 10.
Qed.

Lemma new_crossing_grows : forall x L V z p y w,
  new_crossing x L V z p -> new_crossing x ((y,w)::L) V z p.
Proof. introv (Nxz&[H|(q&w'&?&?&M)]); eauto 10. Qed.

Lemma new_crossing_inv : forall x L V z p y w,
  new_crossing x ((y,w)::L) V z p -> 
      new_crossing x L V z p 
   \/ (z <> x /\ from_out V z p /\ exists q, p = (x,y,w)::q).
Proof. introv (Nxz&[H|(P&(q&w'&E&M))]). eauto. inverts M; eauto 10. Qed.

End NewCrossing.

Lemma value_nonneg_new_crossing : forall x L V y,
  value_nonneg weight (new_crossing x L V y).
Proof. introv [_ [((F&_)&_)|((F&_)&_)]]; apply* nonneg_edges_to_path. Qed.

Hint Resolve value_nonneg_new_crossing.

Lemma from_out_in_nodes : forall V z p,
  from_out V z p -> z \in nodes G.
Proof. introv [F _]. apply* is_path_in_nodes_r. Qed.

Lemma from_out_cons_in_nodes : forall V z p y w q, 
  from_out V z p -> p = (y,z,w)::q -> y \in nodes G.
Proof. introv [F _] E. subst. inverts F. apply* is_path_in_nodes_r. Qed.

Lemma crossing_in_nodes : forall V z p, 
  crossing V z p -> z \in nodes G.
Proof. introv [F _]. apply* from_out_in_nodes. Qed.

Hint Resolve from_out_in_nodes from_out_cons_in_nodes crossing_in_nodes.

Lemma crossing_step : forall L V x, 
  ~ isTrue (V\(x)) -> length V = n -> x \in nodes G ->
  outgoing_edges x L ->
  new_crossing x L V = crossing (V\(x:=true)).
Proof.
  introv Vx SV Nx EQ. extens. intros z p. 
  asserts EF: (z \in nodes G -> z <> x -> from_out (V\(x:=true)) z p = from_out V z p).
    intros. unfold from_out. rew_array~.
  iff (Nzx&H) H.
   hnf in H. destruct H as [(F&[Nxz|(q&y&w&E&Vy)])|(P&(q&w&E&M))];
    (split; [ rewrite* EF | ]).
     auto.
     right. exists q y w. split~. rew_array*. auto_false.
     right. exists q x w. rew_arr~.     
   asserts: (z <> x).
     intro_subst. lets ((_&E)&_): H. rew_arr~ in E. 
    destruct H as (F&[Nxz|(q&y&w&E&Vy)]).
      rewrite* EF in F. subst. split~. left. split~.
      rewrite* EF in F. tests (y = x); split~.
        right. split~. exists q w. split~. rewrite EQ. 
         subst p. applys* is_path_cons_has_edge (proj1 F).
        left. subst p. rew_array* in Vy. splits~. right*.
Qed.

Lemma crossing_shorter : forall V z p, 
  is_path G s z p -> ~ isTrue (V\(z)) -> 
  exists x q, crossing V x q /\ weight q <= weight p.
Proof.
  introv P. set_eq s': s in P. set_eq G': G in P. 
  induction P; intros; subst. 
  exists s (nil:path int). splits_all~. apply le_refl.
  tests (V\(y)).
    exists z ((y,z,w)::p). split. 
      split. split~.
      right. exists p y w. split~. math.
    forwards~ (x&q&E&L): IHP. exists x q. split~.
     rewrite weight_cons. forwards: Neg H. math.    
Qed.

Lemma crossing_best : forall V x p,
  ~ isTrue (V\(x)) -> crossing V x p -> 
  (forall y q, crossing V y q -> weight p <= weight q) ->
  dist G s x = Finite (weight p).
Proof.
  introv Vx En BE. unfold dist.
  lets ((?&_)&_): En. applys~ (@mininf_finite (path int)) p.
  intros p' P'. forwards~ (y&q&E'&L): crossing_shorter V P'.
   forwards: BE E'. math.
Qed.

(*-----------------------------------------------------------*)
(** Properties of the invariant *)

Lemma inv_start : 
  (forall x, x \in nodes G -> index n x) ->
  inv (make n false) (make n Infinite\(s:=Finite 0)) 
      ('{(s, 0)}) (crossing (make n false)).
Proof.
  introv EQ. asserts Es: (crossing (make n false) s nil). 
    splits~. splits~. rew_array~.
  constructors. 
  intros z. constructors~.
  introv Nz Vi. rew_array~ in Vi. false.
  introv Nz Vi. tests (z = s).
    rew_arr~. rewrite~ (mininf_finite (nil:path int)).    
     intros p ((?&?)&?). apply* nonneg_edges_to_path.
    rew_array~. rewrite~ mininf_infinite.
     intros p (P&[Pn|(q&y&w&Py&Ey)]).
       subst. destruct P as [P _]. inverts P. false.
       rew_array* in Ey.
  introv E. multiset_in E. splits~. exists~ (nil:path int).
  introv Nz (P&[Pn|(q&y&w&Py&Ey)]). 
    exists 0. subst p. destruct P as [P _]. inverts P.
     split~. rewrite weight_nil. math.
    rew_array* in Ey. false. 
  rewrite~ length_make.
  rewrite~ length_update. rewrite~ length_make.
Qed.

Lemma inv_end_elim : forall x V B,
  inv V B \{} (crossing V) -> 
  x \in nodes G ->
  B\(x) = dist G s x.
Proof.
  introv [Inv SB SV] Nx. tests (V\(x)). applys* (Bdist (Inv x)).
  rewrite~ (Bbest (Inv x)). unfold dist.
  asserts Ne: (forall z p, z \in nodes G -> ~ crossing V z p).
    introv Nz P. forwards* (d&Na&_): (Hcomp (Inv z)). multiset_in Na.
  apply (eq_trans' Infinite); rewrite~ mininf_infinite.
  intros p P. forwards* (z&q&Q'&?): crossing_shorter P. 
Qed.

Lemma inv_begin_loop : forall x d V B Q Q',
  Q = '{(x,d)} \u Q' -> 
  is_min_of Q (x,d) ->
  x \in nodes G ->
  ~ isTrue (V\(x)) ->
  inv V B Q (crossing V) ->
     inv (V\(x:=true)) B Q' (new_crossing x nil V)
  /\ Finite d = dist G s x.
Proof.
  introv EQ [In Mi] Nx Vx [Inv SV SB]. 
  asserts: (forall y q, crossing V y q -> d <= weight q). 
    introv Ey. lets ((_&?)&_): Ey. specializes~ Inv y.  
    forwards* (d'&In'&?): (Hcomp Inv) Ey.
    lets Sy: Mi In'. asserts: (d <= d'). apply Sy. math.
  forwards* (_&p&En&W): Hcorr (Inv x).
  apply conj_dup_r. subst d. rewrite~ (@crossing_best V x p).
  introv Dx. constructors~. intros z. forwards [Bd Bb Hc Hk]: Inv z.
  tests (z = x). constructors; rew_arr~.
    intros _ _. rewrite~ Bb. subst d. rewrite* (mininf_finite p).
    auto_false.
    introv In'. split~. auto_false~.
    introv _ En'. false~ (proj1 En').
  constructors.
    introv Nz Vi. rew_array~ in Vi.
    introv Nz Vi. rew_array~ in Vi. rewrite~ new_crossing_nil.
    intros d' Iz. forwards [Nz Hcz]: Hc d'. eauto. split~.
     introv Vz. rew_array~ in Vz. rewrite~ new_crossing_nil.  
    introv Nz En'. lets: (proj1 En'). rewrite~ new_crossing_nil in En'.
     forwards~ (dz&Hz&?): Hk En'. exists~ dz.
     subst Q. multiset_in Hz; intros; tryfalse. split~.
Qed.

Lemma inv_end_loop : forall V x Q B L,
  outgoing_edges x L ->
  x \in nodes G ->
  ~ isTrue (V\(x)) ->
  inv (V\(x:=true)) B Q (new_crossing x L V) ->
  inv (V\(x:=true)) B Q (crossing (V\(x:=true))).
Proof.
  introv EL Nx Vx [Inv SV SB]. constructors~.
  intros z. lets [Bd Bb Hc Hk]: Inv z. tests (x = z).
  constructors.
    auto.
    rew_arr~; auto_false.
    introv Hd. forwards [? ?]: Hc Hd. split~. rew_arr~; auto_false.
    introv Nz En. lets ((_&N)&_): En. rew_arr~ in N. false.
  constructors.
    auto.
    rewrite~ crossing_step in Bb.
    introv Hzd. forwards~ [? M]: Hc Hzd. rewrite~ crossing_step in M.
    introv Nz En. apply~ Hk. rewrite~ crossing_step.
Qed.

Lemma inv_no_update : forall V' B Q x d,
  isTrue (V'\(x)) ->
  inv V' B ('{(x,d)}\u Q) (crossing V') ->
  inv V' B Q (crossing V').
Proof.
  introv Vx [Inv SB SV]. constructors~. intros z.
  lets [Bd Bb Hc Hk]: Inv z. constructors~.
    introv Nz En. forwards~ (d'&In&?): Hk En. lets~ ((_&?)&?): En.
     exists d'. split~. multiset_in In; auto_false.
Qed.

Lemma inv_update : forall L V B Q x y w dx dy,
  x \in nodes G ->
  has_edge G x y w ->
  dy = dx + w ->
  Finite dx = dist G s x ->
  inv (V\(x:=true)) B Q (new_crossing x L V) -> 
  If len_gt (B\(y)) dy 
    then inv (V\(x:=true)) (B\(y:=Finite dy)) (\{(y, dy)} \u Q) (new_crossing x ((y,w)::L) V)
    else inv (V\(x:=true)) B Q (new_crossing x ((y, w)::L) V).
Proof.
  introv Nx Ed Dy Eq [Inv SV SB]. sets_eq V': (V\(x:=true)).
  cuts K: (forall z, 
    If len_gt (B\(y)) dy 
    then inv_of z V' (B\(y:=Finite dy)) ('{(y, dy)} \u Q) (new_crossing x ((y,w)::L) V)
    else inv_of z V' B Q (new_crossing x ((y, w)::L) V)).
    case_If; constructors~.
  lets NegP: nonneg_edges_to_path Neg.
  intros z. lets [Bd Bb Hc Hk]: Inv z. tests (z = y).
  (* case z = y *)
  forwards~ (px&Px&Wx&Mx): (@mininf_finite_inv (path int)) (eq_sym Eq).
  lets Ny: (has_edge_in_nodes_r Ed).
  sets p: ((x,y,w)::px). 
  asserts W: (weight p = dy). subst p. rewrite weight_cons. math. 
  tests (V'\(y)) as C; case_If as Nlt.
  (* subcase y visisted, distance improved *)
  false. rewrite~ Bd in Nlt. forwards M: mininf_len_gt Nlt p; subst p; auto.
    rewrite weight_cons in M. math.
  (* subcase y visisted, distance not improved *)
  constructors; auto_false. 
  introv In. forwards [? ?]: Hc In. split~. auto_false.
  intros py _ Ey. lets [E|(Nxy&(P'&Vy')&(p'&Ep))]: (new_crossing_inv Ey).
    forwards~ (d&D'&In'): Hcomp E.
    subst V'. rew_array~ in C. auto_false.
  (* subcase y not visisted, distance improved *)
  asserts P: (new_crossing x ((y, w) :: L) V y p).
    subst p. split. intro_subst. subst V'. rew_arr~ in C.
    right. split. split. auto.
    subst V'. tests (x = y). rew_arr~ in C. rew_array~ in C. exists___~. 
  constructors.
    auto_false.
    introv Vi. rew_arr~. rewrite~ (mininf_finite p). rewrite~ W.
     intros q Enq. lets [E|(Nxy&(P'&Vy')&(p'&Ep))]: (new_crossing_inv Enq).
       rewrite~ Bb in Nlt. forwards~: mininf_len_gt Nlt E. math.
       subst q. rewrite weight_cons. inverts P' as Q' _. forwards: Mx Q'. math.
    introv Iy. split~. multiset_in Iy.
      introv E. inverts E. introv Vi. exists~ p.
      introv Vi. lets~ (_&p'&P'&Wp'): Hc H.
       exists p'. split~. apply~ new_crossing_grows.   
    intros py _ Ey. lets [E|(Nxy&(P'&Vy')&(p'&Ep))]: (new_crossing_inv Ey).
      forwards~ (d&D'&In'): Hcomp E. exists~ d.
      subst py. inverts P' as P' W. rewrite weight_cons. exists dy. split~.
       forwards~ M: (@mininf_finite_elim (path int)) p' (eq_sym Eq). math.
  (* subcase y not visisted, distance not improved *)
  constructors.
    auto_false.
    intros Vi. rewrite~ Bb in Nlt. forwards~ (d&Md&Ld): mininf_len_gt_not Nlt.
     forwards~ (p'&P'&Wq&Mq): (@mininf_finite_inv (path int)) Md.
     rewrite~ Bb. rewrite Md. rewrite~ (mininf_finite p').
      rewrite~ Wq. apply~ new_crossing_grows.
      intros p0 Ep0. rewrite Wq. lets~ [E|(Nxy&(Py&Vy')&(p''&Ep''))]: (new_crossing_inv Ep0).
        subst p0. inverts Py as Py W. rewrite weight_cons. 
         forwards~ M: (@mininf_finite_elim (path int)) p'' (eq_sym Eq). 
         math.
    introv Iy. forwards~ (_&p'&P'&Wp'): Hc Iy. split~. introv Vi. exists p'. split~.
     apply~ new_crossing_grows.   
    intros py _ Ey. lets [E|(Nxy&(Py&Vy')&(p'&Ep))]: (new_crossing_inv Ey).
      applys~ Hk E.
      subst py. inverts Py as Py W. rewrite weight_cons.
       forwards~ M: (@mininf_finite_elim (path int)) p' (eq_sym Eq). 
        rewrite~ Bb in Nlt. forwards~ (p''&Q''&Wq''): mininf_len_gt_not_elim Nlt.
        lets~ (dy'&Iy&Wy): Hk Q''. exists dy'. split~. math.    
  (* case z <> y *)
  case_If.
  constructors.
    intros. rew_array~.
    intros. rew_array~. rewrite~ new_crossing_not. 
    introv In. multiset_in In. intros; false. rewrite~ new_crossing_not.
    introv Nz En. rewrite~ new_crossing_not in En. 
     forwards~ (dz&Hz&?): Hk En. exists~ dz.
  constructors; try solve [ auto | rewrite~ new_crossing_not ].
Qed.

End Invariants.

(*-----------------------------------------------------------*)
(** Proof of Dijkstra's algorithm using the characteristic formula *)

Lemma shortest_path_spec :
  Spec shortest_path g a b |R>> forall G,
    nonneg_edges G ->
    a \in nodes G ->
    b \in nodes G ->
    keep R (g ~> GraphAdjList G) (\= dist G a b).
Proof.
  xcf. introv Pos Ns Ne. unfold GraphAdjList at 1. hdata_simpl. 
  xextract as N Neg Adj. xapp. intros Ln. rewrite <- Ln in Neg. 
  xapps. xapps. xapps. xapps*. xapps. 
  set (data := fun B V Q =>
    g ~> Array N \* v ~> Array V \* b ~> Array B \* q ~> Heap Q).
  set (hinv := fun VQ => let '(V,Q) := VQ in
    Hexists B, data B V Q \* [inv G n s V B Q (crossing G s V)]).
  xseq (# Hexists V, hinv (V,\{})). 
  set (W := lexico2 (binary_map (count (=true)) (upto (length N)))
                    (binary_map (fun Q:multiset(int*int) => card Q:int) (downto 0))).
  xwhile_inv W hinv. 
  (* -- initial state satisfies the invariant -- *)
  refine (ex_intro' (_,_)). unfold hinv,data. hsimpl.
    applys_eq~ inv_start 2. multiset_eq.
  (* -- verification of the loop -- *) 
  intros [V Q]. unfold hinv. xextract as B Inv. xwhile_inv_body. 
  (* ---- loop condition -- *) 
  unfold data. xapps. xret.
  (* ---- loop body -- *) 
  xextract as HN. xapp. intros [x dx] Q' Mi HE.
  unfold S. xextract. intro_subst. 
  lets [Inv' SV SB]: Inv. asserts Nx: (x \in nodes G).
    lets [_ _ Hc _]: Inv' x. forwards* [? _]: Hc dx.
  xmatch. xapps~. xif Vx. 
  (* ------ node treated -- *) 
  sets V': (V\(x:=true)). forwards~ [Inv'' Dx]: inv_begin_loop HE Inv. 
  sets hinv': (fun L => Hexists L', Hexists B Q, data B V' Q 
    \* [inv G n s V' B Q (new_crossing G s x L' V) ] \* [N\(x) = rev(L')++L]).
  xapps~. xfun. xapps~. xapp hinv'.
  (* -------- verification of update -- *) 
  intros m L. xapp_body. intros [y w]. intro_subst_hyp.
  clears B Q update hinv. unfold hinv' at 1. unfold data. 
  xextract as L' B Q Inv EQ. lets [_ _ SB]: Inv. sort. 
  asserts Ew: (has_edge G x y w). rewrite~ <- Adj. rewrite EQ. applys* Mem_app_or.
  asserts Ny: (y \in nodes G). applys* has_edge_in_nodes_r. hide_defs.
  xmatch. xret. xextract as Dy. xapps~. xlet.
  xframe - []. xpost (\= istrue (len_gt (B\(y)) dy)). xgo~.
   hsimpl. simpl. rewrite~ istrue_True. xok. xextracts. 
  rewrite app_last in EQ. rewrite <- rev_cons in EQ.
  unfold hinv', data. forwards~ K: inv_update s Ew Dy Inv.
  xif; case_If. xapps~. xapps~. xsimpl*. xret. xsimpl*.
  (* -------- iter pre-condition -- *) 
  subst hinv' data. hsimpl~ (nil:list (int*int)).
  (* -------- iter post-condition -- *) 
  clears update. subst hinv'.
  hextract as L B' Q'' I' Leq. hsimpl~ (V',Q'') B'.
  left. unfolds. subst V'. applys~ @array_count_upto. math.
  rew_app in Leq. applys~ inv_end_loop I'.
    hnf. intros. rewrite~ <- Adj. rewrite Leq. apply Mem_rev_eq.
  (* ------ node ignored -- *) 
  xret. unfold data. hsimpl (V,Q'). right. split~. hnf. subst Q.
    rewrite card_union, card_single. unfold T. math.
  subst Q. apply* inv_no_update. 
  (* ---- loop post-condition -- *) 
  hextract as He. xclean. subst Q. unfold data. xsimpl~.
  (* ---- return value -- *) 
  intros V B Inv. unfold hinv, data. lets [_ _ SB]: Inv.
  xapp~. intros l. hdata_simpl GraphAdjList. xsimpl~.
  subst l. apply* inv_end_elim.
Qed.


End DijkstraSpec. 

