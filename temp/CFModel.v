Set Implicit Arguments.
Require Export LibCore LibEpsilon Shared.
Require Export CFHeaps.

Axiom heap_disjoint : heap -> heap -> Prop.


(********************************************************************)
(* ** Low-level axioms *)

(** The type Func *)

Axiom val : Type. 

(** The type Func is inhabited *)

Axiom val_inhab : Inhab val. 
Existing Instance val_inhab.

(** The evaluation predicate for functions: [eval f v h v' h'] *)

Axiom eval : forall A B, val -> A -> heap -> B -> heap -> Prop.

(** Evaluation is deterministic *)

Axiom eval_deterministic : forall A B f (v:A) h (v1' v2':B) h1' h2',
  eval f v h v1' h1' -> eval f v h v2' h2' -> v1' = v2' /\ h1' = h2'.
  

(********************************************************************)
(* ** High-level axioms *)

(** The predicate AppReturns *)

Definition app_1 A B (f:val) (x:A) (H:hprop) (Q:B->hprop) :=  
  forall h i, heap_disjoint h i -> H h -> 
    exists v' h' h'', (heap_disjoint h' i /\ heap_disjoint h'' i /\ heap_disjoint h'' h') /\ Q v' h' /\
      eval f x (heap_union h i) v' (heap_union h' (heap_union h'' i)).

(** The predicate AppPure *)

Definition pureapp A B f (x:A) (P:B->Prop) := 
  exists v:B, forall h, eval f x h v h /\ P v.

(** AppReturns is a local property *)

Lemma app_local_1 : forall B A1 (x1:A1) f,
  is_local (app_1 (B:=B) f x1).
Proof.
  intros. extens. intros H Q. iff M. apply~ local_erase.
  introv Dhi Hh. destruct (M h Hh) as (H1&H2&Q'&H'&D12&N&HQ).
  destruct D12 as (h1&h2&?&?&?&?).
  destruct~ (N h1 (heap_union i h2)) as (v'&h1'&i'&?&HQ'&E). 
  skip. (* disjoint *)
  sets h': (heap_union h1' h2).
  forwards Hh': (HQ v' h'). subst h'. exists___. splits~. skip. (* disjoint *)
  destruct Hh' as (h3'&h4'&?&?&?&?).
  exists v' h3' (heap_union h4' i'). splits.
    splits. skip. skip. skip. (* disjoint *) 
    auto.
    subst h h'. skip. (* union commute *)
Qed. 

(** AppPure satisfies the witness property *)

Lemma pureapp_concrete : forall A B (F:val) (V:A) (P:B->Prop),
  pureapp F V P <-> exists V', P V' /\ pureapp F V (= V').
Proof.
  iff H.
  destruct H as (V'&N). destruct (N heap_empty). exists V'. split~.
    exists V'. intros h. destruct (N h). split~.
  destruct H as (V'&?&N). destruct N as (V''&N).
    exists V'. intros h. destruct (N h). subst~.
Qed.

(** AppPure satisfies the determinacy property *)

Lemma pureapp_deterministic : forall A B (F:val) (V:A) (V1' V2':B),
  pureapp F V (= V1') -> pureapp F V (= V2') -> V1' = V2'.
Proof.
  introv (V1&N1) (V2&N2).
  destruct (N1 heap_empty). destruct (N2 heap_empty).
  subst. apply* eval_deterministic.
Qed.          

(** From AppPure to AppReturns *)

Lemma pureapp_to_app : forall A B (F:val) (V:A) (P:B->Prop),
  pureapp F V P -> app_1 F V [] \[P].
Proof.
  introv (v'&N). introv Dhi Hh. exists v' heap_empty heap_empty. splits.
  skip. (* heap_disjoint heap_empty *)
  destruct (N heap_empty). split~.
  hnf in Hh. subst. do 2 rewrite heap_union_neutral_l. destruct~ (N i).
Qed.

(** Overlapping of AppPure and AppReturns *)

Lemma pureapp_and_app : forall A B (F:val) (V:A) (V':B) (H:hprop) (Q:B->hprop) h,
  pureapp F V (= V') -> app_1 F V H Q -> H h -> exists H', (Q V' \* H') h.  (* H ==> Q V' \* H' *)
Proof.
  introv (V''&N) M Hh. destruct (N h) as (HE&?). clear N.
  subst. hnf in M. destruct (M h heap_empty) as (V''&h1&h2&?&HQ&HE'). 
    skip. (* disjoint *)
    auto.
    do 2 rewrite heap_union_neutral_r in HE'.
    forwards [? R]: (eval_deterministic HE HE'). exists (=h2). subst.
    destructs H0. exists h1 h2. splits~. skip. (* disjoint *)
Qed.




