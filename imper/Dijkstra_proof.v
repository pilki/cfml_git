
(*------------------------------------------------------------------*)
(* naturals extended with infinity *)

Inductive num : Set := 
  | Inf : num 
  | Val : nat -> num.

Definition num_add (d1 d2 : num) : num :=
  match d1,d2 with
  | Val v1, Val v2 => Val (v1 + v2)
  | _,_ => Inf
  end.

Definition num_le (d1 d2 : num) : bool :=
  match d1,d2 with
  | Val v1, Val v2 => nat_le v1 v2
  | _, Inf => true
  | Inf, _ => false
  end.

Definition num_min d1 d2 := 
  If (num_le d1 d2) then d1 else d2.

Notation "d1 +=+ d2" := (num_add d1 d2) (at level 68, d2 at level 80).
Notation "d1 <== d2" := (ok (num_le d1 d2)) (at level 68).


(*------------------------------------------------------------------*)
(* properties of num_le *)

Lemma num_le_refl : forall d, d <== d.

Lemma num_any_le_inf : forall d, d <== Inf.

Lemma num_inf_le_only_inf : forall d, Inf <== d -> Inf = d.

Lemma num_zero_le_any : forall d, Val 0 <== d.

Lemma num_le_trans : forall d2 d1 d3,
  d1 <== d2 -> d2 <== d3 -> d1 <== d3.

Lemma num_le_reverse : forall d1 d2, 
  no (num_le d1 d2) -> d2 <== d1.

Lemma num_le_antisym : forall d1 d2,
  d1 <== d2 -> d2 <== d1 -> d1 = d2.

Lemma num_le_add : forall d1 d2, 
  d1 <== (d1 +=+ d2).

Lemma num_le_add_both : forall d1 d2 d3, 
  d1 <== d2 -> (d1 +=+ d3) <== (d2 +=+ d3).

(*------------------------------------------------------------------*)
(* properties of num_min *)

Lemma num_min_swap : forall d1 d2, 
  num_min d1 d2 = num_min d2 d1.

Lemma num_min_if_le : forall d1 d2,
  d1 <== d2 -> num_min d1 d2 = d1.
Lemma num_min_le : forall d1 d2, num_min d1 d2 <== d1.

Lemma num_min_inf : forall d, num_min Inf d = d.

Lemma num_min_case : forall d1 d2,
  num_min d1 d2 = d1 \/ num_min d1 d2 = d2.

Lemma num_min_le_add : forall d1 d2, num_min d1 (d1 +=+ d2) = d1.

(*------------------------------------------------------------------*)
(* minimum over a set (in naturals extended with infinity) *)

Definition min_of_ d (K : Set) (eval : K -> num) (when : K -> Prop) 
  : Prop :=
     (d = Inf /\ (forall k, ~ (when k))
  \/ (   (forall k, when k -> d <== eval k)
      /\ (exists k : K, when k /\ d = eval k) )).

Notation "d 'min_of' f 'such_that' p" := (min_of_ d f p) 
  (at level 68).

Ltac min_of_empty k P :=
  left; split; [ idtac | intros k P ].

Ltac min_of_given p P E := 
  right; split; [intros p P | exists E; split ].

Lemma min_of_when : forall d K eval when k,
  min_of_ (K:=K) d eval when -> when k -> d <== eval k.
intros. destruct H as [[H1 H2] | [H1 H2]].
elim (H2 k H0). auto.
Qed.

Definition equivalent_when_or (K : Set) (f g h : K -> Prop) := 
  forall i : K, (f i -> h i) /\ (g i -> h i) /\ (h i -> f i \/ g i).

Lemma min_of_factorize : 
  forall K eval d1 d2 when1 when2,
  min_of_ (K:=K) d1 eval when1 -> 
  min_of_ (K:=K) d2 eval when2 -> 
  forall (when12 : K -> Prop),
   equivalent_when_or when1 when2 when12 ->
  min_of_ (K:=K) (num_min d1 d2) eval when12. 

(*------------------------------------------------------------------*)
(* axiomatization of indexed set (here called tables) *)

Parameter table : Set -> Set -> Set. 
Parameter table_get : forall (K A : Set) (k : K), table K A -> A.
Notation "t [ k ]" := (table_get k t) 
  (at level 68, right associativity). 

Parameter table_map : 
  forall (K A B : Set) (f : K -> A -> B), table K A -> table K B.
Axiom table_map_spec : 
   forall (K A B : Set) (f : K -> A -> B) (t : table K A) (k : K),
  (table_map f t)[k] = f k (t[k]).

Parameter table_init : forall (K A : Set) (f : K -> A), table K A.
Axiom table_init_spec : forall (K A : Set) (f : K -> A),
  forall k, (table_init f)[k] = f k.

(*------------------------------------------------------------------*)
(* arrays = set indexed by bounded naturals from 0 to size-1 *)

Inductive indices (size : nat) : Set :=
  | Index : forall i : nat, i <* size -> indices size.

Definition comp_indices size (a b : indices size) :=
  match a,b with Index i _, Index j _ => nat_eq i j end.

Definition array size := table (indices size).

(*------------------------------------------------------------------*)
(* axiomatization of (finite) sets of indices (from 0 to size-1) *)

Parameter indices_subset : nat -> Set.

Parameter indices_subset_has : forall size,
  indices_subset size -> indices size -> bool.

Parameter indices_subset_strict_incl : forall size,
  indices_subset size -> indices_subset size -> bool.

Axiom indices_subset_strict_incl_spec : 
  forall size (I J : indices_subset size),
  let has := indices_subset_has (size:=size) in
  ok (indices_subset_strict_incl I J) 
  <->
     (forall i : indices size, ok (has I i) -> ok (has J i))
  /\ (exists i : indices size, no (has I i) /\ ok (has J i)).

Parameter indices_subset_card : forall size, 
  indices_subset size -> nat.

Axiom indices_subset_strict_incl_card_lt : 
   forall size (I J : indices_subset size),
   ok (indices_subset_strict_incl I J) ->
   indices_subset_card I <* indices_subset_card J.


(*------------------------------------------------------------------*)
(* axiomatization of operations on arrays *)

Parameter array_filter : forall (size : nat) 
  (filter : indices size -> bool), indices_subset size.

Axiom array_filter_spec : forall size filter i,
  indices_subset_has (size:=size) (array_filter filter) i = filter i.

Definition array_count size (filter : indices size -> bool) :=
  indices_subset_card (array_filter filter).

Parameter array_find_min_num : forall size  
  (eval : indices size -> num) (filter : indices size -> bool),
  (indices size) * num.

Axiom array_find_min_num_spec : forall size eval filter imin dmin,
   (imin, dmin) = array_find_min_num (size:=size) eval filter ->
      dmin min_of eval such_that (fun i => ok (filter i))
  /\ (dmin = Inf  \/  (ok (filter imin) /\ dmin = eval imin)).


(*------------------------------------------------------------------*)
(* lemmas relating array_count and cardinality *)

Definition filter_stronger_strictly size f1 f2 := 
     (forall i : indices size, ok (f1 i) -> ok (f2 i))
  /\ (exists i : indices size, no (f1 i) /\ ok (f2 i)).

Lemma filter_implies_strict_count_lt :
  forall size (f1 f2 : indices size -> bool),
  filter_stronger_strictly f1 f2 ->
  array_count f1 <* array_count f2.
unfold filter_stronger_strictly, array_count.
intros size f1 f2 [H1 [e [E1 E2]]].
apply indices_subset_strict_incl_card_lt.
apply (proj2 (indices_subset_strict_incl_spec 
              (array_filter f1) (array_filter f2))). split. 
  intro i. do 2 rewrite array_filter_spec. auto.
  exists e. do 2 rewrite array_filter_spec. auto.
Qed.


(*------------------------------------------------------------------*)
(* definition of paths and shortest paths in a graph *)

Inductive path (K : Set) : K -> K -> Set :=
  | path_nil : forall i, path i i
  | path_cons : forall i j k, path i j -> path i k.

Definition Edges K := table K (table K num).

Fixpoint length (K : Set) (E : Edges K) (i j : K) (p : path i j)
  {struct p} : num := match p with
  | path_nil _ => Val 0
  | path_cons _ x y p' => (length E p') +=+ (E[x][y])
  end.

Definition shortest_path (K : Set) (E : Edges K) (i j : K) d :=
  d min_of (@length K E i j) such_that (fun p => True).

(*------------------------------------------------------------------*)
(*------------------------------------------------------------------*)
(*------------------------------------------------------------------*)

Section Dijkstra.

(*------------------------------------------------------------------*)
(* nodes are indexed from 0 to size-1 *)

Parameter (size : nat).
Parameter size_non_negative : (0 <* size).

Definition K := indices size.

(*------------------------------------------------------------------*)
(* input of the algorithm : source and edges *)

Parameter (source : K) (E : Edges K).

Notation "'spath'" := (path source).
Notation "'slength'" := (@length K E source).

(*------------------------------------------------------------------*)
(* state of the algorithm : an array of [treated * dist] *)

Definition state := table K (bool * num).
Definition shortest := (shortest_path E source).
Definition treated (N : state) (i : K) := fst (N[i]).
Definition dist    (N : state) (i : K) := snd (N[i]).

(*------------------------------------------------------------------*)
(* partial implementation of the algorithm in Coq *)

Definition start := table_init (fun k =>  
  (false, If K_eq k source then Val 0 else Inf)).

Definition final (N : state) := table_map (fun k v => snd v) N.

Definition select (N : state) :=
  array_find_min_num (dist N) (fun i => neg (treated N i)).

Definition update (N : state) imin dmin :=
  table_map (fun k (v : bool * num) => 
        ((fst v) || (K_eq k imin),
        num_min (snd v) (dmin +=+ E[imin][k]))
      ) N.


(* -- Dijsktra as we would like to write it

Fixpoint dijkstra_real (N : state) : table K num := 
  let (imin, dmin) := select N in
  If (is_eq_nat nb_left 0) || (is_eq_num dmin Inf)
    then final N 
    else dijkstra_real (update N imin dmin).
*)

(* -- Dijsktra that can compile in Coq 

Fixpoint dijkstra_coq (nb_left : nat) (N : state) 
                  {struct nb_left} : table K num := 
  let (imin, dmin) := select N in
  match nb_left with
  | 0 => final N
  | S p => if num_eq dmin Inf 
             then final N
             else dijkstra_coq p (update N imin dmin)
  end.

  with nb_left = array_count (fun i => neg (treated N i)).
*)

(*------------------------------------------------------------------*)
(* low-level specification of the code *)

Lemma start_spec : forall k,
    no (treated start k) 
 /\ dist start k = If K_eq k source then Val 0 else Inf.
unfold start, treated, dist. intros. 
rewrite table_init_spec. auto.
Qed.

Lemma select_spec : forall N imin dmin, (imin, dmin) = select N -> 
  dmin min_of (dist N) such_that (fun i => no (treated N i))
  /\ (dmin = Inf \/ (no (treated N imin) /\ dmin = dist N imin)).
intros. apply (array_find_min_num_spec H).
Qed.

Lemma final_spec : forall N k, (final N)[k] = dist N k.
unfold final. intros. rewrite table_map_spec. auto.
Qed.

Lemma update_spec : forall N imin dmin,
  let N' := update N imin dmin in
     (forall k, treated N' k = treated N k || (K_eq k imin))
  /\ (forall k, dist N' k = num_min (dist N k) (dmin +=+ E[imin][k])).
unfold update, treated, dist. split; intros;
rewrite table_map_spec; auto.
Qed.

(*------------------------------------------------------------------*)
(* global specification, invariant, and measure *) 

Definition dijkstra_output (R : table K num) :=
  forall k, shortest k (R[k]).

Definition path_direct N i p :=
  exists k : K, exists q : spath k,
     ok (treated N k) /\ p = path_cons i q.

Definition best_direct (N : state) i d := 
  d min_of (slength i) such_that (@path_direct N i).

Definition invariant (N : state) :=
  forall i, let d := dist N i in
    If (K_eq i source) then d = Val 0
    else If (treated N i) then shortest i d
    else best_direct N i d.

Definition measure (N : state) :=
  array_count (fun i => neg (treated N i)).


(*------------------------------------------------------------------*)
(* shortcuts to access to one of three parts of the invariant *)

Lemma inv_source : forall N, invariant N ->
  dist N source = Val 0.
unfold invariant. intros. generalize (H source).
rewrite (If_ok (K_eq_refl source)). auto.
Qed.

Lemma inv_treated : forall N k, invariant N ->
  no (K_eq k source) -> ok (treated N k) -> shortest k (dist N k).
unfold invariant. intros. generalize (H k).
rewrite (If_no H0). rewrite (If_ok H1). auto.
Qed.

Lemma inv_not_treated : forall N k, invariant N ->
  no (K_eq k source) -> no (treated N k) ->
  best_direct N k (dist N k).
unfold invariant. intros. generalize (H k).
rewrite (If_no H0). rewrite (If_no H1). auto.
Qed.


(*------------------------------------------------------------------*)
(* lemmas *)


Lemma path_from_not_treated_longer_than_dmin :
  forall N imin dmin, invariant N ->
  (imin,dmin) = select N -> 
  forall i (p : spath i), no (treated N i) -> 
  dmin <== length E p.

Lemma factorization_of_path_direct : 
  forall N imin dmin k,
  let when1 := path_direct N (i:=k) in 
  let when2 p := (exists q : spath imin, p = path_cons k q) in
  let when12 := path_direct (update N imin dmin) (i:=k) in
  equivalent_when_or when1 when2 when12.

Lemma dijkstra_initialize : invariant start.

Lemma dijkstra_case_final : forall N imin, 
  invariant N -> (imin,Inf) = select N ->
  dijkstra_output (final N).

Lemma dijkstra_case_step : forall N imin dmin, 
  invariant N -> (imin,dmin) = select N -> dmin <> Inf ->
  invariant (update N imin dmin).

Lemma dijkstra_terminates : forall N imin dmin,
  no (treated N imin) ->
  measure (update N imin dmin) <* measure N.

(*------------------------------------------------------------------*)
(* conclusion : dijkstra computes shortest paths from a source
   in finite time for any finite graph with at least one node. *)

Theorem dijkstra_correct : 
    invariant start 
 /\ forall N imin dmin, invariant N ->
      (imin,dmin) = select N -> 
      (dmin = Inf  /\ dijkstra_output (final N))
   \/ (dmin <> Inf /\ let N' := update N imin dmin in
        invariant N' /\ measure N' <* measure N).









(*------------------------------------------------------------------*)
(*             Formalization of Dijkstra's algorithm                *)
(*             Arthur Charguéraud      December 2006                *)
(*------------------------------------------------------------------*)

Set Implicit Arguments.
Require Import Bool.

(*------------------------------------------------------------------*)
(* general tactics *)

Ltac cuts H E := 
  cut (E); [ intro H | idtac ].
Ltac sets H E := 
  set (H := E); clearbody H.
Ltac poses H :=
  let N := fresh "HU" in sets N H.
Ltac asserts H E :=
  assert (H : E).
Ltac splits :=
  repeat split.
Ltac destructs H :=
  let H1 := fresh "H" in let H2 := fresh "H" in first 
  [ destruct H as [H1 H2]; destructs H1 ; destructs H2 | idtac ].
Ltac inversions H :=
  inversion H; subst.
Ltac injections H :=
  injection H; clear H; intros; subst.
Ltac contradictions :=
  assert False; [ auto | contradiction ].
Ltac generalizes H :=
   generalize H; clear H.
Tactic Notation "replaces" constr(a) "with" constr(b) :=
  let H := fresh "H" in
  asserts H (b = a); [ idtac | replace a with b; clear H ].

Ltac applya H := 
  apply H; auto.
Ltac autos :=
  simpl in *; auto.
Ltac use expr :=
  poses expr; autos.
Ltac use2 expr1 expr2 :=
  poses expr1; use expr2.
Ltac use3 expr1 expr2 expr3 :=
  poses expr1; poses expr2; use expr3.

Ltac func_equal := match goal with
  | [ |- (?F _ = ?F _ ) ] => apply (f_equal F)
  | [ |- (?F _ _ = ?F _ _) ] => apply (f_equal2 F)
  | [ |- (?F _ _ _ = ?F _ _ _) ] => apply (f_equal3 F)
  | [ |- (?F _ _ _ _ = ?F _ _ _ _) ] => apply (f_equal4 F)
  | _ => idtac
  end.


(*------------------------------------------------------------------*)
(* booleans reified *)

Definition ok P := (P = true).

Notation "'neg'" := (negb).

Notation "'no' P" := (ok (neg P)) (at level 68).

Hint Unfold ok.

Lemma ok_or_no : forall b, ok b \/ no b.
intros. destruct b; auto.
Qed.

Lemma ok_and_no_false : forall b, ok b -> no b -> False.
intros. rewrite H in H0. inversion H0.
Qed.

Ltac caseb H b :=
  destruct (ok_or_no b) as [H | H].

Ltac contradicts := 
  let doit H := (unfold ok in H; simpl in H; inversion H) in
  match goal with
  | H: no true |- _ => doit H
  | H: ok false |- _ => doit H
  | A: ok ?P, B: no ?P |- _ => elim (ok_and_no_false A B)
  end.

Ltac contradicts_on b := destruct b; contradicts.

Lemma no_to_false : forall b, no b -> b = false.
intros. destruct b. contradicts. auto.
Qed.

Tactic Notation "rewrite_no" constr(H) :=
  match type of H with no ?b =>
    rewrite (no_to_false b H) end.

Tactic Notation "rewrite_no" constr(H) "in" ident(P) :=
  match type of H with no ?b =>
    rewrite (no_to_false b H) in P end.


(*------------------------------------------------------------------*)
(* properties of boolean operators *)

Ltac proof_by_case_2 :=
   intros b1 b2; destruct b1; destruct b2; auto.

Lemma or_swap : forall b1 b2, (b1 || b2) = (b2 || b1).
proof_by_case_2.
Qed.

Lemma or_ok_case : forall b1 b2, ok (b1 || b2) -> ok b1 \/ ok b2.
proof_by_case_2.
Qed.

Lemma or_no_proj : forall b1 b2, no (b1 || b2) -> no b1.
proof_by_case_2.
Qed.

Lemma neg_neg : forall b, neg (neg b) = b.
destruct b; auto.
Qed.


(*------------------------------------------------------------------*)
(* If_then_else on booleans *)

Definition If_then_else b A (c d : A) :=
  match b with | true => c | false => d end.  

Notation "'If' b 'then' c 'else' d" := 
  (If_then_else b c d) (at level 68).

Hint Unfold If_then_else.

Lemma If_ok : forall b (H : ok b) A (c d : A), 
  If b then c else d = c.
intros. rewrite H. auto.
Qed.

Lemma If_no_ : forall b (H : no b) A (c d : A), 
  If b then c else d = d.
intros. rewrite (no_to_false b H). auto.
Qed.

Notation "'If_no'" := (If_no_ _) (at level 68).

Ltac case_If H b :=
  caseb H b; [ repeat (rewrite (If_ok H)) 
             |  repeat (rewrite (If_no H)) ].

Ltac assume_neg H :=
  match goal with
  |- ok ?E => caseb H E; 
    [ exact H | try rewrite neg_neg in H; contradictions ]
  end.


(*------------------------------------------------------------------*)
(* comparison functions equivalent to Leibnitz' equality *)

Definition to_eq (A : Set) (comp : A -> A -> bool) :=
  forall (a b : A), ok (comp a b) -> a = b.

Definition to_neq (A : Set) (comp : A -> A -> bool) :=
  forall (a b : A), no (comp a b) -> a <> b.


(*------------------------------------------------------------------*)
(* booleans *)

Definition bool_eq b1 b2 := 
  match b1, b2 with
  | true, true => true
  | false, false => true
  | _ , _ => false
  end.

Lemma bool_eq_to_eq : to_eq bool_eq.
unfold to_eq. intros. destruct a; destruct b; auto.
Qed.

Lemma bool_neq_to_neq : to_neq bool_eq.
unfold to_neq. intros. destruct a; destruct b; autos.
intro E. inversion E. contradicts.
Qed.


(*------------------------------------------------------------------*)
(* naturals *)

Fixpoint nat_eq (n1 n2 : nat) {struct n1} : bool :=
  match n1, n2 with
  | O, O => true
  | S p1, S p2 => nat_eq p1 p2
  | _ , _ => false
  end.

Lemma nat_eq_to_eq : to_eq nat_eq.
unfold to_eq. intro a. induction a; intros b H; destruct b; 
simpl in H; first [ contradicts | func_equal; auto ].
Qed.

Lemma nat_neq_to_neq : to_neq nat_eq.
unfold to_neq. intro a. induction a; intros b H; destruct b; 
simpl in H; auto. contradicts.
Qed.

Lemma nat_eq_refl : forall i, ok (nat_eq i i).
induction i; autos. 
Qed.

Fixpoint nat_le (n1 n2 : nat) {struct n1} : bool :=
  match n1, n2 with
  | O, O => true
  | S p1, S p2 => nat_le p1 p2
  | O, S p => true
  | _ , _ => false
  end.

Definition nat_lt (n1 n2 : nat) : bool :=
  nat_le n1 n2 && neg (nat_eq n1 n2).


Notation "n1 *= n2" := (ok (nat_eq n1 n2)) 
                        (at level 68, d2 at level 80).

Notation "n1 <*> n2" := (no (nat_eq n1 n2)) 
                        (at level 68, d2 at level 80).

Notation "n1 <*= n2" := (ok (nat_le n1 n2)) 
                        (at level 68, d2 at level 80).

Notation "n1 <* n2" := (ok (nat_lt n1 n2)) 
                       (at level 68, d2 at level 69).


(*------------------------------------------------------------------*)
(* properties of nat_le *)

Lemma nat_le_refl : forall n, ok (nat_le n n).
intros. induction n; auto.
Qed.

  (* trivial but tedious standard lemmas left as axioms *)

Axiom nat_le_trans : forall a b c, 
  ok (nat_le a b) -> ok (nat_le b c) -> ok (nat_le a c).

Axiom nat_le_reverse : forall n1 n2, 
  no (nat_le n1 n2) -> ok (nat_le n2 n1).

Axiom nat_le_antisym : forall n1 n2,
  ok (nat_le n1 n2) -> ok (nat_le n2 n1) -> n1 = n2.

Axiom nat_le_le_add : forall d1 d2,
  ok (nat_le d1 (d1 + d2)).

Axiom nat_le_add_both : forall n1 n2 n3, 
  ok (nat_le n1 n2) -> ok (nat_le (n1 + n3) (n2 + n3)).


(*------------------------------------------------------------------*)
(* naturals extended with infinity *)

Inductive num : Set := 
  | Inf : num 
  | Val : nat -> num.

Definition num_eq d1 d2 :=
  match d1, d2 with
  | Inf, Inf => true
  | Val v1, Val v2 => nat_eq v1 v2
  | _ , _ => false
  end.

Lemma num_eq_to_eq : to_eq num_eq.
unfold to_eq. intros. destruct a; destruct b; 
autos; try contradicts. use nat_eq_to_eq.
Qed.

Lemma num_neq_to_neq : to_neq nat_eq.
unfold to_neq. intros. destruct a; destruct b; 
autos; try contradicts. use nat_neq_to_neq.
Qed.

Definition num_add (d1 d2 : num) : num :=
  match d1,d2 with
  | Val v1, Val v2 => Val (v1 + v2)
  | _,_ => Inf
  end.

Definition num_le (d1 d2 : num) : bool :=
  match d1,d2 with
  | Val v1, Val v2 => nat_le v1 v2
  | _, Inf => true
  | Inf, _ => false
  end.

Definition num_min d1 d2 := 
  If (num_le d1 d2) then d1 else d2.

Notation "d1 +=+ d2" := (num_add d1 d2) (at level 68, d2 at level 80).
Notation "d1 <== d2" := (ok (num_le d1 d2)) (at level 68).


(*------------------------------------------------------------------*)
(* properties of num_le *)

Lemma num_le_refl : forall d, d <== d.
destruct d. auto. use nat_le_refl.
Qed.

Lemma num_any_le_inf : forall d, d <== Inf.
destruct d; auto.
Qed.

Lemma num_inf_le_only_inf : forall d, Inf <== d -> Inf = d.
destruct d. auto. intro H. inversion H.
Qed.

Lemma num_zero_le_any : forall d, Val 0 <== d.
destruct d. auto. destruct n; auto.
Qed.

Lemma num_le_trans : forall d2 d1 d3,
  d1 <== d2 -> d2 <== d3 -> d1 <== d3.
intros d2 d1 d3.
destruct d1; destruct d2; destruct d3; intros; auto.
inversion H0. use (nat_le_trans n n0 n1).
Qed.

Lemma num_le_reverse : forall d1 d2, 
  no (num_le d1 d2) -> d2 <== d1.
intros. destruct d1; destruct d2; autos. 
applya nat_le_reverse.
Qed.

Lemma num_le_antisym : forall d1 d2,
  d1 <== d2 -> d2 <== d1 -> d1 = d2.
 unfold num_le. intros.
destruct d1; destruct d2; try contradicts; auto.
func_equal. applya nat_le_antisym.
Qed.

Lemma num_le_add : forall d1 d2, 
  d1 <== (d1 +=+ d2).
destruct d1; destruct d2; auto.
unfold num_add, num_le.
apply nat_le_le_add.
Qed.

Lemma num_le_add_both : forall d1 d2 d3, 
  d1 <== d2 -> (d1 +=+ d3) <== (d2 +=+ d3).
destruct d1; destruct d2; simpl; intros.
auto. contradicts. apply num_any_le_inf.
destruct d3. auto. simpl. applya nat_le_add_both.
Qed.


(*------------------------------------------------------------------*)
(* properties of num_min *)

Lemma num_min_swap : forall d1 d2, 
  num_min d1 d2 = num_min d2 d1.
intros. destruct d1; destruct d2; autos. 
unfold num_min.
case_If H1 (num_le (Val n) (Val n0));
case_If H2 (num_le (Val n0) (Val n)); auto.
applya num_le_antisym.
poses (num_le_reverse (Val n) (Val n0) H1).
poses (num_le_reverse (Val n0) (Val n) H2).
applya num_le_antisym.
Qed.

Lemma num_min_if_le : forall d1 d2,
  d1 <== d2 -> num_min d1 d2 = d1.
intros. unfold num_min. rewrite H. auto.
Qed.

Lemma num_min_le : forall d1 d2, num_min d1 d2 <== d1.
intros. unfold num_min. case_If H (num_le d1 d2). 
apply num_le_refl. applya num_le_reverse.
Qed. 

Lemma num_min_inf : forall d, num_min Inf d = d.
intros. destruct d; auto.
Qed.

Lemma num_min_case : forall d1 d2,
  num_min d1 d2 = d1 \/ num_min d1 d2 = d2.
intros. unfold num_min. caseb H (num_le d1 d2). 
  left. rewrite (If_ok H). auto.
  right. rewrite (If_no H). auto.
Qed.

Lemma num_min_le_add : forall d1 d2, num_min d1 (d1 +=+ d2) = d1.
intros. destruct d1; destruct d2; auto.
unfold num_min. rewrite num_le_add. auto.
Qed.


(*------------------------------------------------------------------*)
(* minimum over a set (in naturals extended with infinity) *)

Definition min_of_ d (K : Set) (eval : K -> num) (when : K -> Prop) 
  : Prop :=
     (d = Inf /\ (forall k, ~ (when k))
  \/ (   (forall k, when k -> d <== eval k)
      /\ (exists k : K, when k /\ d = eval k) )).

Notation "d 'min_of' f 'such_that' p" := (min_of_ d f p) 
  (at level 68).

Ltac min_of_empty k P :=
  left; split; [ idtac | intros k P ].

Ltac min_of_given p P E := 
  right; split; [intros p P | exists E; split ].

Lemma min_of_when : forall d K eval when k,
  min_of_ (K:=K) d eval when -> when k -> d <== eval k.
intros. destruct H as [[H1 H2] | [H1 H2]].
elim (H2 k H0). auto.
Qed.

Definition equivalent_when_or (K : Set) (f g h : K -> Prop) := 
  forall i : K, (f i -> h i) /\ (g i -> h i) /\ (h i -> f i \/ g i).

Lemma min_of_factorize : 
  forall K eval d1 d2 when1 when2,
  min_of_ (K:=K) d1 eval when1 -> 
  min_of_ (K:=K) d2 eval when2 -> 
  forall (when12 : K -> Prop),
   equivalent_when_or when1 when2 when12 ->
  min_of_ (K:=K) (num_min d1 d2) eval when12. 
intros K eval d1 d2 when1 when2 A1 A2 when12 P.
destruct A1 as [[G1 H1] | [G1 H1]];
destruct A2 as [[G2 H2] | [G2 H2]].
  (* none, none *)
  rewrite G1. rewrite G2. left. intuition eauto.
  poses (P k). intuition eauto.
  (* none, some *) 
  rewrite G1. rewrite num_min_inf. 
  destruct H2. right. poses (P x). intuition eauto.
  poses (P k). intuition eauto.
  (* some, none *) 
  rewrite G2. rewrite num_min_swap. rewrite num_min_inf. 
  destruct H1. right. poses (P x). intuition eauto.
  poses (P k). intuition eauto.
  (* some, some *)
  destruct H1 as [k1 [W1 E1]]. destruct H2 as [k2 [W2 E2]]. 
  right. split.
  intros k W. destruct (P k) as [A [B C]]. destruct (C W).
     apply (num_le_trans d1). apply num_min_le. eauto.  
     apply (num_le_trans d2). rewrite num_min_swap. 
      apply num_min_le. eauto.
    destruct (num_min_case d1 d2).  
      exists k1. rewrite <- E1. poses (P k1). intuition auto. 
      exists k2. rewrite <- E2. poses (P k2). intuition auto. 
Qed.


(*------------------------------------------------------------------*)
(* axiomatization of indexed set (here called tables) *)

Parameter table : Set -> Set -> Set. 
Parameter table_get : forall (K A : Set) (k : K), table K A -> A.
Notation "t [ k ]" := (table_get k t) 
  (at level 68, right associativity). 

Parameter table_map : 
  forall (K A B : Set) (f : K -> A -> B), table K A -> table K B.
Axiom table_map_spec : 
   forall (K A B : Set) (f : K -> A -> B) (t : table K A) (k : K),
  (table_map f t)[k] = f k (t[k]).

Parameter table_init : forall (K A : Set) (f : K -> A), table K A.
Axiom table_init_spec : forall (K A : Set) (f : K -> A),
  forall k, (table_init f)[k] = f k.


(*------------------------------------------------------------------*)
(* arrays = set indexed by bounded naturals from 0 to size-1 *)

Inductive indices (size : nat) : Set :=
  | Index : forall i : nat, i <* size -> indices size.

Definition comp_indices size (a b : indices size) :=
  match a,b with Index i _, Index j _ => nat_eq i j end.

Definition array size := table (indices size).

(* here we need a little "classical" hack to be able to say that 
   two indices are Leibnitz equal when their comparison returns true *)
   Require Import ProofIrrelevance.
   Axiom classical : forall A : Prop, A \/ ~ A.

Lemma comp_indices_to_eq : forall size, to_eq (@comp_indices size).
intros size a b H. destruct a; destruct b. simpl in H.
generalize o o0. clear o o0. 
rewrite (nat_eq_to_eq i i0 H). intros.
rewrite (proof_irrelevance_cci classical (i0 <* size) o o0). auto.
Qed.

(* end of little hack *)


(*------------------------------------------------------------------*)
(* axiomatization of (finite) sets of indices (from 0 to size-1) *)

Parameter indices_subset : nat -> Set.

Parameter indices_subset_has : forall size,
  indices_subset size -> indices size -> bool.

Parameter indices_subset_strict_incl : forall size,
  indices_subset size -> indices_subset size -> bool.

Axiom indices_subset_strict_incl_spec : 
  forall size (I J : indices_subset size),
  let has := indices_subset_has (size:=size) in
  ok (indices_subset_strict_incl I J) 
  <->
     (forall i : indices size, ok (has I i) -> ok (has J i))
  /\ (exists i : indices size, no (has I i) /\ ok (has J i)).

Parameter indices_subset_card : forall size, 
  indices_subset size -> nat.

Axiom indices_subset_strict_incl_card_lt : 
   forall size (I J : indices_subset size),
   ok (indices_subset_strict_incl I J) ->
   indices_subset_card I <* indices_subset_card J.


(*------------------------------------------------------------------*)
(* axiomatization of operations on arrays *)

Parameter array_filter : forall (size : nat) 
  (filter : indices size -> bool), indices_subset size.

Axiom array_filter_spec : forall size filter i,
  indices_subset_has (size:=size) (array_filter filter) i = filter i.

Definition array_count size (filter : indices size -> bool) :=
  indices_subset_card (array_filter filter).

Parameter array_find_min_num : forall size  
  (eval : indices size -> num) (filter : indices size -> bool),
  (indices size) * num.

Axiom array_find_min_num_spec : forall size eval filter imin dmin,
   (imin, dmin) = array_find_min_num (size:=size) eval filter ->
      dmin min_of eval such_that (fun i => ok (filter i))
  /\ (dmin = Inf  \/  (ok (filter imin) /\ dmin = eval imin)).


(*------------------------------------------------------------------*)
(* lemmas relating array_count and cardinality *)

Definition filter_stronger_strictly size f1 f2 := 
     (forall i : indices size, ok (f1 i) -> ok (f2 i))
  /\ (exists i : indices size, no (f1 i) /\ ok (f2 i)).

Lemma filter_implies_strict_count_lt :
  forall size (f1 f2 : indices size -> bool),
  filter_stronger_strictly f1 f2 ->
  array_count f1 <* array_count f2.
unfold filter_stronger_strictly, array_count.
intros size f1 f2 [H1 [e [E1 E2]]].
apply indices_subset_strict_incl_card_lt.
apply (proj2 (indices_subset_strict_incl_spec 
              (array_filter f1) (array_filter f2))). split. 
  intro i. do 2 rewrite array_filter_spec. auto.
  exists e. do 2 rewrite array_filter_spec. auto.
Qed.


(*------------------------------------------------------------------*)
(* definition of paths and shortest paths in a graph *)

Inductive path (K : Set) : K -> K -> Set :=
  | path_nil : forall i, path i i
  | path_cons : forall i j k, path i j -> path i k.

Definition Edges K := table K (table K num).

Fixpoint length (K : Set) (E : Edges K) (i j : K) (p : path i j)
  {struct p} : num := match p with
  | path_nil _ => Val 0
  | path_cons _ x y p' => (length E p') +=+ (E[x][y])
  end.

Definition shortest_path (K : Set) (E : Edges K) (i j : K) d :=
  d min_of (@length K E i j) such_that (fun p => True).


(*------------------------------------------------------------------*)
(*------------------------------------------------------------------*)
(*------------------------------------------------------------------*)

Section Dijkstra.

(*------------------------------------------------------------------*)
(* nodes are indexed from 0 to size-1 *)

Parameter (size : nat).
Parameter size_non_negative : (0 <* size).

Definition K := indices size.
Definition K_eq := (@comp_indices size).

Lemma K_eq_to_eq : to_eq K_eq.
unfold K_eq. apply comp_indices_to_eq.
Qed.

Lemma K_eq_refl : forall i, ok (K_eq i i).
destruct i. unfold K_eq, comp_indices. apply nat_eq_refl.
Qed.

Tactic Notation "rewrite_K_eq" ident(H) :=
  match type of H with ok (K_eq ?a ?b) =>
    rewrite (K_eq_to_eq a b H) end.

Tactic Notation "rewrite_K_eq" ident(H) "in" ident(P) :=
  match type of H with ok (K_eq ?a ?b) =>
    rewrite (K_eq_to_eq a b H) in P end.

Tactic Notation "rewrite_K_eq" "<-" ident(H) :=
  match type of H with ok (K_eq ?a ?b) =>
    rewrite <- (K_eq_to_eq a b H) end.


(*------------------------------------------------------------------*)
(* input of the algorithm : source and edges *)

Parameter (source : K) (E : Edges K).

Notation "'spath'" := (path source).
Notation "'slength'" := (@length K E source).


(*------------------------------------------------------------------*)
(* state of the algorithm : an array of [treated * dist] *)

Definition state := table K (bool * num).
Definition shortest := (shortest_path E source).
Definition treated (N : state) (i : K) := fst (N[i]).
Definition dist    (N : state) (i : K) := snd (N[i]).


(*------------------------------------------------------------------*)
(* partial implementation of the algorithm in Coq *)

Definition start := table_init (fun k =>  
  (false, If K_eq k source then Val 0 else Inf)).

Definition final (N : state) := table_map (fun k v => snd v) N.

Definition select (N : state) :=
  array_find_min_num (dist N) (fun i => neg (treated N i)).

Definition update (N : state) imin dmin :=
  table_map (fun k (v : bool * num) => 
        ((fst v) || (K_eq k imin),
        num_min (snd v) (dmin +=+ E[imin][k]))
      ) N.


(* -- Dijsktra as we would like to write it

Fixpoint dijkstra_real (N : state) : table K num := 
  let (imin, dmin) := select N in
  If (is_eq_nat nb_left 0) || (is_eq_num dmin Inf)
    then final N 
    else dijkstra_real (update N imin dmin).
*)

(* -- Dijsktra that can compile in Coq 

Fixpoint dijkstra_coq (nb_left : nat) (N : state) 
                  {struct nb_left} : table K num := 
  let (imin, dmin) := select N in
  match nb_left with
  | 0 => final N
  | S p => if num_eq dmin Inf 
             then final N
             else dijkstra_coq p (update N imin dmin)
  end.

  with nb_left = array_count (fun i => neg (treated N i)).
*)


(*------------------------------------------------------------------*)
(* low-level specification of the code *)

Lemma start_spec : forall k,
    no (treated start k) 
 /\ dist start k = If K_eq k source then Val 0 else Inf.
unfold start, treated, dist. intros. 
rewrite table_init_spec. auto.
Qed.

Lemma select_spec : forall N imin dmin, (imin, dmin) = select N -> 
  dmin min_of (dist N) such_that (fun i => no (treated N i))
  /\ (dmin = Inf \/ (no (treated N imin) /\ dmin = dist N imin)).
intros. apply (array_find_min_num_spec H).
Qed.

Lemma final_spec : forall N k, (final N)[k] = dist N k.
unfold final. intros. rewrite table_map_spec. auto.
Qed.

Lemma update_spec : forall N imin dmin,
  let N' := update N imin dmin in
     (forall k, treated N' k = treated N k || (K_eq k imin))
  /\ (forall k, dist N' k = num_min (dist N k) (dmin +=+ E[imin][k])).
unfold update, treated, dist. split; intros;
rewrite table_map_spec; auto.
Qed.


(*------------------------------------------------------------------*)
(* global specification, invariant, and measure *) 

Definition dijkstra_output (R : table K num) :=
  forall k, shortest k (R[k]).

Definition path_direct N i p :=
  exists k : K, exists q : spath k,
     ok (treated N k) /\ p = path_cons i q.

Definition best_direct (N : state) i d := 
  d min_of (slength i) such_that (@path_direct N i).

Definition invariant (N : state) :=
  forall i, let d := dist N i in
    If (K_eq i source) then d = Val 0
    else If (treated N i) then shortest i d
    else best_direct N i d.

Definition measure (N : state) :=
  array_count (fun i => neg (treated N i)).


(*------------------------------------------------------------------*)
(* shortcuts to access to one of three parts of the invariant *)

Lemma inv_source : forall N, invariant N ->
  dist N source = Val 0.
unfold invariant. intros. generalize (H source).
rewrite (If_ok (K_eq_refl source)). auto.
Qed.

Lemma inv_treated : forall N k, invariant N ->
  no (K_eq k source) -> ok (treated N k) -> shortest k (dist N k).
unfold invariant. intros. generalize (H k).
rewrite (If_no H0). rewrite (If_ok H1). auto.
Qed.

Lemma inv_not_treated : forall N k, invariant N ->
  no (K_eq k source) -> no (treated N k) ->
  best_direct N k (dist N k).
unfold invariant. intros. generalize (H k).
rewrite (If_no H0). rewrite (If_no H1). auto.
Qed.


(*------------------------------------------------------------------*)
(* lemmas *)


Lemma path_from_not_treated_longer_than_dmin :
  forall N imin dmin, invariant N ->
  (imin,dmin) = select N -> 
  forall i (p : spath i), no (treated N i) -> 
  dmin <== length E p.
intros N imin dmin inv sel.
destruct (select_spec sel) as [dmin_min_of _].
asserts direct_path_longer (forall i j (q : spath i), 
        ok (treated N i) -> no (treated N j) ->
        dmin <== slength j (path_cons j q)).
  intros i j q treated_i not_treated_j. 
  caseb is_j_source (K_eq j source). 
    apply (num_le_trans (Val 0)).
      rewrite <- (inv_source inv).
       apply (min_of_when source dmin_min_of).      
       rewrite_K_eq <- is_j_source. auto.
      apply num_zero_le_any.  
    apply (num_le_trans (dist N j)).
      applya (min_of_when j dmin_min_of).
      asserts best_direct_j (best_direct N j (dist N j)).
        applya (inv_not_treated j inv).
      apply (min_of_when (path_cons j q) best_direct_j).
      exists i. exists q. auto.
asserts not_treated_longer 
       (forall s i (p : path s i), s = source ->
        no (treated N i) -> dmin <== length E p).
  induction p as [ j | s i j q ]. 
    intro EQ. rewrite EQ. intros. simpl.
     rewrite <- (inv_source inv).
     applya (min_of_when source dmin_min_of).
    caseb is_treated_i (treated N i).
      clear IHq. intro EQ. generalizes q. rewrite EQ.
       intros. apply direct_path_longer; auto.
      intros. simpl. apply (num_le_trans (length E q)).
         rewrite IHq; auto. 
         apply (num_le_add).
auto.
Qed.


Lemma factorization_of_path_direct : 
  forall N imin dmin k,
  let when1 := path_direct N (i:=k) in 
  let when2 p := (exists q : spath imin, p = path_cons k q) in
  let when12 := path_direct (update N imin dmin) (i:=k) in
  equivalent_when_or when1 when2 when12.
intros. 
sets update_treated (proj1 (update_spec N imin dmin)).
intro p. unfold when1, when2, when12. splits.
  (* when1 -> when12 *)
  unfold path_direct. intros [i [q [treated_q def_p]]].
  exists i. exists q. split; auto.
  rewrite update_treated. rewrite treated_q. auto.
  (* when2 -> when12 *)
  unfold path_direct. intros [q def_p].
  exists imin. exists q. split; auto.
  rewrite update_treated. 
  rewrite or_swap. rewrite (K_eq_refl imin). auto.
  (* when12 -> when1 \/ when2 *)
  unfold path_direct. intros [i [q [treated_q def_p]]].
  rewrite update_treated in treated_q.
  destruct (or_ok_case (treated N i) (K_eq i imin) treated_q).
  left. eauto. right. rewrite_K_eq <- H. eauto.
Qed.


Lemma dijkstra_initialize : invariant start.

unfold invariant. intro k.
destruct (start_spec k) as [S0 S1].
generalizes S1. case_If H1 (K_eq k source); intros.

  (* case k is source *)
  auto.

  (* otherwise k is not source *)
  case_If H2 (treated start k). 

  (* case k is treated *)
  contradicts.

  (* case k is not treated *)
  min_of_empty p P. auto. 
  destruct P as [i [q [P1 P2]]].
  destruct (start_spec i). 
  contradicts.
Qed.


Lemma dijkstra_case_final : forall N imin, 
  invariant N -> (imin,Inf) = select N ->
  dijkstra_output (final N).

intros N imin inv sel k.
rewrite final_spec. 
caseb is_source (K_eq k source).

  (* case k is source *)
  unfold shortest, shortest_path.
  rewrite_K_eq is_source. 
  rewrite (inv_source inv).
  min_of_given p P (path_nil source); auto.
  apply num_zero_le_any.

  (* otherwise k is not source *)
  caseb is_treated_k (treated N k).

  (* case k is treated *)
  apply (inv_treated k inv); auto. 
  replaces (dist N k) with Inf.
    destruct (select_spec sel) as [M _]. 
     apply num_inf_le_only_inf. 
     applya (min_of_when k M).
    sets longer (path_from_not_treated_longer_than_dmin inv sel).
     min_of_given p T (path_cons k (path_nil source)); auto.
     apply num_inf_le_only_inf. applya longer.
    
Qed.


Lemma dijkstra_case_step : forall N imin dmin, 
  invariant N -> (imin,dmin) = select N -> dmin <> Inf ->
  invariant (update N imin dmin).

intros N imin dmin inv sel dmin_not_inf k.

sets upd_spec (update_spec N imin dmin).
rewrite (proj1 upd_spec). rewrite (proj2 upd_spec).
clear upd_spec.

destruct (select_spec sel) as [dmin_min_of H].
destruct H as [ H | [no_treated_imin dmin_dist_imin] ].
contradiction.

asserts exists_qmin (exists q : spath imin, dmin = slength imin q).
  caseb is_imin_source (K_eq imin source). 

  (* case imin is source *)
  rewrite dmin_dist_imin. 
  rewrite_K_eq is_imin_source. 
  exists (path_nil source). 
  rewrite (inv_source inv). auto.

  (* case imin is not source *)
  asserts dmin_best_direct (best_direct N imin dmin).
    rewrite dmin_dist_imin. applya (inv_not_treated imin inv).   
  destruct dmin_best_direct as [[H1 H2] | [H1 [q [D L]]]].
    contradiction. eauto.

destruct exists_qmin as [qmin length_of_qmin].

asserts shortest_imin_dmin (shortest imin dmin).
  right. split. 
    intros p _. applya (path_from_not_treated_longer_than_dmin inv sel).
    exists qmin. eauto.

case_If is_source_k (K_eq k source).
  
  (* case k is source *)
  rewrite_K_eq is_source_k.
  rewrite (inv_source inv).
  unfold num_min. 
  rewrite num_zero_le_any. auto.

  (* otherwise k is not source *)
  caseb is_treated_k (treated N k).

  (* case k is treated *)
  rewrite is_treated_k. simpl.
  asserts optimal_dist_k (shortest k (dist N k)). 
    applya (inv_treated k inv).
  asserts not_improved ((dist N k) <== (dmin +=+ E [imin][k])).  
    set (p := path_cons k qmin).
    apply (@num_le_trans (slength k p)).  
      applya (min_of_when p optimal_dist_k).
      rewrite length_of_qmin. apply num_le_refl.
  unfold num_min. rewrite (If_ok not_improved). auto.

  (* otherwise k is not treated *)
  caseb is_k_imin (K_eq k imin).

  (* case k is imin *)
  rewrite is_k_imin. rewrite or_swap. simpl.
  rewrite_K_eq is_k_imin.
  rewrite <- dmin_dist_imin.
  rewrite num_min_le_add.
  apply shortest_imin_dmin.

  (* otherwise k is not imin *)
  rewrite_no is_treated_k. rewrite_no is_k_imin. simpl.
  asserts best_direct_k (best_direct N k (dist N k)).
    applya (inv_not_treated k inv).
  asserts best_via_imin_k ((dmin +=+ E[imin][k]) min_of (slength k) 
                            such_that (fun p : spath k => 
                            exists q : spath imin, p = path_cons k q)).
   min_of_given p exists_q (path_cons k qmin).
     destruct exists_q as [q def_p].
      rewrite def_p. simpl. apply num_le_add_both. 
      applya (min_of_when q shortest_imin_dmin). 
     eauto.
     simpl. rewrite length_of_qmin. auto. 
  unfold best_direct. 
  apply (min_of_factorize best_direct_k best_via_imin_k).
  apply factorization_of_path_direct.
Qed.


Lemma dijkstra_terminates : forall N imin dmin,
  no (treated N imin) ->
  measure (update N imin dmin) <* measure N.
intros N imin dmin no_treated_imin. unfold measure.
sets upd_spec (proj1 (update_spec N imin dmin)).
apply filter_implies_strict_count_lt. split. 
  intro i. rewrite upd_spec. apply or_no_proj.
  exists imin. rewrite upd_spec. 
   rewrite_no no_treated_imin. rewrite K_eq_refl. auto.
Qed.


(*------------------------------------------------------------------*)
(* conclusion : dijkstra computes shortest paths from a source
   in finite time for any finite graph with at least one node. *)


Theorem dijkstra_correct : 
    invariant start 
 /\ forall N imin dmin, invariant N ->
      (imin,dmin) = select N -> 
      (dmin = Inf  /\ dijkstra_output (final N))
   \/ (dmin <> Inf /\ let N' := update N imin dmin in
        invariant N' /\ measure N' <* measure N).
split. 
  apply dijkstra_initialize.
  intros N imin dmin inv sel. destruct dmin. 
    left. split. auto. apply (dijkstra_case_final inv sel).
    right. assert (Val n <> Inf). intro H. inversion H.
     splits. auto. applya (dijkstra_case_step inv sel).
     apply dijkstra_terminates.
      destruct (select_spec sel) as [_ [A | [A B]]]; auto.
Qed.


(*------------------------------------------------------------------*)

End Dijkstra.

(*------------------------------------------------------------------*)





