
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



