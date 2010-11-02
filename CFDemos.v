Set Implicit Arguments.
Require Import LibCore Shared CFHeaps.


(** Demos *)

Lemma hextract_demo_1 : forall n J H2 H3 H4 H',
  H4 \* (Hexists y, [y = 2]) \* 
   (Hexists x, [n = x + x] \* (J x \* x ~> Id 3) \* H2) \* H3 ==> H'.
Proof.
  intros. dup 3.
  (* details *)
  hextract_setup tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  try hextract_step tt.
  hextract_cleanup tt.
  intros.
  skip.
  (* short *)
  hextract. skip.
  (* if needed *)
  hextract_if_needed tt. intros.
  try hextract_if_needed tt. skip.
Qed.

Lemma hextract_demo_2 : forall H1 H' (G:Prop),
  (forall H2, H1 \* (Hexists y, [y = 2]) \* H2 ==> H' -> G) ->
  G.
Proof.
  introv W. eapply W. dup.
  (* details *)
  hextract_setup tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  try hextract_step tt.
  hextract_cleanup tt.
  intros y Hy.
  skip.
  (* short *)
  hextract. skip.
Admitted.


Lemma hsimpl_demo_1 : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 ==> H4 \* H3 \* H5 \* H2.
Proof.
  intros. dup. 
  (* details *)
  hsimpl_setup tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  try hsimpl_step tt.
  hsimpl_cleanup tt.
  skip.
  (* short *)
  hsimpl. skip.
Qed.

Lemma hsimpl_demo_2 : forall (l1 l2:loc) S1 S2 H1 H2 H3 H',
  (forall X S1' HG, X ==> H1 \* l1 ~> S1' \* H2 \* HG -> X ==> H') ->
  H1 \* l1 ~> S1 \* l2 ~> S2 \* H3 ==> H'.
Proof.
  intros. dup.
  (* details *) 
  eapply H.
  hsimpl_setup tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  try hsimpl_step tt.
  hsimpl_cleanup tt.
  skip.
  (* short *)
  eapply H.
  hsimpl. skip.
Admitted.

Lemma hsimpl_demo_3 : forall (l1 l2:loc) S1 S2 H1 H2 H',
  (forall X S1' HG, X ==> H1 \* l1 ~> S1' \* HG -> HG = HG -> X ==> H') ->
  H1 \* l1 ~> S1 \* l2 ~> S2 \* H2 ==> H'.
Proof.
  intros. dup.
  (* details *)
  eapply H.  
  hsimpl_setup tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  try hsimpl_step tt.
  hsimpl_cleanup tt.
  skip.
  auto.
  (* short *)
  eapply H.
  hsimpl.
  auto.
Admitted.

Lemma hsimpl_demo_4 : forall n m J H2 H3 H4,
  n = m + m ->
  H2 \* J m \* H3 \* H4 ==> H4 \* (Hexists y, y ~> Id 2) \* (Hexists x, [n = x + x] \* J x \* H2) \* H3.
Proof.
  intros. dup.
  (* details *)
  hsimpl_setup tt.
  hsimpl_step tt.
  hsimpl_step tt. 
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  try hsimpl_step tt.
  hsimpl_cleanup tt.
  auto.
  auto.
  auto.
  (* short *)
  hsimpl.
  auto.
  auto.
  auto.
Qed.

Lemma hclean_demo_1 : forall A (x X:A) H1 H2 H3 B (F:~~B) Q,  
   is_local F ->
   F (H1 \* [] \* (H2 \* Hexists y:int, [y = y]) \* x ~> Id X \* H3) Q.
Proof.
  intros. dup.
  (* details *)
  hclean_setup tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  try hclean_step tt.  hclean_cleanup tt.
  skip.
  (* short *)
  hclean.
  skip.
Qed.  




