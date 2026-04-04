From Stdlib Require Import Relations.

Definition diamond_property {A} (R : relation A) :=
  forall (x y1 y2 : A), R x y1 -> R x y2 -> exists z, R y1 z /\ R y2 z.

Lemma diamond_property_for_symmR :
  forall {A} (R : relation A), symmetric _ R -> diamond_property R.
Proof. unfold diamond_property; intros. exists x; split; auto. Qed.

(******************************************************************************)
(* Lemmata for Relation Operators                                             *)
(******************************************************************************)
Lemma symmetric_clos_trans_1n :
  forall {A} (R : relation A), symmetric _ R ->
    symmetric _ (clos_trans_1n A R).
Proof.
  intros. unfold symmetric in *; intros. induction H0.
  + apply t1n_step; auto.
  + apply clos_trans_t1n. eapply t_trans.
    - apply clos_t1n_trans in IHclos_trans_1n. eassumption.
    - apply t_step. apply H; auto.
Qed.

(******************************************************************************)
(* Generic Results on Confluence                                              *)
(******************************************************************************)
Lemma diamond_R_clos_trans_1n_R_r :
  forall {A} (R : relation A), diamond_property R ->
    forall (x y1 y2 : A), R x y1 -> (clos_trans_1n _ R) x y2 ->
      exists z, (clos_trans_1n _ R) y1 z /\ (clos_trans_1n _ R) y2 z.
Proof.
  intros. generalize dependent y1.
  induction H1; intros.
  + destruct (H _ _ _ H0 H1) as [? [? ?]]. exists x0; split; econstructor; auto.
  + destruct (H _ _ _ H0 H2) as [? [? ?]].
    destruct (IHclos_trans_1n _ H3) as [? [? ?]].
    exists x1; split; auto.
    eapply Relation_Operators.t1n_trans; eauto.
Qed.

Lemma diamond_R_diamond_clos_trans_R :
  forall {A} (R : relation A),
    diamond_property R -> diamond_property (clos_trans _  R).
Proof.
  intros. unfold diamond_property. intros.
  apply clos_trans_t1n_iff in H0. apply clos_trans_t1n_iff in H1.
  generalize dependent y2.
  induction H0; intros.
  + destruct (diamond_R_clos_trans_1n_R_r _ H _ _ _ H0 H1) as [? [? ?]].
    exists x0. apply clos_trans_t1n_iff in H2. apply clos_trans_t1n_iff in H3.
    split; auto.
  + destruct (diamond_R_clos_trans_1n_R_r _ H _ _ _ H0 H2) as [? [? ?]].
    destruct (IHclos_trans_1n _ H3) as [? [? ?]]. exists x1. split; auto.
    apply clos_trans_t1n_iff in H4. eapply t_trans; eauto.
Qed.

Lemma diamond_preserved_under_eq :
  forall {A} (R1 R2 : relation A),
    diamond_property R1 -> (forall x y, R1 x y <-> R2 x y) -> diamond_property R2.
Proof.
  intros. unfold diamond_property; intros.
  apply H0 in H1. apply H0 in H2. destruct (H _ _ _ H1 H2) as [? [? ?]].
  exists x0. apply H0 in H3. apply H0 in H4. split; auto.
Qed.
