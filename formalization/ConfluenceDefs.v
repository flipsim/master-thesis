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
