From FD Require Import Syntax.
From FD Require Import Types.
From FD Require Import StructCong.
From FD Require Import Reduction.
From FD Require Import Contexts.
From FD Require Import Typing.
From FD Require Import FinalProcess.
From FD Require Import Progress.

From Stdlib Require List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
Import List.ListNotations.

(******************************************************************************)
(* Irreducibility                                                             *)
(******************************************************************************)
Definition irreducible P := forall Q, ~ (P ⊳ Q).

(******************************************************************************)
(* The notion of final process coindices with irreducibility                  *)
(******************************************************************************)
(* We want to show, that for every well-typed P, final P iff irreducible P *)
(* The direction <- follows immediately by progress  *)
Lemma irreducible_implies_final :
  forall Γ P, Γ ⊢ P :# -> irreducible P -> final P.
Proof.
  intros. apply progress in H. destruct H as [[P' ?] |]; auto.
  exfalso. apply (H0 P'); auto.
Qed.

(* For the direction -> we require additional lemmata *)
(* Stop is irreducible *)
Lemma stop_irreducible : forall P, P = stop -> irreducible P.
Proof.
  intros P Hstop Q Hred.
  induction Hred; try discriminate; subst.
  apply IHHred.
  apply stop_equiv_stop; auto.
Qed.

(* Links containing futures are irreducible *)
Lemma link_future_irreducible_d :
    forall n,
      forall k i M P,
        k <= n ->
        P ≡ (link (future i) M) ->
        forall Q, ~ (reduces_d k P Q).
Proof.
  induction n; intros; intro Hred.
  + assert (k = 0) by lia; subst. inversion Hred; subst; try congruence;
    try match goal with
    | [ H : _ ≡ _ |- _ ] =>
        destruct (link_future_equiv_link_future _ _ _ (or_intror H)) as [M' [n' [? [? | ?]]]];
        try congruence
    end.
  + inversion Hred; subst;
    try match goal with
    | [ H : _ ≡ _ |- _ ] =>
        destruct (link_future_equiv_link_future _ _ _ (or_intror H)) as [M' [n' [? [? | ?]]]];
        try congruence
    end.
    - assert (n0 <= n) by lia.
      assert (P' ≡ (link (future i) M)). { eapply c_trans; eauto. apply c_comm; auto. }
      apply (IHn _ _ _ _ H6 H7 Q'); auto.
    - assert (n0 <= n) by lia.
      assert (P' ≡ (link (future i) M)). { eapply c_trans; eauto. apply c_comm; auto. }
      apply (IHn _ _ _ _ H6 H7 Q'); auto.
Qed.

Lemma link_future_irreducible :
  forall i M P,
    P ≡ (link (future i) M) ->
    irreducible P.
Proof.
  intros. intros Q Hred.
  apply reduces_d_from_reduces in Hred. destruct Hred.
  eapply link_future_irreducible_d in H0; auto.
  apply H.
Qed.

(* Link trees are irreducible *)
Inductive link_tree : nat -> process -> Prop :=
  | link_tree_leaf_nn : forall i i1 i2 M1 M2 P1 P2,
                    no_future M1 -> no_future M2 ->
                    i < i1 -> i < i2 ->
                    P1 ≡ (link (future i1) M1) ->
                    P2 ≡ (link (future i2) M2) ->
                    link_tree i (cut P1 P2)
  | link_tree_leaf_nf : forall i i1 i2 i3 M P,
                    no_future M ->
                    i < i1 -> i < i2 -> i < i3 ->
                    P ≡ (link (future i3) M) ->
                    link_tree i (cut (link (future i1) (future i2)) P)
  | link_tree_leaf_fn : forall i i1 i2 i3 M P,
                          no_future M ->
                          i < i1 -> i < i2 -> i < i3 ->
                          P ≡ (link (future i1) M) ->
                          link_tree i (cut P (link (future i2) (future i3)))
  | link_tree_leaf_ff : forall i i1 i2 i3 i4,
                          i < i1 -> i < i2 -> i < i3 -> i < i4 ->
                          link_tree i
                            (cut (link (future i1) (future i2)) (link (future i3) (future i4)))
  | link_tree_cons_nl : forall i i' M P L,
                          link_tree (S i) P ->
                          no_future M ->
                          i < i' ->
                          L ≡ (link (future i') M) ->
                          link_tree i (cut L P)
  | link_tree_cons_nr : forall i i' M P R,
                          link_tree (S i) P ->
                          no_future M ->
                          i < i' ->
                          R ≡ (link (future i') M) ->
                          link_tree i (cut P R)
  | link_tree_cons_fl : forall i i1 i2 P,
                          link_tree (S i) P ->
                          i < i1 -> i < i2 ->
                          link_tree i (cut (link (future i1) (future i2)) P)
  | link_tree_cons_fr : forall i i1 i2 P,
                          link_tree (S i) P ->
                          i < i1 -> i < i2 ->
                          link_tree i (cut P (link (future i1) (future i2)))
  | link_tree_branch : forall i P Q,
                        link_tree (S i) P -> link_tree (S i) Q -> link_tree i (cut P Q).

(* A final link list is a link tree *)
Lemma final_link_list_is_link_tree' :
  forall j xs P,
    (forall x, List.In x xs -> x > j) -> link_list xs P -> link_tree j P.
Proof.
  intros.
  generalize dependent j.
  induction H0; intros.
  + destruct M1, M2; try congruence.
    destruct (link_future_equiv_link_future _ _ _ (or_intror H1)) as [? [? [? ?]]].
    destruct (link_future_equiv_link_future _ _ _ (or_intror H2)) as [? [? [? ?]]].
    destruct H5, H7; subst; simpl in H3.
    - destruct x, x1; try now inversion H4.
      eapply link_tree_leaf_nn; try apply c_refl; try congruence;
      [ specialize H3 with i1 | specialize H3 with i2 ]; lia.
    - destruct x, x1; try now inversion H4.
      eapply link_tree_leaf_nn; try apply c_refl; try apply c_link; try congruence;
      [ specialize H3 with i1 | specialize H3 with i2 ]; lia.
    - destruct x, x1; try now inversion H4.
      eapply link_tree_leaf_nn; try apply c_refl; try apply c_link; try congruence;
      [ specialize H3 with i1 | specialize H3 with i2 ]; lia.
    - destruct x, x1; try now inversion H4.
      eapply link_tree_leaf_nn; try apply c_refl; try apply c_link; try congruence;
      [ specialize H3 with i1 | specialize H3 with i2 ]; lia.
  + destruct M; try congruence.
    destruct (link_future_equiv_link_future _ _ _ (or_intror H0)) as [? [? [? ?]]].
    destruct x. inversion H2. simpl in H1.
    destruct H3; subst.
    - eapply link_tree_leaf_nf; try apply c_refl; try congruence;
      [ specialize H1 with i1 | specialize H1 with i2 | specialize H1 with i3 ]; lia.
    - eapply link_tree_leaf_nf; try apply c_link; try congruence;
      [ specialize H1 with i1 | specialize H1 with i2 | specialize H1 with i3 ]; lia.
  + destruct M; try congruence.
    destruct (link_future_equiv_link_future _ _ _ (or_intror H0)) as [? [? [? ?]]].
    destruct x. inversion H2. simpl in H1.
    destruct H3; subst.
    - eapply link_tree_leaf_fn; try apply c_refl; try congruence;
      [ specialize H1 with i1 | specialize H1 with i2 | specialize H1 with i3 ]; lia.
    - eapply link_tree_leaf_fn; try apply c_link; try congruence;
      [ specialize H1 with i1 | specialize H1 with i2 | specialize H1 with i3 ]; lia.
  + apply link_tree_leaf_ff; simpl in H;
    [ specialize H with i1 | specialize H with i2 | specialize H with i3 | specialize H with i4 ]; lia.
  + pose proof (H2 i). simpl in H3.
    eapply link_tree_cons_nl.
    * apply IHlink_list; intros. apply List.in_map_iff in H4. destruct H4 as [x' [? ?]].
      subst. specialize H2 with x'. simpl in H2. pose proof (H2 (or_intror H5)). lia.
    * eassumption.
    * eapply H2. simpl. left. reflexivity.
    * eassumption.
  + pose proof (H i1). simpl in H1.
    pose proof (H i2). simpl in H2.
    simpl in H.
    eapply link_tree_cons_fl.
    * apply IHlink_list; intros. apply List.in_map_iff in H3. destruct H3 as [x' [? ?]].
      subst. specialize H with x'. pose proof (H (or_intror (or_intror H4))). lia.
    * lia.
    * lia.
Qed.

Lemma final_link_list_is_link_tree :
  forall xs P,
    ~ (List.In 0 xs) -> link_list xs P -> link_tree 0 P.
Proof.
  intros. eapply final_link_list_is_link_tree'; eauto.
  intros. destruct x; [congruence | lia].
Qed.

(* Link treenes is preserved under structural congruence *)
Lemma struct_cong_preserves_link_tree' :
  forall n,
    forall k,
      k <= n ->
        forall j P Q,
          link_tree j P ->
          (struct_cong_d k P Q) \/ (struct_cong_d k Q P) ->
          link_tree j Q.
Proof.
  induction n; intros.
  + assert (k = 0) by lia; subst. destruct H1; inversion H1; subst.
    - inversion H0.
    - inversion H0; subst;
      admit.
    - inversion H0; subst;
      admit.
    - auto.
    - inversion H0.
    - inversion H0; subst;
      admit.
    - inversion H0; subst;
      admit.
    - auto.
  + destruct H1.
    - inversion H1; subst.
      * inversion H0.
      * inversion H0; subst;
        admit.
      * admit.
      * auto.
      * eapply (IHn n0); eauto. lia.
      * assert (link_tree j Q0). { eapply (IHn n1); eauto. lia. }
        eapply (IHn n2); eauto. lia.
      * inversion H0.
      * inversion H0; subst;
        admit.
      * inversion H0.
    - inversion H1; subst.
      * inversion H0.
      * inversion H0; subst;
        admit.
      * admit.
      * auto.
      * eapply (IHn n0); eauto. lia.
      * assert (link_tree j Q0). { eapply (IHn n2); eauto. lia. }
        eapply (IHn n1); eauto. lia.
      * inversion H0.
      * admit.
      * inversion H0.
Admitted.

Lemma struct_cong_preserves_link_tree :
  forall j P Q, link_tree j P -> P ≡ Q -> link_tree j Q.
Proof.
  intros.
  eapply (proj1 struct_cong_d_from_struct_cong) in H0. destruct H0.
  eapply struct_cong_preserves_link_tree'; eauto.
Qed.

Lemma link_tree_irreducible' :
  forall n,
    forall k,
      k <= n ->
      forall j P, link_tree j P -> (forall Q, ~ (reduces_d k P Q)).
Proof.
  induction n; intros; intro Hred.
  + assert (k = 0) by lia; subst. inversion Hred; subst; try now inversion H0.
    inversion H0; subst; exfalso; try lia.
    - destruct (link_future_equiv_link_future _ _ _ (or_introl H8)) as [? [? [? [? | ?]]]].
      * inversion H2; subst. lia.
      * inversion H2; subst. congruence.
    - destruct (link_future_equiv_link_future _ _ _ (or_introl H8)) as [? [? [? [? | ?]]]].
      * inversion H2; subst. lia.
      * inversion H2; subst. congruence.
    - destruct (link_future_equiv_link_future _ _ _ (or_introl H7)) as [? [? [? [? | ?]]]].
      * inversion H2; subst. lia.
      * inversion H2; subst. congruence.
    - inversion H3.
    - inversion H3.
    - inversion H4.
  + inversion H0; subst.
    - inversion Hred; subst.
      * destruct (link_future_equiv_link_future _ _ _ (or_introl H5)) as [? [? [? [? | ?]]]].
        ** inversion H8; subst. lia.
        ** inversion H8; subst. congruence.
      * apply (link_future_irreducible _ _ _ H5 P').
        apply reduces_from_reduces_d in H11; auto.
      * assert (n0 <= n) by lia.
        apply (struct_cong_preserves_link_tree _ _ _ H0) in H7.
        apply (IHn n0 H10 _ _ H7 Q'); auto.
    - inversion Hred; subst.
      * inversion H0; lia.
      * assert ((link (future i1) (future i2)) ≡ (link (future i1) (future i2))) by apply c_refl.
        apply (link_future_irreducible _ _ _ H6 P').
        apply reduces_from_reduces_d in H10; auto.
      * assert (n0 <= n) by lia.
        apply (struct_cong_preserves_link_tree _ _ _ H0) in H6.
        apply (IHn n0 H9 _ _ H6 Q'); auto.
    - inversion Hred; subst.
      * destruct (link_future_equiv_link_future _ _ _ (or_introl H5)) as [? [? [? [? | ?]]]].
        ** inversion H7; subst. lia.
        ** inversion H7; subst. congruence.
      * apply (link_future_irreducible _ _ _ H5 P').
        apply reduces_from_reduces_d in H10; auto.
      * assert (n0 <= n) by lia.
        apply (struct_cong_preserves_link_tree _ _ _ H0) in H6.
        apply (IHn n0 H9 _ _ H6 Q'); auto.
    - inversion Hred; subst.
      * lia.
      * assert ((link (future i1) (future i2)) ≡ (link (future i1) (future i2))) by apply c_refl.
        apply (link_future_irreducible _ _ _ H5 P').
        apply reduces_from_reduces_d in H9; auto.
      * assert (n0 <= n) by lia.
        apply (struct_cong_preserves_link_tree _ _ _ H0) in H5.
        apply (IHn n0 H8 _ _ H5 Q'); auto.
    - inversion Hred; subst.
      * destruct (link_future_equiv_link_future _ _ _ (or_introl H4)) as [? [? [? [? | ?]]]].
        ** inversion H6; subst. lia.
        ** inversion H6; subst. congruence.
      * apply (link_future_irreducible _ _ _ H4 P').
        apply reduces_from_reduces_d in H9; auto.
      * assert (n0 <= n) by lia.
        apply (struct_cong_preserves_link_tree _ _ _ H0) in H5.
        apply (IHn n0 H8 _ _ H5 Q'); auto.
    - inversion Hred; subst.
      * inversion H1.
      * assert (n0 <= n) by lia.
        apply (IHn n0 H5 _ _ H1 P'); auto.
      * assert (n0 <= n) by lia.
        apply (struct_cong_preserves_link_tree _ _ _ H0) in H5.
        apply (IHn n0 H8 _ _ H5 Q'); auto.
    - inversion Hred; subst.
      * lia.
      * assert ((link (future i1) (future i2)) ≡ (link (future i1) (future i2))) by apply c_refl.
        apply (link_future_irreducible _ _ _ H4 P').
        apply reduces_from_reduces_d in H8; auto.
      * assert (n0 <= n) by lia.
        apply (struct_cong_preserves_link_tree _ _ _ H0) in H4.
        apply (IHn n0 H7 _ _ H4 Q'); auto.
    - inversion Hred; subst.
      * inversion H1.
      * assert (n0 <= n) by lia.
        apply (IHn n0 H4 _ _ H1 P'); auto.
      * assert (n0 <= n) by lia.
        apply (struct_cong_preserves_link_tree _ _ _ H0) in H4.
        apply (IHn n0 H7 _ _ H4 Q'); auto.
    - inversion Hred; subst.
      * inversion H1.
      * assert (n0 <= n) by lia.
        apply (IHn n0 H3 _ _ H1 P'); auto.
      * assert (n0 <= n) by lia.
        apply (struct_cong_preserves_link_tree _ _ _ H0) in H3.
        apply (IHn n0 H6 _ _ H3 Q'); auto.
Qed.

Lemma link_tree_irreducible :
  forall j P, link_tree j P -> irreducible P.
Proof.
  intros. intros Q Hred. apply reduces_d_from_reduces in Hred. destruct Hred.
  eapply link_tree_irreducible' in H0; eauto.
Qed.

(* The direction -> uses the facts above:
   stop, links with futures and link trees are irreducible *)
Lemma final_implies_irreducible :
  forall Γ P, Γ ⊢ P :# -> final P -> irreducible P.
Proof.
  intros. inversion H0.
  + apply stop_irreducible. reflexivity.
  + eapply link_future_irreducible. apply c_refl.
  + eapply link_future_irreducible. apply c_link.
  + assert (link_tree 0 P'). { apply (final_link_list_is_link_tree _ _ H1 H2). }
    (* link_treenes is preserved under structural congruence *)
    apply c_comm in H3.
    pose proof (struct_cong_preserves_link_tree _ _ _ H5 H3).
    (* link_trees are irreducible *)
    eapply link_tree_irreducible; eauto.
Qed.

Corollary final_iff_irreducible :
  forall Γ P, Γ ⊢ P :# -> final P <-> irreducible P.
Proof.
  intros; split.
  + eapply final_implies_irreducible; eauto.
  + eapply irreducible_implies_final; eauto.
Qed.
