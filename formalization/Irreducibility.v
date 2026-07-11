From FD Require Import Syntax.
From FD Require Import Types.
From FD Require Import Renaming.
From FD Require Import StructCong.
From FD Require Import Reduction.
From FD Require Import Contexts.
From FD Require Import Typing.
From FD Require Import FinalProcess.
From FD Require Import Progress.
From FD Require Import FreeVars.

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
  forall Γ P, Γ ⊢ P :# -> irreducible P -> is_final P.
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

Ltac link_tree_econstructor :=
  match goal with
  | [ |- link_tree ?j (cut (link (future ?i1) (future ?i2)) (link (future ?i3) (future ?i4))) ]
    => eapply link_tree_leaf_ff; eauto
  | [ HP  : ?P ≡ (link (future ?i1) _),
      Hi1 : ?j < ?i1,
      Hi2 : ?j < ?i2,
      Hi3 : ?j < ?i3
      |- link_tree ?j (cut ?P (link (future ?i2) (future ?i3))) ]
    => eapply (link_tree_leaf_fn _ _ _ _ _ _ _ Hi1 Hi2 Hi3 HP); eauto
  | [ HP  : ?P ≡ (link (future ?i3) _),
      Hi1 : ?j < ?i1,
      Hi2 : ?j < ?i2,
      Hi3 : ?j < ?i3
      |- link_tree ?j (cut (link (future ?i1) (future ?i2)) ?P) ]
    => eapply (link_tree_leaf_nf _ _ _ _ _ _ _ Hi1 Hi2 Hi3 HP); eauto
  | [ HQ  : link_tree (S ?j) ?Q,
      Hi1 : ?j < ?i1,
      Hi2 : ?j < ?i2
      |- link_tree ?j (cut ?Q (link (future ?i1) (future ?i2))) ]
    => eapply (link_tree_cons_fr _ _ _ _ HQ Hi1 Hi2); eauto
  | [ HQ  : link_tree (S ?j) ?Q,
      Hi1 : ?j < ?i1,
      Hi2 : ?j < ?i2
      |- link_tree ?j (cut (link (future ?i1) (future ?i2)) ?Q) ]
    => eapply (link_tree_cons_fl _ _ _ _ HQ Hi1 Hi2); eauto
  | [ HP : ?P ≡ (link (future ?i) ?M),
      Hi : ?j < ?i,
      HQ : link_tree (S ?j) ?Q
      |- link_tree ?j (cut ?P ?Q) ]
    => eapply (link_tree_cons_nl _ _ _ _ _ HQ _ Hi HP); eauto
  | [ HP : ?P ≡ (link (future ?i) ?M),
      Hi : ?j < ?i,
      HQ : link_tree (S ?j) ?Q
      |- link_tree ?j (cut ?Q ?P) ]
    => eapply (link_tree_cons_nr _ _ _ _ _ HQ _ Hi HP); eauto
  | [ HP  : ?P ≡ (link (future ?i1) ?M1),
      HQ  : ?Q ≡ (link (future ?i2) ?M2),
      Hi1 : ?j < ?i1,
      Hi2 : ?j < ?i2
      |- link_tree ?j (cut ?P ?Q) ]
    => eapply (link_tree_leaf_nn _ _ _ _ _ _ _ _ _ Hi1 Hi2 HP HQ); eauto
  | [ HP : link_tree (S ?j) ?P,
      HQ : link_tree (S ?j) ?Q
      |- link_tree ?j (cut ?P ?Q) ]
    => eapply (link_tree_branch _ _ _ HP HQ); eauto
  end.

(* Helper lemmas on link trees *)
Lemma link_tree_SSj_f :
  forall j P f,
    (forall x, S j < x -> S j < f x) ->
    link_tree (S (S j)) P -> link_tree (S (S j)) (rename_process P f).
Proof with try (exfalso; lia).
  intros. generalize dependent j. generalize dependent f.
  induction P; intros; inversion H0; subst.
  + assert (up_ren f i1 > S (S j)).
    {
      destruct i1... destruct i1... destruct i1...
      simpl.
      assert (f (S (S i1)) > S j). { apply H; auto. lia. }
      lia.
    }
    assert (up_ren f i2 > S (S j)).
    {
      destruct i2... destruct i2... destruct i2...
      simpl.
      assert (f (S (S i2)) > S j). { apply H; auto. lia. }
      lia.
    }
    destruct (link_future_equiv_link_future _ _ _ (or_intror H8)) as [? [? [? ?]]].
    destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
    destruct H10, H12; subst; simpl.
    - eapply link_tree_leaf_nn; try apply c_refl; try lia.
      * destruct M1; try congruence; inversion H7; simpl; congruence.
      * destruct M2; try congruence; inversion H11; simpl; congruence.
    - eapply link_tree_leaf_nn; try apply c_refl;  try apply c_link; try lia.
      * destruct M1; try congruence; inversion H7; simpl; congruence.
      * destruct M2; try congruence; inversion H11; simpl; congruence.
    - eapply link_tree_leaf_nn; try apply c_refl;  try apply c_link; try lia.
      * destruct M1; try congruence; inversion H7; simpl; congruence.
      * destruct M2; try congruence; inversion H11; simpl; congruence.
    - eapply link_tree_leaf_nn; try apply c_refl;  try apply c_link; try lia.
      * destruct M1; try congruence; inversion H7; simpl; congruence.
      * destruct M2; try congruence; inversion H11; simpl; congruence.
  + assert (up_ren f i1 > S (S j)).
    {
      destruct i1... destruct i1... destruct i1...
      simpl.
      assert (f (S (S i1)) > S j). { apply H; auto. lia. }
      lia.
    }
    assert (up_ren f i2 > S (S j)).
    {
      destruct i2... destruct i2... destruct i2...
      simpl.
      assert (f (S (S i2)) > S j). { apply H; auto. lia. }
      lia.
    }
    assert (up_ren f i3 > S (S j)).
    {
      destruct i3... destruct i3... destruct i3...
      simpl.
      assert (f (S (S i3)) > S j). { apply H; auto. lia. }
      lia.
    }
    simpl.
    destruct (link_future_equiv_link_future _ _ _ (or_intror H8)) as [? [? [? ?]]].
    eapply (link_tree_leaf_nf _ _ _ _ (rename_message x (up_ren f))); try lia.
    - destruct M; try congruence; inversion H9; simpl; congruence.
    - assert (S (S j) < up_ren f i3) by lia. apply H11.
    - destruct H10; subst. simpl. apply c_refl. apply c_link.
  + assert (up_ren f i1 > S (S j)).
    {
      destruct i1... destruct i1... destruct i1...
      simpl.
      assert (f (S (S i1)) > S j). { apply H; auto. lia. }
      lia.
    }
    assert (up_ren f i2 > S (S j)).
    {
      destruct i2... destruct i2... destruct i2...
      simpl.
      assert (f (S (S i2)) > S j). { apply H; auto. lia. }
      lia.
    }
    assert (up_ren f i3 > S (S j)).
    {
      destruct i3... destruct i3... destruct i3...
      simpl.
      assert (f (S (S i3)) > S j). { apply H; auto. lia. }
      lia.
    }
    simpl.
    destruct (link_future_equiv_link_future _ _ _ (or_intror H8)) as [? [? [? ?]]].
    eapply (link_tree_leaf_fn _ _ _ _ (rename_message x (up_ren f))); try lia.
    - destruct M; try congruence; inversion H9; simpl; congruence.
    - assert (S (S j) < up_ren f i1) by lia. apply H11.
    - destruct H10; subst. simpl. apply c_refl. apply c_link.
  + simpl.
    assert (up_ren f i1 > S (S j)).
    {
      destruct i1... destruct i1... destruct i1...
      simpl.
      assert (f (S (S i1)) > S j). { apply H; auto. lia. }
      lia.
    }
    assert (up_ren f i2 > S (S j)).
    {
      destruct i2... destruct i2... destruct i2...
      simpl.
      assert (f (S (S i2)) > S j). { apply H; auto. lia. }
      lia.
    }
    assert (up_ren f i3 > S (S j)).
    {
      destruct i3... destruct i3... destruct i3...
      simpl.
      assert (f (S (S i3)) > S j). { apply H; auto. lia. }
      lia.
    }
    assert (up_ren f i4 > S (S j)).
    {
      destruct i4... destruct i4... destruct i4...
      simpl.
      assert (f (S (S i4)) > S j). { apply H; auto. lia. }
      lia.
    }
    link_tree_econstructor.
  + assert (up_ren f i' > S (S j)).
    {
      destruct i'... destruct i'... destruct i'...
      simpl.
      assert (f (S (S i')) > S j). { apply H; auto. lia. }
      lia.
    }
    simpl.
    destruct (link_future_equiv_link_future _ _ _ (or_intror H7)) as [? [? [? ?]]].
    eapply (link_tree_cons_nl _ _ (rename_message x (up_ren f))).
    - apply IHP2; auto. intros. destruct x1... destruct x1... destruct x1...
      simpl. assert (S j < f (S (S x1))). { apply H; auto. lia. } lia.
    - destruct M; try congruence; inversion H2; simpl; congruence.
    - assert (S (S j) < up_ren f i') by lia. apply H8.
    - destruct H5; subst; simpl. apply c_refl. apply c_link.
  + assert (up_ren f i' > S (S j)).
    {
      destruct i'... destruct i'... destruct i'...
      simpl.
      assert (f (S (S i')) > S j). { apply H; auto. lia. }
      lia.
    }
    simpl.
    destruct (link_future_equiv_link_future _ _ _ (or_intror H7)) as [? [? [? ?]]].
    eapply (link_tree_cons_nr _ _ (rename_message x (up_ren f))).
    - apply IHP1; auto. intros. destruct x1... destruct x1... destruct x1...
      simpl. assert (S j < f (S (S x1))). { apply H; auto. lia. } lia.
    - destruct M; try congruence; inversion H2; simpl; congruence.
    - assert (S (S j) < up_ren f i') by lia. apply H8.
    - destruct H5; subst; simpl. apply c_refl. apply c_link.
  + assert (up_ren f i1 > S (S j)).
    {
      destruct i1... destruct i1... destruct i1...
      simpl.
      assert (f (S (S i1)) > S j). { apply H; auto. lia. }
      lia.
    }
    assert (up_ren f i2 > S (S j)).
    {
      destruct i2... destruct i2... destruct i2...
      simpl.
      assert (f (S (S i2)) > S j). { apply H; auto. lia. }
      lia.
    }
    simpl.
    apply link_tree_cons_fl; auto.
    eapply (IHP2 (up_ren f) _ _ H3). Unshelve.
    intros. destruct x... destruct x... destruct x... simpl.
    assert (S j < f (S (S x))). { apply H; auto; lia. } lia.
  + assert (up_ren f i1 > S (S j)).
    {
      destruct i1... destruct i1... destruct i1...
      simpl.
      assert (f (S (S i1)) > S j). { apply H; auto. lia. }
      lia.
    }
    assert (up_ren f i2 > S (S j)).
    {
      destruct i2... destruct i2... destruct i2...
      simpl.
      assert (f (S (S i2)) > S j). { apply H; auto. lia. }
      lia.
    }
    simpl.
    apply link_tree_cons_fr; auto.
    eapply (IHP1 (up_ren f) _ _ H3). Unshelve.
    intros. destruct x... destruct x... destruct x... simpl.
    assert (S j < f (S (S x))). { apply H; auto; lia. } lia.
  + apply (IHP1 (up_ren f)) in H4. apply (IHP2 (up_ren f)) in H5.
    - simpl. link_tree_econstructor.
    - intros. destruct x... destruct x... destruct x... simpl.
      assert (f (S (S x)) > S j). { apply H. lia. }
      lia.
    - intros. destruct x... destruct x... destruct x... simpl.
      assert (f (S (S x)) > S j). { apply H. lia. }
      lia.
Qed.

Lemma link_tree_SSj_swap01 :
  forall j P,
    link_tree (S (S j)) P -> link_tree (S (S j)) (rename_process P swap01).
Proof with try (exfalso; lia).
  intros. apply link_tree_SSj_f; auto; intros. destruct x... destruct x...
  simpl. auto.
Qed.

Lemma link_tree_down :
  forall j P,
    link_tree (S j) P -> forall k, link_tree j (down1_process P k).
Proof with (try (exfalso; lia)).
  intros. generalize dependent j. generalize dependent k.
  induction P; intros; inversion H; subst.
  + destruct (link_future_equiv_link_future _ _ _ (or_intror H7)) as [? [? [? ?]]].
    destruct (link_future_equiv_link_future _ _ _ (or_intror H8)) as [? [? [? ?]]].
    destruct i1, i2... destruct i1, i2...
    destruct H1, H9; subst; simpl; unfold relocate; simpl;
    destruct (S k <? S (S i1)), (S k <? S (S i2)); eapply link_tree_leaf_nn;
    try apply c_refl; try apply c_link; try lia;
    try (destruct M1; try congruence; inversion H0; simpl; congruence);
    try (destruct M2; try congruence; inversion H6; simpl; congruence).
  + destruct (link_future_equiv_link_future _ _ _ (or_intror H7)) as [? [? [? ?]]].
    destruct i1, i2, i3... destruct i1, i2, i3...
    destruct H1; subst; simpl; unfold relocate; simpl;
    destruct (S k <? S (S i1)), (S k <? S (S i2)), (S k <? S (S i3));
    eapply link_tree_leaf_nf; try apply c_refl; try apply c_link; try lia;
    try (destruct M; try congruence; inversion H0; simpl; congruence).
  + destruct (link_future_equiv_link_future _ _ _ (or_intror H7)) as [? [? [? ?]]].
    destruct i1, i2, i3... destruct i1, i2, i3...
    destruct H1; subst; simpl; unfold relocate; simpl;
    destruct (S k <? S (S i1)), (S k <? S (S i2)), (S k <? S (S i3));
    eapply link_tree_leaf_fn; try apply c_refl; try apply c_link; try lia;
    try (destruct M; try congruence; inversion H0; simpl; congruence).
  + destruct i1, i2, i3, i4... destruct i1, i2, i3, i4...
    simpl; unfold relocate; simpl;
    destruct (S k <? S (S i1)), (S k <? S (S i2)), (S k <? S (S i3)), (S k <? S (S i4));
    eapply link_tree_leaf_ff; lia.
  + destruct (link_future_equiv_link_future _ _ _ (or_intror H6)) as [? [? [? ?]]].
    destruct i'...
    destruct H1; subst; simpl; unfold relocate; simpl;
    destruct (S k <? S i');
    eapply link_tree_cons_nl; try apply c_refl; try apply c_link; try lia;
    try (destruct M; try congruence; inversion H0; simpl; congruence);
    try apply IHP2; auto.
  + destruct (link_future_equiv_link_future _ _ _ (or_intror H6)) as [? [? [? ?]]].
    destruct i'...
    destruct H1; subst; simpl; unfold relocate; simpl;
    destruct (S k <? S i');
    eapply link_tree_cons_nr; try apply c_refl; try apply c_link; try lia;
    try (destruct M; try congruence; inversion H0; simpl; congruence);
    try apply IHP1; auto.
  + destruct i1, i2... destruct i1, i2...
    simpl. destruct (S k <? S (S i1)), (S k <? S (S i2));
    eapply link_tree_cons_fl; try lia; try apply IHP2; auto.
  + destruct i1, i2... destruct i1, i2...
    simpl. destruct (S k <? S (S i1)), (S k <? S (S i2));
    eapply link_tree_cons_fr; try lia; try apply IHP1; auto.
  + simpl. apply link_tree_branch; [apply IHP1 | apply IHP2]; auto.
Qed.

Lemma link_tree_lift_j_up :
  forall j P,
    forall k, k <= j -> link_tree j P -> link_tree (S j) (lift_process P k 1).
Proof with try (exfalso; lia).
  intros j P. generalize dependent j.
  induction P; intros; inversion H0; subst.
  + destruct (link_future_equiv_link_future _ _ _ (or_intror H8)) as [? [? [? ?]]].
    destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
    destruct i1, i2...
    assert (k <= i1) by lia.
    assert (k <=? i1 = true). { apply Compare_dec.leb_correct. auto. }
    assert (k <= i2) by lia.
    assert (k <=? i2 = true). { apply Compare_dec.leb_correct. auto. }
    destruct H2, H10; subst; simpl; unfold relocate; simpl.
    - rewrite H12, H14. eapply link_tree_leaf_nn; try apply c_refl; try lia.
      * destruct M1; try congruence; inversion H1; simpl; congruence.
      * destruct M2; try congruence; inversion H7; simpl; congruence.
    - rewrite H12, H14. eapply link_tree_leaf_nn; try apply c_refl; try apply c_link; try lia.
      * destruct M1; try congruence; inversion H1; simpl; congruence.
      * destruct M2; try congruence; inversion H7; simpl; congruence.
    - rewrite H12, H14. eapply link_tree_leaf_nn; try apply c_refl; try apply c_link; try lia.
      * destruct M1; try congruence; inversion H1; simpl; congruence.
      * destruct M2; try congruence; inversion H7; simpl; congruence.
    - rewrite H12, H14. eapply link_tree_leaf_nn; try apply c_refl; try apply c_link; try lia.
      * destruct M1; try congruence; inversion H1; simpl; congruence.
      * destruct M2; try congruence; inversion H7; simpl; congruence.
  + destruct (link_future_equiv_link_future _ _ _ (or_intror H8)) as [? [? [? ?]]].
    destruct i1, i2, i3...
    assert (k <= i1) by lia.
    assert (k <=? i1 = true). { apply Compare_dec.leb_correct. auto. }
    assert (k <= i2) by lia.
    assert (k <=? i2 = true). { apply Compare_dec.leb_correct. auto. }
    assert (k <= i3) by lia.
    assert (k <=? i3 = true). { apply Compare_dec.leb_correct. auto. }
    destruct H2; subst; simpl; unfold relocate; simpl; rewrite H9, H11, H13.
    - eapply link_tree_leaf_nf; try apply c_refl; try lia.
      destruct M; try congruence; inversion H1; simpl; congruence.
    - eapply link_tree_leaf_nf; try apply c_link; try lia.
      destruct M; try congruence; inversion H1; simpl; congruence.
  + destruct (link_future_equiv_link_future _ _ _ (or_intror H8)) as [? [? [? ?]]].
    destruct i1, i2, i3...
    assert (k <= i1) by lia.
    assert (k <=? i1 = true). { apply Compare_dec.leb_correct. auto. }
    assert (k <= i2) by lia.
    assert (k <=? i2 = true). { apply Compare_dec.leb_correct. auto. }
    assert (k <= i3) by lia.
    assert (k <=? i3 = true). { apply Compare_dec.leb_correct. auto. }
    destruct H2; subst; simpl; unfold relocate; simpl; rewrite H9, H11, H13.
    - eapply link_tree_leaf_fn; try apply c_refl; try lia.
      destruct M; try congruence; inversion H1; simpl; congruence.
    - eapply link_tree_leaf_fn; try apply c_link; try lia.
      destruct M; try congruence; inversion H1; simpl; congruence.
  + destruct i1, i2, i3, i4...
    assert (k <= i1) by lia.
    assert (k <=? i1 = true). { apply Compare_dec.leb_correct. auto. }
    assert (k <= i2) by lia.
    assert (k <=? i2 = true). { apply Compare_dec.leb_correct. auto. }
    assert (k <= i3) by lia.
    assert (k <=? i3 = true). { apply Compare_dec.leb_correct. auto. }
    assert (k <= i4) by lia.
    assert (k <=? i4 = true). { apply Compare_dec.leb_correct. auto. }
    simpl; unfold relocate; simpl; rewrite H2, H8, H10, H12. apply link_tree_leaf_ff; lia.
  + destruct (link_future_equiv_link_future _ _ _ (or_intror H7)) as [? [? [? ?]]].
    destruct i'... simpl.
    assert (k <= i') by lia.
    assert (k <=? i' = true). { apply Compare_dec.leb_correct. auto. }
    eapply (link_tree_cons_nl _ _ (lift_message x (S k) 1)).
    - apply IHP2; auto; lia.
    - destruct M; try congruence; inversion H1; simpl; congruence.
    - assert (S j < (S (S i'))) by lia. apply H9.
    - destruct H2; subst; simpl; unfold relocate; simpl; rewrite H8. apply c_refl. apply c_link.
  + destruct (link_future_equiv_link_future _ _ _ (or_intror H7)) as [? [? [? ?]]].
    destruct i'... simpl.
    assert (k <= i') by lia.
    assert (k <=? i' = true). { apply Compare_dec.leb_correct. auto. }
    eapply (link_tree_cons_nr _ _ (lift_message x (S k) 1)).
    - apply IHP1; auto; lia.
    - destruct M; try congruence; inversion H1; simpl; congruence.
    - assert (S j < (S (S i'))) by lia. apply H9.
    - destruct H2; subst; simpl; unfold relocate; simpl; rewrite H8. apply c_refl. apply c_link.
  + destruct i1, i2...
    assert (k <= i1) by lia.
    assert (k <=? i1 = true). { apply Compare_dec.leb_correct. auto. }
    assert (k <= i2) by lia.
    assert (k <=? i2 = true). { apply Compare_dec.leb_correct. auto. }
    simpl; unfold relocate; simpl. rewrite H2, H7.
    apply link_tree_cons_fl; try lia. apply IHP2; auto; lia.
  + destruct i1, i2...
    assert (k <= i1) by lia.
    assert (k <=? i1 = true). { apply Compare_dec.leb_correct. auto. }
    assert (k <= i2) by lia.
    assert (k <=? i2 = true). { apply Compare_dec.leb_correct. auto. }
    simpl; unfold relocate; simpl. rewrite H2, H7.
    apply link_tree_cons_fr; try lia. apply IHP1; auto; lia.
  + simpl. apply link_tree_branch; [apply IHP1 | apply IHP2]; auto; lia.
Qed.

Lemma link_tree_up :
  forall j P,
    link_tree j P -> link_tree (S j) (up P).
Proof. intros. unfold up. apply (link_tree_lift_j_up j _ 0); auto. lia. Qed.

Local Hint Rewrite
  swap_swap_id
  down_after_up_process_id
  up_after_down_process_id
    : up_down_rename_rewrites.

(* Link treenes is preserved under structural congruence *)
Lemma struct_cong_preserves_link_tree' :
  forall n,
    forall k,
      k <= n ->
        forall j P Q,
          link_tree j P ->
          (struct_cong_d k P Q) \/ (struct_cong_d k Q P) ->
          link_tree j Q.
Proof with (try (exfalso; lia)).
  induction n; intros.
  + assert (k = 0) by lia; subst. destruct H1; inversion H1; subst.
    - inversion H0.
    - inversion H0; subst; link_tree_econstructor.
      Unshelve. all: eauto.
    - inversion H0; subst.
      * exfalso.
        destruct (link_future_equiv_link_future _ _ _ (or_intror H10)) as [? [? [? [? | ?]]]]; congruence.
      * exfalso.
        destruct (link_future_equiv_link_future _ _ _ (or_intror H10)) as [? [? [? [? | ?]]]]; congruence.
      * exfalso.
        destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? [? | ?]]]]; congruence.
      * inversion H5; subst.
        ** destruct i1; try (exfalso; lia).
           destruct (link_future_equiv_link_future _ _ _ (or_intror H14)) as [? [? [? ?]]].
           eapply link_tree_cons_nl.
           -- destruct (link_future_equiv_link_future _ _ _ (or_intror H15)) as [? [? [? ?]]].
              destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
              eapply (link_tree_leaf_nn _ _ _  (rename_message x1 swap01) (rename_message (lift_message x3 0 1) swap01)).
              ++ destruct M2; try congruence. inversion H13; simpl. congruence.
              ++ destruct M; try congruence. inversion H17; simpl. congruence.
              ++ apply H12.
              ++ assert (S j < S i') by lia. apply H19.
              ++ destruct H16; subst; destruct i2; try (exfalso; lia); simpl;
                 destruct i2; try (exfalso; lia).
                 apply c_refl. apply c_link.
              ++ destruct H18; subst; simpl. destruct i'; try (exfalso; lia).
                 { unfold relocate; simpl. apply c_refl. }
                 { destruct i'; try (exfalso; lia). apply c_link. }
           -- assert (no_future (down1_message (rename_message x swap01) 0)).
              { destruct M1; try congruence; inversion H3; subst. simpl. congruence. }
              eapply H13.
           -- assert (j < i1) by lia; eassumption.
           -- destruct (link_future_equiv_link_future _ _ _ (or_intror H14)) as [? [? [? ?]]].
              destruct H4; subst; simpl; destruct i1; simpl; try apply c_refl; try apply c_link.
        ** destruct i1, i2; try (exfalso; lia); destruct i1, i2; try (exfalso; lia).
           simpl. eapply link_tree_cons_fl; try lia.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H14)) as [? [? [? ?]]].
           destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
           eapply (link_tree_leaf_nn _ _ _  (rename_message x swap01) (rename_message (lift_message x1 0 1) swap01)).
           ++ destruct M0; try congruence. inversion H3; simpl. congruence.
           ++ destruct M; try congruence. inversion H12; simpl. congruence.
           ++ apply H13.
           ++ assert (S j < S i') by lia. apply H16.
           ++ destruct H4; subst; destruct i3; try (exfalso; lia); simpl;
              destruct i3; try (exfalso; lia).
              apply c_refl. apply c_link.
           ++ destruct H15; subst; simpl. destruct i'; try (exfalso; lia).
              { unfold relocate; simpl. apply c_refl. }
              { destruct i'; try (exfalso; lia). apply c_link. }
        ** destruct (link_future_equiv_link_future _ _ _ (or_intror H14)) as [? [? [? ?]]].
           destruct i1; try (exfalso; lia); destruct i'...
           eapply (link_tree_cons_nl _ _ (down1_message (rename_message x swap01) 0)).
           ++ destruct i2, i3... destruct i2, i3... simpl.
              destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
              eapply (link_tree_leaf_nf _ _ _ _ (rename_message (lift_message x1 0 1) swap01)); try lia.
              -- destruct M; try congruence; inversion H12; simpl; congruence.
              -- assert (S j < S (S i')) by lia. apply H16.
              -- destruct H15; subst; simpl; unfold relocate; simpl.
                 apply c_refl. apply c_link.
           ++ destruct M0; try congruence. inversion H3; simpl; congruence.
           ++ assert (j < i1) by lia. eapply H12.
           ++ destruct H4; subst; destruct i1; try (exfalso; lia); simpl.
              apply c_refl. apply c_link.
        ** destruct i1, i2, i3, i4... destruct i1, i2, i3, i4... simpl.
           apply link_tree_cons_fl; try lia.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
           eapply (link_tree_leaf_nf _ _ _ _ (rename_message (lift_message x 0 1) swap01)); try lia.
           ++ destruct M; try congruence; inversion H3; simpl; congruence.
           ++ assert (S j < S i') by lia. apply H11.
           ++ destruct H4; subst; destruct i'... simpl; unfold relocate; simpl.
              apply c_refl. apply c_link.
        ** destruct (link_future_equiv_link_future _ _ _ (or_intror H13)) as [? [? [? ?]]].
           destruct i'0...
           eapply (link_tree_cons_nl _ _ (down1_message (rename_message x swap01) 0)).
           ++ destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
              eapply (link_tree_cons_nr _ _ (rename_message (lift_message x1 0 1) swap01)).
              -- apply link_tree_SSj_swap01; auto.
              -- destruct M; try congruence; inversion H11; simpl; congruence.
              -- assert (S j < S i') by lia. apply H15.
              -- destruct H14; subst; destruct i'... all: unfold relocate; simpl;
                 unfold relocate; simpl. apply c_refl. apply c_link.
           ++ destruct M0; try congruence; inversion H3; simpl; congruence.
           ++ assert (j < i'0) by lia. apply H11.
           ++ destruct H4; subst; destruct i'0... simpl. apply c_refl. apply c_link.
        ** eapply link_tree_branch.
           ++ apply link_tree_SSj_swap01 in H7.
              apply link_tree_down; auto.
           ++ destruct (link_future_equiv_link_future _ _ _ (or_intror H13)) as [? [? [? ?]]].
              destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
              eapply (link_tree_leaf_nn _ _ _ (rename_message x swap01) (rename_message (lift_message x1 0 1) swap01)).
              -- destruct M0; try congruence; inversion H3; simpl; congruence.
              -- destruct M; try congruence; inversion H11; simpl; congruence.
              -- apply H12.
              -- assert (S j < S i') by lia. apply H15.
              -- destruct H4; subst; simpl;
                 destruct i'0... destruct i'0... simpl. apply c_refl.
                 destruct i'0... apply c_link.
              -- destruct H14; subst; simpl. all: destruct i'... all: unfold relocate; simpl.
                 apply c_refl. apply c_link.
        ** destruct i1, i2... destruct i1, i2... simpl.
           apply link_tree_cons_fl; try lia.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
           eapply (link_tree_cons_nr _ _ (rename_message (lift_message x 0 1) swap01)).
           -- apply link_tree_SSj_swap01; auto.
           -- destruct M; try congruence; inversion H3; simpl; congruence.
           -- assert (S j < S i') by lia. apply H10.
           -- destruct H4; subst; destruct i'... all: simpl; unfold relocate; simpl.
              apply c_refl. apply c_link.
        ** apply link_tree_branch.
           -- apply link_tree_down. apply link_tree_SSj_swap01; auto.
           -- destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
              destruct i1, i2... destruct i1, i2... simpl.
              eapply (link_tree_leaf_nf _ _ _ _ (rename_message (lift_message x 0 1) swap01)); try lia.
              ++ destruct M; try congruence; inversion H3; simpl; congruence.
              ++ assert (S j < S i') by lia. apply H10.
              ++ destruct H4; subst; destruct i'... all: simpl; unfold relocate; simpl.
                 apply c_refl. apply c_link.
        ** apply link_tree_branch.
           -- apply link_tree_down. apply link_tree_SSj_swap01; auto.
           -- destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
              eapply (link_tree_cons_nr _ _ (rename_message (lift_message x 0 1) swap01)).
              ++ apply link_tree_SSj_swap01; auto.
              ++ destruct M; try congruence; inversion H3; simpl; congruence.
              ++ assert (S j < S i') by lia. apply H7.
              ++ destruct H4; subst; destruct i'... all: simpl; unfold relocate; simpl.
                 apply c_refl. apply c_link.
      * inversion H5; subst.
        ** destruct i1, i2... simpl. unfold relocate. simpl.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H13)) as [? [? [? ?]]].
           destruct (link_future_equiv_link_future _ _ _ (or_intror H14)) as [? [? [? ?]]].
           destruct i0... destruct i3... destruct i3...
           eapply (link_tree_cons_nl _ _ (down1_message (rename_message x swap01) 0)).
           ++ eapply (link_tree_leaf_fn _ _ _ _ (rename_message x1 swap01)).
              -- destruct M2; try congruence; inversion H12; simpl; congruence.
              -- apply H11.
              -- lia.
              -- lia.
              -- destruct H15; subst; simpl. apply c_refl. apply c_link.
           ++ destruct M1; try congruence; inversion H3; simpl; congruence.
           ++ assert (j < i0) by lia. apply H16.
           ++ destruct H4; subst; destruct i0... all: simpl. apply c_refl. apply c_link.
        ** destruct i0, i3, i1, i2... destruct i0, i3... simpl.
           apply link_tree_cons_fl; try lia.
           unfold relocate; simpl.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H13)) as [? [? [? ?]]].
           eapply (link_tree_leaf_fn _ _ _ _ (rename_message x swap01)); try lia.
           -- destruct M; try congruence; inversion H3; simpl; congruence.
           -- apply H12.
           -- destruct H4; subst; destruct i4... all: destruct i4... all: simpl.
              apply c_refl. apply c_link.
        ** destruct i1, i2, i3, i4... destruct i3, i4... simpl; unfold relocate; simpl.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H13)) as [? [? [? ?]]].
           destruct i0...
           eapply (link_tree_cons_nl _ _ (down1_message (rename_message x swap01) 0)).
           -- apply link_tree_leaf_ff; try lia.
           -- destruct M; try congruence; inversion H3; simpl; congruence.
           -- assert (j < i0) by lia. apply H11.
           -- destruct H4; subst; destruct i0... all: simpl.
              apply c_refl. apply c_link.
        ** destruct i0, i3, i4, i5, i1, i2... destruct i0, i3, i4, i5... simpl.
           unfold relocate. simpl.
           apply link_tree_cons_fl; try lia.
           apply link_tree_leaf_ff; try lia.
        ** destruct i1, i2... simpl; unfold relocate; simpl.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H12)) as [? [? [? ?]]].
           destruct i'...
           eapply (link_tree_cons_nl _ _ (down1_message (rename_message x swap01) 0)).
           -- apply link_tree_cons_fr; try lia. apply link_tree_SSj_swap01; auto.
           -- destruct M; try congruence; inversion H3; simpl; congruence.
           -- assert (j < i') by lia. apply H10.
           -- destruct H4; subst; destruct i'... all: simpl. apply c_refl. apply c_link.
        ** destruct i1, i2... simpl; unfold relocate; simpl.
           apply link_tree_branch.
           -- apply link_tree_down. apply link_tree_SSj_swap01; auto.
           -- destruct (link_future_equiv_link_future _ _ _ (or_intror H12)) as [? [? [? ?]]].
              destruct i'...
              eapply (link_tree_leaf_fn _ _ _ _ (rename_message x swap01)); try lia.
              ++ destruct M; try congruence; inversion H3; simpl; congruence.
              ++ apply H11.
              ++ destruct H4; subst; destruct i'... all: simpl. apply c_refl. apply c_link.
        ** destruct i0, i3, i1, i2... destruct i0, i3... simpl; unfold relocate; simpl.
           apply link_tree_cons_fl; try lia.
           apply link_tree_cons_fr; try lia.
           apply link_tree_SSj_swap01; auto.
        ** destruct i0, i3, i1, i2... destruct i0, i3... simpl; unfold relocate; simpl.
           apply link_tree_branch.
           -- apply link_tree_down. apply link_tree_SSj_swap01; auto.
           -- apply link_tree_leaf_ff; lia.
        ** destruct i1, i2... simpl; unfold relocate; simpl.
           apply link_tree_branch.
           -- apply link_tree_down. apply link_tree_SSj_swap01; auto.
           -- apply link_tree_cons_fr; try lia. apply link_tree_SSj_swap01; auto.
      * assert (link_tree (S (S j)) (rename_process (up R) swap01)).
        { apply link_tree_SSj_swap01. apply link_tree_up; auto. }
        inversion H6; subst.
        ** destruct (link_future_equiv_link_future _ _ _ (or_intror H13)) as [? [? [? ?]]].
           destruct i1... destruct i2...
           eapply (link_tree_cons_nl _ _ (down1_message (rename_message x swap01) 0)).
           ++ destruct (link_future_equiv_link_future _ _ _ (or_intror H14)) as [? [? [? ?]]].
              eapply (link_tree_cons_nl _ _ (rename_message x1 swap01)).
              -- auto.
              -- destruct M2; try congruence; inversion H12; simpl; congruence.
              -- apply H11.
              -- destruct H15; subst; destruct i2... all: simpl. apply c_refl. apply c_link.
           ++ destruct M1; try congruence; inversion H4; simpl; congruence.
           ++ assert (j < i1) by lia. apply H12.
           ++ destruct H5; subst; destruct i1... all: simpl. apply c_refl. apply c_link.
        ** destruct i1, i2... destruct i1, i2... simpl.
           apply link_tree_cons_fl; try lia. destruct i3...
           destruct (link_future_equiv_link_future _ _ _ (or_intror H13)) as [? [? [? ?]]].
           eapply (link_tree_cons_nl _ _ (rename_message x swap01)).
           ++ auto.
           ++ destruct M; try congruence; inversion H4; simpl; congruence.
           ++ apply H12.
           ++ destruct H5; subst; destruct i3... all: simpl. apply c_refl. apply c_link.
        ** destruct i2, i3... destruct i2, i3... simpl.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H13)) as [? [? [? ?]]].
           destruct i1...
           eapply (link_tree_cons_nl _ _ (down1_message (rename_message x swap01) 0)).
           ++ apply link_tree_cons_fl; try lia. auto.
           ++ destruct M; try congruence; inversion H4; simpl; congruence.
           ++ assert (j < i1) by lia. apply H11.
           ++ destruct H5; subst; destruct i1... all: simpl. apply c_refl. apply c_link.
        ** destruct i1, i2, i3, i4... destruct i1, i2, i3, i4... simpl.
           apply link_tree_cons_fl; try lia.
           apply link_tree_cons_fl; try lia.
           auto.
        ** apply link_tree_SSj_swap01 in H8.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H12)) as [? [? [? ?]]].
           destruct i'...
           eapply (link_tree_cons_nl _ _ (down1_message (rename_message x swap01) 0)).
           ++ link_tree_econstructor.
           ++ destruct M; try congruence; inversion H4; simpl; congruence.
           ++ assert (j < i') by lia. apply H10.
           ++ destruct H5; subst; destruct i'... all: simpl. apply c_refl. apply c_link.
        ** apply link_tree_branch.
           ++ apply link_tree_down. apply link_tree_SSj_swap01; auto.
           ++ destruct (link_future_equiv_link_future _ _ _ (or_intror H12)) as [? [? [? ?]]].
              destruct i'...
              eapply (link_tree_cons_nl _ _ (rename_message x swap01)).
              -- apply link_tree_SSj_swap01. apply link_tree_up; auto.
              -- destruct M; try congruence; inversion H4; simpl; congruence.
              -- assert (j < i') by lia. apply H11.
              -- destruct H5; subst; destruct i'... all: simpl. apply c_refl. apply c_link.
        ** destruct i1, i2... destruct i1, i2... simpl.
           apply link_tree_cons_fl; try lia. apply link_tree_branch; auto.
           apply link_tree_SSj_swap01; auto.
        ** destruct i1, i2... destruct i1, i2... simpl.
           apply link_tree_branch. { apply link_tree_down; apply link_tree_SSj_swap01; auto. }
           apply link_tree_cons_fl; try lia; auto.
        ** apply link_tree_branch. { apply link_tree_down; apply link_tree_SSj_swap01; auto. }
           apply link_tree_branch. { apply link_tree_SSj_swap01; auto. }
           auto.
    - auto.
    (* symmetric to the previous cases *)
    - inversion H0.
    - inversion H0; subst; link_tree_econstructor. Unshelve. all: eauto.
    - inversion H0; subst.
      * exfalso.
        destruct (link_future_equiv_link_future _ _ _ (or_intror H11)) as [? [? [? [? | ?]]]]; destruct P0; simpl in *; congruence.
      * exfalso.
        destruct (link_future_equiv_link_future _ _ _ (or_intror H10)) as [? [? [? [? | ?]]]]; congruence.
      * assert (link_tree (S j) (cut P0 Q0)).
        {
          destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [HM H']]].
          destruct i'...
          inversion H5; subst;
          try match goal with
          | [ H : (rename_process ?Q swap01) ≡ (link (future ?i) ?M1),
              Hj : S ?j < ?i
            |- link_tree (S ?j) (cut _ ?Q) ]
            => destruct (link_future_equiv_link_future _ _ _ (or_intror H)) as [x1 [? [HM1 H'']]];
               eapply (link_tree_leaf_nn _ _ _ (rename_message (lift_message x 0 1) swap01) (rename_message x1 swap01));
               [ destruct M; try congruence; inversion HM; simpl; congruence
               | destruct M1; try congruence; inversion HM1; simpl; congruence
               | assert (S j < S (S i')) as Hji by lia; apply Hji
               | apply Hj
               | replace P0 with (rename_process (up (down (rename_process P0 swap01))) swap01)
                  by (autorewrite with up_down_rename_rewrites; auto; apply nfv_01_swap; auto);
                  destruct H' as [H1' | H2'];
                  [ rewrite H1'; simpl; unfold relocate; simpl; apply c_refl
                  | rewrite H2'; simpl; unfold relocate; simpl; apply c_link
                  ]
               | replace Q with (rename_process (rename_process Q swap01) swap01)
                  by (autorewrite with up_down_rename_rewrites; auto);
                 destruct i; try (exfalso; lia);
                 destruct i; try (exfalso; lia);
                 destruct H'' as [H1'' | H2''];
                 [ rewrite H1''; simpl; apply c_refl
                 | rewrite H2''; simpl; apply c_link
                 ]
               ]
          | [ H : link (future ?i1) (future ?i2) = rename_process ?Q swap01,
              Hj : S ?j < ?i
            |- link_tree (S ?j) (cut _ ?Q) ]
            => replace Q with (rename_process (rename_process Q swap01) swap01)
                by (autorewrite with up_down_rename_rewrites; auto);
               rewrite <- H;
               destruct i1, i2; try (exfalso; lia);
               destruct i1, i2; try (exfalso; lia);
               simpl;
               eapply (link_tree_leaf_fn _ _ _ _ (rename_message (lift_message x 0 1) swap01)); try lia;
               [ destruct M; try congruence; inversion HM; simpl; congruence
               | assert (S j < S (S i')) as Hji by lia; apply Hji
               | replace P0 with (rename_process (up (down (rename_process P0 swap01))) swap01)
                  by (autorewrite with up_down_rename_rewrites; auto; apply nfv_01_swap; auto);
                 destruct H' as [H1' | H2'];
                 [ rewrite H1'; simpl; unfold relocate; simpl; apply c_refl
                 | rewrite H2'; simpl; unfold relocate; simpl; apply c_link
                 ]
               ]
          | [ H : link_tree (S (S ?j)) (rename_process ?Q swap01)
            |- link_tree (S ?j) (cut _ ?Q) ]
            => apply link_tree_SSj_swap01 in H;
               autorewrite with up_down_rename_rewrites in H;
               eapply (link_tree_cons_nl _ _ (rename_message (lift_message x 0 1) swap01));
               [ auto
               | destruct M; try congruence; inversion HM; simpl; congruence
               | assert (S j < S (S i')) as Hji by lia; apply Hji
               | replace P0 with (rename_process (up (down (rename_process P0 swap01))) swap01)
                  by (autorewrite with up_down_rename_rewrites; auto; apply nfv_01_swap; auto);
                 destruct H' as [H1' | H2'];
                 [ rewrite H1'; simpl; unfold relocate; simpl; apply c_refl
                 | rewrite H2'; simpl; unfold relocate; simpl; apply c_link
                 ]
               ]
          end.
        }
        inversion H5; subst;
        try match goal with
        | [ H : (rename_process (up ?R) swap01) ≡ (link (future ?i) ?M)
          |- link_tree ?j (cut _ ?R) ]
          => destruct (link_future_equiv_link_future _ _ _ (or_intror H)) as [x [? [Hx HR]]];
             destruct i as [|i]; try (exfalso; lia);
             eapply (link_tree_cons_nr _ _ (down1_message (rename_message x swap01) 0));
             [ auto
             | destruct M; try congruence; inversion Hx; simpl; congruence
             | assert (j < i) as Hji by lia; apply Hji
             | destruct HR as [HR1 | HR2];
               replace R with (down (rename_process (rename_process (up R) swap01) swap01))
                 by (autorewrite with up_down_rename_rewrites; reflexivity);
             [ rewrite HR1; destruct i; try (exfalso; lia); simpl; apply c_refl
             | rewrite HR2; destruct i; try (exfalso; lia); simpl; apply c_link
             ]
             ]
        | [ H : (link (future ?i) (future ?i')) = (rename_process (up ?R) swap01)
          |- link_tree ?j (cut _ ?R) ]
          => replace R with (down (rename_process (rename_process (up R) swap01) swap01))
               by (autorewrite with up_down_rename_rewrites; reflexivity);
             rewrite <- H;
             destruct i, i'; try (exfalso; lia);
             destruct i, i'; try (exfalso; lia);
             simpl;
             apply link_tree_cons_fr; try lia; auto
        | [ H : link_tree (S (S ?j)) (rename_process (up ?R) swap01)
          |- link_tree ?j (cut _ ?R) ]
          => apply link_tree_SSj_swap01 in H; apply link_tree_up in H;
             autorewrite with up_down_rename_rewrites in H;
             eapply link_tree_down with (k := 0) in H;
             eapply link_tree_down with (k := 0) in H;
             replace (down1_process (down1_process (up (up R)) 0) 0) with (down (down (up (up R)))) in H by reflexivity;
             autorewrite with up_down_rename_rewrites in H;
             link_tree_econstructor
        end.
      * exfalso.
        destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? [? | ?]]]]; congruence.
      * assert (link_tree (S j) (cut P0 Q0)).
        {
          inversion H5; subst;
          try match goal with
          | [ H : (rename_process ?Q swap01) ≡ (link (future ?i) ?M1),
              Hj : S ?j < ?i
            |- link_tree (S ?j) (cut _ ?Q) ]
            => replace P0 with (rename_process (up (down (rename_process P0 swap01))) swap01)
                by (autorewrite with up_down_rename_rewrites; auto; apply nfv_01_swap; auto);
                rewrite <- H3;
                destruct i1, i2; try (exfalso; lia); simpl; unfold relocate; simpl;
                destruct (link_future_equiv_link_future _ _ _ (or_intror H)) as [x1 [? [HM1 H'']]];
                eapply (link_tree_leaf_nf _ _ _ _ (rename_message x1 swap01)); try lia;
                [ destruct M1; try congruence; inversion HM1; simpl; congruence
                | apply Hj
                | replace Q with (rename_process (rename_process Q swap01) swap01)
                    by (autorewrite with up_down_rename_rewrites; auto);
                  destruct i; try (exfalso; lia);
                  destruct i; try (exfalso; lia);
                  destruct H'' as [H1'' | H2''];
                  [ rewrite H1''; simpl; apply c_refl
                  | rewrite H2''; simpl; apply c_link
                  ]
                ]
          | [ H : link (future ?i0) (future ?i3) = rename_process ?Q swap01
            |- link_tree (S ?j) (cut _ ?Q) ]
            => replace P0 with (rename_process (up (down (rename_process P0 swap01))) swap01)
                  by (autorewrite with up_down_rename_rewrites; auto; apply nfv_01_swap; auto);
               rewrite <- H3;
               replace Q with (rename_process (rename_process Q swap01) swap01)
                  by (autorewrite with up_down_rename_rewrites; auto);
               rewrite <- H;
               destruct i0, i3, i2, i1; try (exfalso; lia);
               destruct i0, i3; try (exfalso; lia);
               simpl; unfold relocate; simpl;
               eapply link_tree_leaf_ff; try lia
          | [ H : link_tree (S (S j)) (rename_process Q0 swap01)
            |- link_tree (S ?j) (cut _ ?Q) ]
            => apply link_tree_SSj_swap01 in H;
               autorewrite with up_down_rename_rewrites in H;
               replace P0 with (rename_process (up (down (rename_process P0 swap01))) swap01)
                  by (autorewrite with up_down_rename_rewrites; auto; apply nfv_01_swap; auto);
               rewrite <- H3;
               destruct i1, i2; try (exfalso; lia); simpl; unfold relocate; simpl;
               eapply link_tree_cons_fl; auto; try lia
          end.
        }
        inversion H5; subst;
        try match goal with
        | [ H : (rename_process (up ?R) swap01) ≡ (link (future ?i) ?M)
          |- link_tree ?j (cut _ ?R) ]
          => destruct (link_future_equiv_link_future _ _ _ (or_intror H)) as [x [? [Hx HR]]];
             destruct i as [|i]; try (exfalso; lia);
             eapply (link_tree_cons_nr _ _ (down1_message (rename_message x swap01) 0));
             [ auto
             | destruct M; try congruence; inversion Hx; simpl; congruence
             | assert (j < i) as Hji by lia; apply Hji
             | destruct HR as [HR1 | HR2];
               replace R with (down (rename_process (rename_process (up R) swap01) swap01))
                 by (autorewrite with up_down_rename_rewrites; reflexivity);
             [ rewrite HR1; destruct i; try (exfalso; lia); simpl; apply c_refl
             | rewrite HR2; destruct i; try (exfalso; lia); simpl; apply c_link
             ]
             ]
        | [ H : (link (future ?i) (future ?i')) = (rename_process (up ?R) swap01)
          |- link_tree ?j (cut _ ?R) ]
          => replace R with (down (rename_process (rename_process (up R) swap01) swap01))
               by (autorewrite with up_down_rename_rewrites; reflexivity);
             rewrite <- H;
             destruct i, i'; try (exfalso; lia);
             destruct i, i'; try (exfalso; lia);
             simpl;
             apply link_tree_cons_fr; try lia; auto
        | [ H : link_tree (S (S ?j)) (rename_process (up ?R) swap01)
          |- link_tree ?j (cut _ ?R) ]
          => apply link_tree_SSj_swap01 in H; apply link_tree_up in H;
             autorewrite with up_down_rename_rewrites in H;
             eapply link_tree_down with (k := 0) in H;
             eapply link_tree_down with (k := 0) in H;
             replace (down1_process (down1_process (up (up R)) 0) 0) with (down (down (up (up R)))) in H by reflexivity;
             autorewrite with up_down_rename_rewrites in H;
             link_tree_econstructor
        end.
      * assert (link_tree (S j) (cut P0 Q0)).
        {
          assert (link_tree (S (S j)) P0).
          {
            apply link_tree_up in H6. apply link_tree_SSj_swap01 in H6;
            autorewrite with up_down_rename_rewrites in H6; auto.
            apply nfv_01_swap; auto.
          }
          inversion H7; subst;
          try match goal with
          | [ H : (rename_process ?Q swap01) ≡ (link (future ?i) ?M1),
              Hj : S ?j < ?i
            |- link_tree (S ?j) (cut _ ?Q) ]
            => destruct (link_future_equiv_link_future _ _ _ (or_intror H)) as [x1 [? [HM1 H'']]];
               eapply (link_tree_cons_nr _ _ (rename_message x1 swap01)); try lia;
               [ auto
               | destruct M1; try congruence; inversion HM1; simpl; congruence
               | apply Hj
               | replace Q with (rename_process (rename_process Q swap01) swap01)
                   by (autorewrite with up_down_rename_rewrites; auto);
                 destruct i; try (exfalso; lia);
                 destruct i; try (exfalso; lia);
                 destruct H'' as [H1'' | H2''];
                 [ rewrite H1''; simpl; apply c_refl
                 | rewrite H2''; simpl; apply c_link
                 ]
               ]
          | [ H : link (future ?i1) (future ?i2) = rename_process ?Q swap01
            |- link_tree (S ?j) (cut _ ?Q) ]
            => replace Q with (rename_process (rename_process Q swap01) swap01)
                   by (autorewrite with up_down_rename_rewrites; auto);
               rewrite <- H;
               destruct i1, i2; try (exfalso; lia);
               destruct i1, i2; try (exfalso; lia);
               simpl;
               apply link_tree_cons_fr; try lia; auto
          | [ H : link_tree (S (S j)) (rename_process Q0 swap01)
            |- link_tree (S ?j) (cut _ ?Q) ]
            => apply link_tree_SSj_swap01 in H;
               autorewrite with up_down_rename_rewrites in H;
               apply link_tree_branch; auto
          end.
        }
        inversion H7; subst;
        try match goal with
        | [ H : (rename_process (up ?R) swap01) ≡ (link (future ?i) ?M)
          |- link_tree ?j (cut _ ?R) ]
          => destruct (link_future_equiv_link_future _ _ _ (or_intror H)) as [x [? [Hx HR]]];
             destruct i as [|i]; try (exfalso; lia);
             eapply (link_tree_cons_nr _ _ (down1_message (rename_message x swap01) 0));
             [ auto
             | destruct M; try congruence; inversion Hx; simpl; congruence
             | assert (j < i) as Hji by lia; apply Hji
             | destruct HR as [HR1 | HR2];
               replace R with (down (rename_process (rename_process (up R) swap01) swap01))
                 by (autorewrite with up_down_rename_rewrites; reflexivity);
             [ rewrite HR1; destruct i; try (exfalso; lia); simpl; apply c_refl
             | rewrite HR2; destruct i; try (exfalso; lia); simpl; apply c_link
             ]
             ]
        | [ H : (link (future ?i) (future ?i')) = (rename_process (up ?R) swap01)
          |- link_tree ?j (cut _ ?R) ]
          => replace R with (down (rename_process (rename_process (up R) swap01) swap01))
               by (autorewrite with up_down_rename_rewrites; reflexivity);
             rewrite <- H;
             destruct i, i'; try (exfalso; lia);
             destruct i, i'; try (exfalso; lia);
             simpl;
             apply link_tree_cons_fr; try lia; auto
        | [ H : link_tree (S (S ?j)) (rename_process (up ?R) swap01)
          |- link_tree ?j (cut _ ?R) ]
          => apply link_tree_SSj_swap01 in H; apply link_tree_up in H;
             autorewrite with up_down_rename_rewrites in H;
             eapply link_tree_down with (k := 0) in H;
             eapply link_tree_down with (k := 0) in H;
             replace (down1_process (down1_process (up (up R)) 0) 0) with (down (down (up (up R)))) in H by reflexivity;
             autorewrite with up_down_rename_rewrites in H;
             link_tree_econstructor
        end.
    - auto.
  + destruct H1.
    - inversion H1; subst.
      * inversion H0.
      * inversion H0; subst; try link_tree_econstructor.
        Unshelve. all: eauto.
      * inversion H0; subst.
        ** exfalso.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H10)) as [? [? [? [? | ?]]]]; congruence.
        ** exfalso.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H10)) as [? [? [? [? | ?]]]]; congruence.
        ** exfalso.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? [? | ?]]]]; congruence.
        ** inversion H5; subst.
           *** destruct i1; try (exfalso; lia).
               destruct (link_future_equiv_link_future _ _ _ (or_intror H14)) as [? [? [? ?]]].
               eapply link_tree_cons_nl.
               -- destruct (link_future_equiv_link_future _ _ _ (or_intror H15)) as [? [? [? ?]]].
                  destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
                  eapply (link_tree_leaf_nn _ _ _  (rename_message x1 swap01) (rename_message (lift_message x3 0 1) swap01)).
                  ++ destruct M2; try congruence. inversion H13; simpl. congruence.
                  ++ destruct M; try congruence. inversion H17; simpl. congruence.
                  ++ apply H12.
                  ++ assert (S j < S i') by lia. apply H19.
                  ++ destruct H16; subst; destruct i2; try (exfalso; lia); simpl;
                     destruct i2; try (exfalso; lia).
                     apply c_refl. apply c_link.
                  ++ destruct H18; subst; simpl. destruct i'; try (exfalso; lia).
                     { unfold relocate; simpl. apply c_refl. }
                     { destruct i'; try (exfalso; lia). apply c_link. }
               -- assert (no_future (down1_message (rename_message x swap01) 0)).
                  { destruct M1; try congruence; inversion H3; subst. simpl. congruence. }
                  eapply H13.
               -- assert (j < i1) by lia; eassumption.
               -- destruct (link_future_equiv_link_future _ _ _ (or_intror H14)) as [? [? [? ?]]].
                  destruct H4; subst; simpl; destruct i1; simpl; try apply c_refl; try apply c_link.
           *** destruct i1, i2; try (exfalso; lia); destruct i1, i2; try (exfalso; lia).
               simpl. eapply link_tree_cons_fl; try lia.
               destruct (link_future_equiv_link_future _ _ _ (or_intror H14)) as [? [? [? ?]]].
               destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
               eapply (link_tree_leaf_nn _ _ _  (rename_message x swap01) (rename_message (lift_message x1 0 1) swap01)).
               ++ destruct M0; try congruence. inversion H3; simpl. congruence.
               ++ destruct M; try congruence. inversion H12; simpl. congruence.
               ++ apply H13.
               ++ assert (S j < S i') by lia. apply H16.
               ++ destruct H4; subst; destruct i3; try (exfalso; lia); simpl;
                  destruct i3; try (exfalso; lia).
                  apply c_refl. apply c_link.
               ++ destruct H15; subst; simpl. destruct i'; try (exfalso; lia).
                  { unfold relocate; simpl. apply c_refl. }
                  { destruct i'; try (exfalso; lia). apply c_link. }
           *** destruct (link_future_equiv_link_future _ _ _ (or_intror H14)) as [? [? [? ?]]].
               destruct i1; try (exfalso; lia); destruct i'...
               eapply (link_tree_cons_nl _ _ (down1_message (rename_message x swap01) 0)).
               ++ destruct i2, i3... destruct i2, i3... simpl.
                  destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
                  eapply (link_tree_leaf_nf _ _ _ _ (rename_message (lift_message x1 0 1) swap01)); try lia.
                  -- destruct M; try congruence; inversion H12; simpl; congruence.
                  -- assert (S j < S (S i')) by lia. apply H16.
                  -- destruct H15; subst; simpl; unfold relocate; simpl.
                     apply c_refl. apply c_link.
               ++ destruct M0; try congruence. inversion H3; simpl; congruence.
               ++ assert (j < i1) by lia. eapply H12.
               ++ destruct H4; subst; destruct i1; try (exfalso; lia); simpl.
                  apply c_refl. apply c_link.
           *** destruct i1, i2, i3, i4... destruct i1, i2, i3, i4... simpl.
               apply link_tree_cons_fl; try lia.
               destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
               eapply (link_tree_leaf_nf _ _ _ _ (rename_message (lift_message x 0 1) swap01)); try lia.
               ++ destruct M; try congruence; inversion H3; simpl; congruence.
               ++ assert (S j < S i') by lia. apply H11.
               ++ destruct H4; subst; destruct i'... simpl; unfold relocate; simpl.
                  apply c_refl. apply c_link.
           *** destruct (link_future_equiv_link_future _ _ _ (or_intror H13)) as [? [? [? ?]]].
               destruct i'0...
               eapply (link_tree_cons_nl _ _ (down1_message (rename_message x swap01) 0)).
               ++ destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
                  eapply (link_tree_cons_nr _ _ (rename_message (lift_message x1 0 1) swap01)).
                  -- apply link_tree_SSj_swap01; auto.
                  -- destruct M; try congruence; inversion H11; simpl; congruence.
                  -- assert (S j < S i') by lia. apply H15.
                  -- destruct H14; subst; destruct i'... all: unfold relocate; simpl;
                     unfold relocate; simpl. apply c_refl. apply c_link.
               ++ destruct M0; try congruence; inversion H3; simpl; congruence.
               ++ assert (j < i'0) by lia. apply H11.
               ++ destruct H4; subst; destruct i'0... simpl. apply c_refl. apply c_link.
           *** eapply link_tree_branch.
               ++ apply link_tree_SSj_swap01 in H7.
                  apply link_tree_down; auto.
               ++ destruct (link_future_equiv_link_future _ _ _ (or_intror H13)) as [? [? [? ?]]].
                  destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
                  eapply (link_tree_leaf_nn _ _ _ (rename_message x swap01) (rename_message (lift_message x1 0 1) swap01)).
                  -- destruct M0; try congruence; inversion H3; simpl; congruence.
                  -- destruct M; try congruence; inversion H11; simpl; congruence.
                  -- apply H12.
                  -- assert (S j < S i') by lia. apply H15.
                  -- destruct H4; subst; simpl;
                     destruct i'0... destruct i'0... simpl. apply c_refl.
                     destruct i'0... apply c_link.
                  -- destruct H14; subst; simpl. all: destruct i'... all: unfold relocate; simpl.
                     apply c_refl. apply c_link.
           *** destruct i1, i2... destruct i1, i2... simpl.
               apply link_tree_cons_fl; try lia.
               destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
               eapply (link_tree_cons_nr _ _ (rename_message (lift_message x 0 1) swap01)).
               -- apply link_tree_SSj_swap01; auto.
               -- destruct M; try congruence; inversion H3; simpl; congruence.
               -- assert (S j < S i') by lia. apply H10.
               -- destruct H4; subst; destruct i'... all: simpl; unfold relocate; simpl.
                  apply c_refl. apply c_link.
           *** apply link_tree_branch.
               -- apply link_tree_down. apply link_tree_SSj_swap01; auto.
               -- destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
                  destruct i1, i2... destruct i1, i2... simpl.
                  eapply (link_tree_leaf_nf _ _ _ _ (rename_message (lift_message x 0 1) swap01)); try lia.
                  ++ destruct M; try congruence; inversion H3; simpl; congruence.
                  ++ assert (S j < S i') by lia. apply H10.
                  ++ destruct H4; subst; destruct i'... all: simpl; unfold relocate; simpl.
                     apply c_refl. apply c_link.
           *** apply link_tree_branch.
               -- apply link_tree_down. apply link_tree_SSj_swap01; auto.
               -- destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? ?]]].
                  eapply (link_tree_cons_nr _ _ (rename_message (lift_message x 0 1) swap01)).
                  ++ apply link_tree_SSj_swap01; auto.
                  ++ destruct M; try congruence; inversion H3; simpl; congruence.
                  ++ assert (S j < S i') by lia. apply H7.
                  ++ destruct H4; subst; destruct i'... all: simpl; unfold relocate; simpl.
                     apply c_refl. apply c_link.
        ** inversion H5; subst.
           *** destruct i1, i2... simpl. unfold relocate. simpl.
               destruct (link_future_equiv_link_future _ _ _ (or_intror H13)) as [? [? [? ?]]].
               destruct (link_future_equiv_link_future _ _ _ (or_intror H14)) as [? [? [? ?]]].
               destruct i0... destruct i3... destruct i3...
               eapply (link_tree_cons_nl _ _ (down1_message (rename_message x swap01) 0)).
               ++ eapply (link_tree_leaf_fn _ _ _ _ (rename_message x1 swap01)).
                  -- destruct M2; try congruence; inversion H12; simpl; congruence.
                  -- apply H11.
                  -- lia.
                  -- lia.
                  -- destruct H15; subst; simpl. apply c_refl. apply c_link.
               ++ destruct M1; try congruence; inversion H3; simpl; congruence.
               ++ assert (j < i0) by lia. apply H16.
               ++ destruct H4; subst; destruct i0... all: simpl. apply c_refl. apply c_link.
           *** destruct i0, i3, i1, i2... destruct i0, i3... simpl.
               apply link_tree_cons_fl; try lia.
               unfold relocate; simpl.
               destruct (link_future_equiv_link_future _ _ _ (or_intror H13)) as [? [? [? ?]]].
               eapply (link_tree_leaf_fn _ _ _ _ (rename_message x swap01)); try lia.
               -- destruct M; try congruence; inversion H3; simpl; congruence.
               -- apply H12.
               -- destruct H4; subst; destruct i4... all: destruct i4... all: simpl.
                  apply c_refl. apply c_link.
           *** destruct i1, i2, i3, i4... destruct i3, i4... simpl; unfold relocate; simpl.
               destruct (link_future_equiv_link_future _ _ _ (or_intror H13)) as [? [? [? ?]]].
               destruct i0...
               eapply (link_tree_cons_nl _ _ (down1_message (rename_message x swap01) 0)).
               -- apply link_tree_leaf_ff; try lia.
               -- destruct M; try congruence; inversion H3; simpl; congruence.
               -- assert (j < i0) by lia. apply H11.
               -- destruct H4; subst; destruct i0... all: simpl.
                  apply c_refl. apply c_link.
           *** destruct i0, i3, i4, i5, i1, i2... destruct i0, i3, i4, i5... simpl.
               unfold relocate. simpl.
               apply link_tree_cons_fl; try lia.
               apply link_tree_leaf_ff; try lia.
           *** destruct i1, i2... simpl; unfold relocate; simpl.
               destruct (link_future_equiv_link_future _ _ _ (or_intror H12)) as [? [? [? ?]]].
               destruct i'...
               eapply (link_tree_cons_nl _ _ (down1_message (rename_message x swap01) 0)).
               -- apply link_tree_cons_fr; try lia. apply link_tree_SSj_swap01; auto.
               -- destruct M; try congruence; inversion H3; simpl; congruence.
               -- assert (j < i') by lia. apply H10.
               -- destruct H4; subst; destruct i'... all: simpl. apply c_refl. apply c_link.
           *** destruct i1, i2... simpl; unfold relocate; simpl.
               apply link_tree_branch.
               -- apply link_tree_down. apply link_tree_SSj_swap01; auto.
               -- destruct (link_future_equiv_link_future _ _ _ (or_intror H12)) as [? [? [? ?]]].
                  destruct i'...
                  eapply (link_tree_leaf_fn _ _ _ _ (rename_message x swap01)); try lia.
                  ++ destruct M; try congruence; inversion H3; simpl; congruence.
                  ++ apply H11.
                  ++ destruct H4; subst; destruct i'... all: simpl. apply c_refl. apply c_link.
           *** destruct i0, i3, i1, i2... destruct i0, i3... simpl; unfold relocate; simpl.
               apply link_tree_cons_fl; try lia.
               apply link_tree_cons_fr; try lia.
               apply link_tree_SSj_swap01; auto.
           *** destruct i0, i3, i1, i2... destruct i0, i3... simpl; unfold relocate; simpl.
               apply link_tree_branch.
               -- apply link_tree_down. apply link_tree_SSj_swap01; auto.
               -- apply link_tree_leaf_ff; lia.
           *** destruct i1, i2... simpl; unfold relocate; simpl.
               apply link_tree_branch.
               -- apply link_tree_down. apply link_tree_SSj_swap01; auto.
               -- apply link_tree_cons_fr; try lia. apply link_tree_SSj_swap01; auto.
        ** assert (link_tree (S (S j)) (rename_process (up R) swap01)).
           { apply link_tree_SSj_swap01. apply link_tree_up; auto. }
           inversion H6; subst.
           *** destruct (link_future_equiv_link_future _ _ _ (or_intror H13)) as [? [? [? ?]]].
               destruct i1... destruct i2...
               eapply (link_tree_cons_nl _ _ (down1_message (rename_message x swap01) 0)).
               ++ destruct (link_future_equiv_link_future _ _ _ (or_intror H14)) as [? [? [? ?]]].
                  eapply (link_tree_cons_nl _ _ (rename_message x1 swap01)).
                  -- auto.
                  -- destruct M2; try congruence; inversion H12; simpl; congruence.
                  -- apply H11.
                  -- destruct H15; subst; destruct i2... all: simpl. apply c_refl. apply c_link.
               ++ destruct M1; try congruence; inversion H4; simpl; congruence.
               ++ assert (j < i1) by lia. apply H12.
               ++ destruct H5; subst; destruct i1... all: simpl. apply c_refl. apply c_link.
           *** destruct i1, i2... destruct i1, i2... simpl.
               apply link_tree_cons_fl; try lia. destruct i3...
               destruct (link_future_equiv_link_future _ _ _ (or_intror H13)) as [? [? [? ?]]].
               eapply (link_tree_cons_nl _ _ (rename_message x swap01)).
               ++ auto.
               ++ destruct M; try congruence; inversion H4; simpl; congruence.
               ++ apply H12.
               ++ destruct H5; subst; destruct i3... all: simpl. apply c_refl. apply c_link.
           *** destruct i2, i3... destruct i2, i3... simpl.
               destruct (link_future_equiv_link_future _ _ _ (or_intror H13)) as [? [? [? ?]]].
               destruct i1...
               eapply (link_tree_cons_nl _ _ (down1_message (rename_message x swap01) 0)).
               ++ apply link_tree_cons_fl; try lia. auto.
               ++ destruct M; try congruence; inversion H4; simpl; congruence.
               ++ assert (j < i1) by lia. apply H11.
               ++ destruct H5; subst; destruct i1... all: simpl. apply c_refl. apply c_link.
           *** destruct i1, i2, i3, i4... destruct i1, i2, i3, i4... simpl.
               apply link_tree_cons_fl; try lia.
               apply link_tree_cons_fl; try lia.
               auto.
           *** apply link_tree_SSj_swap01 in H8.
               destruct (link_future_equiv_link_future _ _ _ (or_intror H12)) as [? [? [? ?]]].
               destruct i'...
               eapply (link_tree_cons_nl _ _ (down1_message (rename_message x swap01) 0)).
               ++ link_tree_econstructor.
               ++ destruct M; try congruence; inversion H4; simpl; congruence.
               ++ assert (j < i') by lia. apply H10.
               ++ destruct H5; subst; destruct i'... all: simpl. apply c_refl. apply c_link.
           *** apply link_tree_branch.
               ++ apply link_tree_down. apply link_tree_SSj_swap01; auto.
               ++ destruct (link_future_equiv_link_future _ _ _ (or_intror H12)) as [? [? [? ?]]].
                  destruct i'...
                  eapply (link_tree_cons_nl _ _ (rename_message x swap01)).
                  -- apply link_tree_SSj_swap01. apply link_tree_up; auto.
                  -- destruct M; try congruence; inversion H4; simpl; congruence.
                  -- assert (j < i') by lia. apply H11.
                  -- destruct H5; subst; destruct i'... all: simpl. apply c_refl. apply c_link.
           *** destruct i1, i2... destruct i1, i2... simpl.
               apply link_tree_cons_fl; try lia. apply link_tree_branch; auto.
               apply link_tree_SSj_swap01; auto.
           *** destruct i1, i2... destruct i1, i2... simpl.
               apply link_tree_branch. { apply link_tree_down; apply link_tree_SSj_swap01; auto. }
               apply link_tree_cons_fl; try lia; auto.
           *** apply link_tree_branch. { apply link_tree_down; apply link_tree_SSj_swap01; auto. }
               apply link_tree_branch. { apply link_tree_SSj_swap01; auto. }
               auto.
      * auto.
      * eapply (IHn n0); eauto. lia.
      * assert (link_tree j Q0). { eapply (IHn n1); eauto. lia. }
        eapply (IHn n2); eauto. lia.
      * inversion H0.
      * inversion H0; subst.
        ** apply (proj1 struct_cong_from_struct_cong_d) in H2. apply c_comm in H2.
           apply (proj1 struct_cong_from_struct_cong_d) in H3. apply c_comm in H3.
           pose proof (c_trans _ _ _ H2 H11). pose proof (c_trans _ _ _ H3 H12).
           link_tree_econstructor. Unshelve. all: eauto.
        ** apply (proj1 struct_cong_from_struct_cong_d) in H2. apply c_comm in H2.
           apply (proj1 struct_cong_from_struct_cong_d) in H3. apply c_comm in H3.
           pose proof (c_trans _ _ _ H3 H11).
           destruct (link_future_equiv_link_future _ _ _ (or_intror H2)) as [? [? [? ?]]].
           pose proof (future_equiv_future _ _ _ (or_intror H5)); subst.
           destruct H9; subst; link_tree_econstructor.
           Unshelve. all: eauto.
        ** apply (proj1 struct_cong_from_struct_cong_d) in H2. apply c_comm in H2.
           apply (proj1 struct_cong_from_struct_cong_d) in H3. apply c_comm in H3.
           pose proof (c_trans _ _ _ H2 H11).
           destruct (link_future_equiv_link_future _ _ _ (or_intror H3)) as [? [? [? ?]]].
           pose proof (future_equiv_future _ _ _ (or_intror H5)); subst.
           destruct H9; subst; link_tree_econstructor.
           Unshelve. all: eauto.
        ** apply (proj1 struct_cong_from_struct_cong_d) in H2. apply c_comm in H2.
           apply (proj1 struct_cong_from_struct_cong_d) in H3. apply c_comm in H3.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H2)) as [? [? [? ?]]].
           pose proof (future_equiv_future _ _ _ (or_intror H4)); subst.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H3)) as [? [? [? ?]]].
           pose proof (future_equiv_future _ _ _ (or_intror H8)); subst.
           destruct H5; destruct H11; subst; link_tree_econstructor.
        ** assert (n2 <= n) by lia.
           pose proof (IHn _ H4 (S j) _ _ H6 (or_introl H3)).
           apply (proj1 struct_cong_from_struct_cong_d) in H2. apply c_comm in H2.
           pose proof (c_trans _ _ _ H2 H10).
           link_tree_econstructor. Unshelve. eauto.
        ** assert (n1 <= n) by lia.
           pose proof (IHn _ H4 (S j) _ _ H6 (or_introl H2)).
           apply (proj1 struct_cong_from_struct_cong_d) in H3. apply c_comm in H3.
           pose proof (c_trans _ _ _ H3 H10).
           link_tree_econstructor. Unshelve. eauto.
        ** assert (n2 <= n) by lia.
           pose proof (IHn _ H4 _ _ _ H6 (or_introl H3)).
           apply (proj1 struct_cong_from_struct_cong_d) in H2.
           destruct (link_future_equiv_link_future _ _ _ (or_introl H2)) as [? [? [? ?]]].
           pose proof (future_equiv_future _ _ _ (or_intror H7)); subst.
           destruct H10; subst; link_tree_econstructor.
        ** assert (n1 <= n) by lia.
           pose proof (IHn _ H4 _ _ _ H6 (or_introl H2)).
           apply (proj1 struct_cong_from_struct_cong_d) in H3.
           destruct (link_future_equiv_link_future _ _ _ (or_introl H3)) as [? [? [? ?]]].
           pose proof (future_equiv_future _ _ _ (or_intror H7)); subst.
           destruct H10; subst; link_tree_econstructor.
        ** assert (n1 <= n) by lia. assert (n2 <= n) by lia.
           pose proof (IHn _ H4 _ _ _ H7 (or_introl H2)).
           pose proof (IHn _ H5 _ _ _ H8 (or_introl H3)).
           link_tree_econstructor.
      * inversion H0.
    - inversion H1; subst.
      * inversion H0.
      * inversion H0; subst; link_tree_econstructor.
        Unshelve. all: eauto.
      * inversion H0; subst.
        ** exfalso.
          destruct (link_future_equiv_link_future _ _ _ (or_intror H11)) as [? [? [? [? | ?]]]]; destruct P0; simpl in *; congruence.
        ** exfalso.
          destruct (link_future_equiv_link_future _ _ _ (or_intror H10)) as [? [? [? [? | ?]]]]; congruence.
        ** assert (link_tree (S j) (cut P0 Q0)).
          {
            destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [HM H']]].
            destruct i'...
            inversion H5; subst;
            try match goal with
            | [ H : (rename_process ?Q swap01) ≡ (link (future ?i) ?M1),
                Hj : S ?j < ?i
              |- link_tree (S ?j) (cut _ ?Q) ]
              => destruct (link_future_equiv_link_future _ _ _ (or_intror H)) as [x1 [? [HM1 H'']]];
                 eapply (link_tree_leaf_nn _ _ _ (rename_message (lift_message x 0 1) swap01) (rename_message x1 swap01));
                 [ destruct M; try congruence; inversion HM; simpl; congruence
                 | destruct M1; try congruence; inversion HM1; simpl; congruence
                 | assert (S j < S (S i')) as Hji by lia; apply Hji
                 | apply Hj
                 | replace P0 with (rename_process (up (down (rename_process P0 swap01))) swap01)
                    by (autorewrite with up_down_rename_rewrites; auto; apply nfv_01_swap; auto);
                    destruct H' as [H1' | H2'];
                    [ rewrite H1'; simpl; unfold relocate; simpl; apply c_refl
                    | rewrite H2'; simpl; unfold relocate; simpl; apply c_link
                    ]
                 | replace Q with (rename_process (rename_process Q swap01) swap01)
                    by (autorewrite with up_down_rename_rewrites; auto);
                   destruct i; try (exfalso; lia);
                   destruct i; try (exfalso; lia);
                   destruct H'' as [H1'' | H2''];
                   [ rewrite H1''; simpl; apply c_refl
                   | rewrite H2''; simpl; apply c_link
                   ]
                 ]
            | [ H : link (future ?i1) (future ?i2) = rename_process ?Q swap01,
                Hj : S ?j < ?i
              |- link_tree (S ?j) (cut _ ?Q) ]
              => replace Q with (rename_process (rename_process Q swap01) swap01)
                  by (autorewrite with up_down_rename_rewrites; auto);
                 rewrite <- H;
                 destruct i1, i2; try (exfalso; lia);
                 destruct i1, i2; try (exfalso; lia);
                 simpl;
                 eapply (link_tree_leaf_fn _ _ _ _ (rename_message (lift_message x 0 1) swap01)); try lia;
                 [ destruct M; try congruence; inversion HM; simpl; congruence
                 | assert (S j < S (S i')) as Hji by lia; apply Hji
                 | replace P0 with (rename_process (up (down (rename_process P0 swap01))) swap01)
                    by (autorewrite with up_down_rename_rewrites; auto; apply nfv_01_swap; auto);
                   destruct H' as [H1' | H2'];
                   [ rewrite H1'; simpl; unfold relocate; simpl; apply c_refl
                   | rewrite H2'; simpl; unfold relocate; simpl; apply c_link
                   ]
                 ]
            | [ H : link_tree (S (S ?j)) (rename_process ?Q swap01)
              |- link_tree (S ?j) (cut _ ?Q) ]
              => apply link_tree_SSj_swap01 in H;
                 autorewrite with up_down_rename_rewrites in H;
                 eapply (link_tree_cons_nl _ _ (rename_message (lift_message x 0 1) swap01));
                 [ auto
                 | destruct M; try congruence; inversion HM; simpl; congruence
                 | assert (S j < S (S i')) as Hji by lia; apply Hji
                 | replace P0 with (rename_process (up (down (rename_process P0 swap01))) swap01)
                    by (autorewrite with up_down_rename_rewrites; auto; apply nfv_01_swap; auto);
                   destruct H' as [H1' | H2'];
                   [ rewrite H1'; simpl; unfold relocate; simpl; apply c_refl
                   | rewrite H2'; simpl; unfold relocate; simpl; apply c_link
                   ]
                 ]
            end.
          }
          inversion H5; subst;
          try match goal with
          | [ H : (rename_process (up ?R) swap01) ≡ (link (future ?i) ?M)
            |- link_tree ?j (cut _ ?R) ]
            => destruct (link_future_equiv_link_future _ _ _ (or_intror H)) as [x [? [Hx HR]]];
               destruct i as [|i]; try (exfalso; lia);
               eapply (link_tree_cons_nr _ _ (down1_message (rename_message x swap01) 0));
               [ auto
               | destruct M; try congruence; inversion Hx; simpl; congruence
               | assert (j < i) as Hji by lia; apply Hji
               | destruct HR as [HR1 | HR2];
                 replace R with (down (rename_process (rename_process (up R) swap01) swap01))
                   by (autorewrite with up_down_rename_rewrites; reflexivity);
               [ rewrite HR1; destruct i; try (exfalso; lia); simpl; apply c_refl
               | rewrite HR2; destruct i; try (exfalso; lia); simpl; apply c_link
               ]
               ]
          | [ H : (link (future ?i) (future ?i')) = (rename_process (up ?R) swap01)
            |- link_tree ?j (cut _ ?R) ]
            => replace R with (down (rename_process (rename_process (up R) swap01) swap01))
                 by (autorewrite with up_down_rename_rewrites; reflexivity);
               rewrite <- H;
               destruct i, i'; try (exfalso; lia);
               destruct i, i'; try (exfalso; lia);
               simpl;
               apply link_tree_cons_fr; try lia; auto
          | [ H : link_tree (S (S ?j)) (rename_process (up ?R) swap01)
            |- link_tree ?j (cut _ ?R) ]
            => apply link_tree_SSj_swap01 in H; apply link_tree_up in H;
               autorewrite with up_down_rename_rewrites in H;
               eapply link_tree_down with (k := 0) in H;
               eapply link_tree_down with (k := 0) in H;
               replace (down1_process (down1_process (up (up R)) 0) 0) with (down (down (up (up R)))) in H by reflexivity;
               autorewrite with up_down_rename_rewrites in H;
               link_tree_econstructor
          end.
        ** exfalso.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [? [? [? [? | ?]]]]; congruence.
        ** assert (link_tree (S j) (cut P0 Q0)).
          {
            inversion H5; subst;
            try match goal with
            | [ H : (rename_process ?Q swap01) ≡ (link (future ?i) ?M1),
                Hj : S ?j < ?i
              |- link_tree (S ?j) (cut _ ?Q) ]
              => replace P0 with (rename_process (up (down (rename_process P0 swap01))) swap01)
                  by (autorewrite with up_down_rename_rewrites; auto; apply nfv_01_swap; auto);
                  rewrite <- H3;
                  destruct i1, i2; try (exfalso; lia); simpl; unfold relocate; simpl;
                  destruct (link_future_equiv_link_future _ _ _ (or_intror H)) as [x1 [? [HM1 H'']]];
                  eapply (link_tree_leaf_nf _ _ _ _ (rename_message x1 swap01)); try lia;
                  [ destruct M1; try congruence; inversion HM1; simpl; congruence
                  | apply Hj
                  | replace Q with (rename_process (rename_process Q swap01) swap01)
                      by (autorewrite with up_down_rename_rewrites; auto);
                    destruct i; try (exfalso; lia);
                    destruct i; try (exfalso; lia);
                    destruct H'' as [H1'' | H2''];
                    [ rewrite H1''; simpl; apply c_refl
                    | rewrite H2''; simpl; apply c_link
                    ]
                  ]
            | [ H : link (future ?i0) (future ?i3) = rename_process ?Q swap01
              |- link_tree (S ?j) (cut _ ?Q) ]
              => replace P0 with (rename_process (up (down (rename_process P0 swap01))) swap01)
                    by (autorewrite with up_down_rename_rewrites; auto; apply nfv_01_swap; auto);
                 rewrite <- H3;
                 replace Q with (rename_process (rename_process Q swap01) swap01)
                    by (autorewrite with up_down_rename_rewrites; auto);
                 rewrite <- H;
                 destruct i0, i3, i2, i1; try (exfalso; lia);
                 destruct i0, i3; try (exfalso; lia);
                 simpl; unfold relocate; simpl;
                 eapply link_tree_leaf_ff; try lia
            | [ H : link_tree (S (S j)) (rename_process Q0 swap01)
              |- link_tree (S ?j) (cut _ ?Q) ]
              => apply link_tree_SSj_swap01 in H;
                 autorewrite with up_down_rename_rewrites in H;
                 replace P0 with (rename_process (up (down (rename_process P0 swap01))) swap01)
                    by (autorewrite with up_down_rename_rewrites; auto; apply nfv_01_swap; auto);
                 rewrite <- H3;
                 destruct i1, i2; try (exfalso; lia); simpl; unfold relocate; simpl;
                 eapply link_tree_cons_fl; auto; try lia
            end.
          }
          inversion H5; subst;
          try match goal with
          | [ H : (rename_process (up ?R) swap01) ≡ (link (future ?i) ?M)
            |- link_tree ?j (cut _ ?R) ]
            => destruct (link_future_equiv_link_future _ _ _ (or_intror H)) as [x [? [Hx HR]]];
               destruct i as [|i]; try (exfalso; lia);
               eapply (link_tree_cons_nr _ _ (down1_message (rename_message x swap01) 0));
               [ auto
               | destruct M; try congruence; inversion Hx; simpl; congruence
               | assert (j < i) as Hji by lia; apply Hji
               | destruct HR as [HR1 | HR2];
                 replace R with (down (rename_process (rename_process (up R) swap01) swap01))
                   by (autorewrite with up_down_rename_rewrites; reflexivity);
               [ rewrite HR1; destruct i; try (exfalso; lia); simpl; apply c_refl
               | rewrite HR2; destruct i; try (exfalso; lia); simpl; apply c_link
               ]
               ]
          | [ H : (link (future ?i) (future ?i')) = (rename_process (up ?R) swap01)
            |- link_tree ?j (cut _ ?R) ]
            => replace R with (down (rename_process (rename_process (up R) swap01) swap01))
                 by (autorewrite with up_down_rename_rewrites; reflexivity);
               rewrite <- H;
               destruct i, i'; try (exfalso; lia);
               destruct i, i'; try (exfalso; lia);
               simpl;
               apply link_tree_cons_fr; try lia; auto
          | [ H : link_tree (S (S ?j)) (rename_process (up ?R) swap01)
            |- link_tree ?j (cut _ ?R) ]
            => apply link_tree_SSj_swap01 in H; apply link_tree_up in H;
               autorewrite with up_down_rename_rewrites in H;
               eapply link_tree_down with (k := 0) in H;
               eapply link_tree_down with (k := 0) in H;
               replace (down1_process (down1_process (up (up R)) 0) 0) with (down (down (up (up R)))) in H by reflexivity;
               autorewrite with up_down_rename_rewrites in H;
               link_tree_econstructor
          end.
        ** assert (link_tree (S j) (cut P0 Q0)).
          {
            assert (link_tree (S (S j)) P0).
            {
              apply link_tree_up in H6. apply link_tree_SSj_swap01 in H6;
              autorewrite with up_down_rename_rewrites in H6; auto.
              apply nfv_01_swap; auto.
            }
            inversion H7; subst;
            try match goal with
            | [ H : (rename_process ?Q swap01) ≡ (link (future ?i) ?M1),
                Hj : S ?j < ?i
              |- link_tree (S ?j) (cut _ ?Q) ]
              => destruct (link_future_equiv_link_future _ _ _ (or_intror H)) as [x1 [? [HM1 H'']]];
                 eapply (link_tree_cons_nr _ _ (rename_message x1 swap01)); try lia;
                 [ auto
                 | destruct M1; try congruence; inversion HM1; simpl; congruence
                 | apply Hj
                 | replace Q with (rename_process (rename_process Q swap01) swap01)
                     by (autorewrite with up_down_rename_rewrites; auto);
                   destruct i; try (exfalso; lia);
                   destruct i; try (exfalso; lia);
                   destruct H'' as [H1'' | H2''];
                   [ rewrite H1''; simpl; apply c_refl
                   | rewrite H2''; simpl; apply c_link
                   ]
                 ]
            | [ H : link (future ?i1) (future ?i2) = rename_process ?Q swap01
              |- link_tree (S ?j) (cut _ ?Q) ]
              => replace Q with (rename_process (rename_process Q swap01) swap01)
                     by (autorewrite with up_down_rename_rewrites; auto);
                 rewrite <- H;
                 destruct i1, i2; try (exfalso; lia);
                 destruct i1, i2; try (exfalso; lia);
                 simpl;
                 apply link_tree_cons_fr; try lia; auto
            | [ H : link_tree (S (S j)) (rename_process Q0 swap01)
              |- link_tree (S ?j) (cut _ ?Q) ]
              => apply link_tree_SSj_swap01 in H;
                 autorewrite with up_down_rename_rewrites in H;
                 apply link_tree_branch; auto
            end.
          }
          inversion H7; subst;
          try match goal with
          | [ H : (rename_process (up ?R) swap01) ≡ (link (future ?i) ?M)
            |- link_tree ?j (cut _ ?R) ]
            => destruct (link_future_equiv_link_future _ _ _ (or_intror H)) as [x [? [Hx HR]]];
               destruct i as [|i]; try (exfalso; lia);
               eapply (link_tree_cons_nr _ _ (down1_message (rename_message x swap01) 0));
               [ auto
               | destruct M; try congruence; inversion Hx; simpl; congruence
               | assert (j < i) as Hji by lia; apply Hji
               | destruct HR as [HR1 | HR2];
                 replace R with (down (rename_process (rename_process (up R) swap01) swap01))
                   by (autorewrite with up_down_rename_rewrites; reflexivity);
               [ rewrite HR1; destruct i; try (exfalso; lia); simpl; apply c_refl
               | rewrite HR2; destruct i; try (exfalso; lia); simpl; apply c_link
               ]
               ]
          | [ H : (link (future ?i) (future ?i')) = (rename_process (up ?R) swap01)
            |- link_tree ?j (cut _ ?R) ]
            => replace R with (down (rename_process (rename_process (up R) swap01) swap01))
                 by (autorewrite with up_down_rename_rewrites; reflexivity);
               rewrite <- H;
               destruct i, i'; try (exfalso; lia);
               destruct i, i'; try (exfalso; lia);
               simpl;
               apply link_tree_cons_fr; try lia; auto
          | [ H : link_tree (S (S ?j)) (rename_process (up ?R) swap01)
            |- link_tree ?j (cut _ ?R) ]
            => apply link_tree_SSj_swap01 in H; apply link_tree_up in H;
               autorewrite with up_down_rename_rewrites in H;
               eapply link_tree_down with (k := 0) in H;
               eapply link_tree_down with (k := 0) in H;
               replace (down1_process (down1_process (up (up R)) 0) 0) with (down (down (up (up R)))) in H by reflexivity;
               autorewrite with up_down_rename_rewrites in H;
               link_tree_econstructor
          end.
      * auto.
      * eapply (IHn n0); eauto. lia.
      * assert (link_tree j Q0). { eapply (IHn n2); eauto. lia. }
        eapply (IHn n1); eauto. lia.
      * inversion H0.
      * inversion H0; subst.
        ** apply (proj1 struct_cong_from_struct_cong_d) in H2.
           apply (proj1 struct_cong_from_struct_cong_d) in H3.
           pose proof (c_trans _ _ _ H2 H11). pose proof (c_trans _ _ _ H3 H12).
           link_tree_econstructor. Unshelve. all: eauto.
        ** apply (proj1 struct_cong_from_struct_cong_d) in H2.
           apply (proj1 struct_cong_from_struct_cong_d) in H3.
           pose proof (c_trans _ _ _ H3 H11).
           destruct (link_future_equiv_link_future _ _ _ (or_intror H2)) as [? [? [? ?]]].
           pose proof (future_equiv_future _ _ _ (or_intror H5)); subst.
           destruct H9; subst; link_tree_econstructor.
           Unshelve. all: eauto.
        ** apply (proj1 struct_cong_from_struct_cong_d) in H2.
           apply (proj1 struct_cong_from_struct_cong_d) in H3.
           pose proof (c_trans _ _ _ H2 H11).
           destruct (link_future_equiv_link_future _ _ _ (or_intror H3)) as [? [? [? ?]]].
           pose proof (future_equiv_future _ _ _ (or_intror H5)); subst.
           destruct H9; subst; link_tree_econstructor.
           Unshelve. all: eauto.
        ** apply (proj1 struct_cong_from_struct_cong_d) in H2.
           apply (proj1 struct_cong_from_struct_cong_d) in H3.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H2)) as [? [? [? ?]]].
           pose proof (future_equiv_future _ _ _ (or_intror H4)); subst.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H3)) as [? [? [? ?]]].
           pose proof (future_equiv_future _ _ _ (or_intror H8)); subst.
           destruct H5; destruct H11; subst; link_tree_econstructor.
        ** assert (n2 <= n) by lia.
           pose proof (IHn _ H4 (S j) _ _ H6 (or_intror H3)).
           apply (proj1 struct_cong_from_struct_cong_d) in H2.
           pose proof (c_trans _ _ _ H2 H10).
           link_tree_econstructor. Unshelve. eauto.
        ** assert (n1 <= n) by lia.
           pose proof (IHn _ H4 (S j) _ _ H6 (or_intror H2)).
           apply (proj1 struct_cong_from_struct_cong_d) in H3.
           pose proof (c_trans _ _ _ H3 H10).
           link_tree_econstructor. Unshelve. eauto.
        ** assert (n2 <= n) by lia.
           pose proof (IHn _ H4 _ _ _ H6 (or_intror H3)).
           apply (proj1 struct_cong_from_struct_cong_d) in H2.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H2)) as [? [? [? ?]]].
           pose proof (future_equiv_future _ _ _ (or_intror H7)); subst.
           destruct H10; subst; link_tree_econstructor.
        ** assert (n1 <= n) by lia.
           pose proof (IHn _ H4 _ _ _ H6 (or_intror H2)).
           apply (proj1 struct_cong_from_struct_cong_d) in H3.
           destruct (link_future_equiv_link_future _ _ _ (or_intror H3)) as [? [? [? ?]]].
           pose proof (future_equiv_future _ _ _ (or_intror H7)); subst.
           destruct H10; subst; link_tree_econstructor.
        ** assert (n1 <= n) by lia. assert (n2 <= n) by lia.
           pose proof (IHn _ H4 _ _ _ H7 (or_intror H2)).
           pose proof (IHn _ H5 _ _ _ H8 (or_intror H3)).
           link_tree_econstructor.
      * inversion H0.
Qed.

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
  forall Γ P, Γ ⊢ P :# -> is_final P <-> irreducible P.
Proof.
  intros; split.
  + intros. apply final_wt_implies_final in H0. eapply final_implies_irreducible; eauto.
  + eapply irreducible_implies_final; eauto.
Qed.
