From FD Require Import Syntax.
From FD Require Import Types.
From FD Require Import Renaming.
From FD Require Import StructCong.
From FD Require Import Reduction.
From FD Require Import Contexts.
From FD Require Import Typing.
From FD Require Import FreeVars.

From Stdlib Require List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
Import List.ListNotations.

(******************************************************************************)
(* Canonical Cut Forms                                                        *)
(******************************************************************************)
Definition no_root_cut (P : process) :=
  forall Q R, P <> (cut Q R).

Inductive cut_list : process -> Prop :=
  | cut_list_nil  : forall L R,
                      no_root_cut L ->
                      no_root_cut R ->
                      cut_list (cut L R)
  | cut_list_cons : forall L P,
                      no_root_cut L ->
                      cut_list P ->
                      cut_list (cut L P).

(******************************************************************************)
(* Final Processes (for the untyped case)                                     *)
(******************************************************************************)
Definition no_future (M : message) :=
  forall i, M <> future i.

Inductive link_list : list nat -> process -> Prop :=
  | link_cut_nn : forall i1 i2 M1 M2 P1 P2,
                    no_future M1 -> no_future M2 ->
                    P1 ≡ (link (future i1) M1) ->
                    P2 ≡ (link (future i2) M2) ->
                    link_list [i1; i2] (cut P1 P2)
  | link_cut_nf : forall i1 i2 i3 M P,
                    no_future M ->
                    P ≡ (link (future i3) M) ->
                    link_list [i1; i2; i3] (cut (link (future i1) (future i2)) P)
  | link_cut_fn : forall i1 i2 i3 M P,
                    no_future M ->
                    P ≡ (link (future i1) M) ->
                    link_list [i1; i2; i3] (cut P (link (future i2) (future i3)))
  | link_cut_ff : forall i1 i2 i3 i4,
                    link_list [i1; i2; i3; i4] (cut (link (future i1) (future i2))
                                                    (link (future i3) (future i4)))
  | link_cons_n   : forall i M xs P L,
                      link_list (List.map S xs) P ->
                      no_future M ->
                      L ≡ (link (future i) M) ->
                      link_list (i :: xs) (cut L P)
  | link_cons_f   : forall i1 i2 xs P,
                      link_list (List.map S xs) P ->
                      link_list (i1 :: i2 :: xs) (cut (link (future i1) (future i2)) P).

Inductive final : process -> Prop :=
  | final_stop : final stop
  | final_future_l : forall i M, final (link (future i) M)
  | final_future_r : forall i M, final (link M (future i))
  | final_list : forall xs P P',
                  ~ (List.In 0 xs) ->
                  link_list xs P' ->
                  P ≡ P' ->
                  final P.

(******************************************************************************)
(* Final Processes (for typed processes)                                      *)
(******************************************************************************)
Inductive link_list_wt : list nat -> process -> Prop :=
  | link_list_nil : forall i1 i2 M1 M2 P1 P2,
                    no_future M1 -> no_future M2 ->
                    P1 ≡ (link (future i1) M1) ->
                    P2 ≡ (link (future i2) M2) ->
                    link_list_wt [i1; i2] (cut P1 P2)
  | link_list_cons : forall i M xs P L,
                      link_list_wt (List.map S xs) P ->
                      no_future M ->
                      L ≡ (link (future i) M) ->
                      link_list_wt (i :: xs) (cut L P).

Inductive is_final : process -> Prop :=
  | final_stop_wt : is_final stop
  | final_future_l_wt : forall i M, is_final (link (future i) M)
  | final_future_r_wt : forall i M, is_final (link M (future i))
  | final_list_wt : forall xs P P',
                      ~ (List.In 0 xs) ->
                      link_list_wt xs P' ->
                      P ≡ P' ->
                      is_final P.

Lemma well_typed_link_list_no_0_is_link_list_wt :
  forall Γ P xs, Γ ⊢ P :# -> link_list xs P -> ~ (List.In 0 xs) -> link_list_wt xs P.
Proof.
  intros. generalize dependent Γ.
  induction H0; intros.
  + eapply (link_list_nil i1 i2 M1 M2); eauto.
  + simpl in H1. assert (i1 <> 0) by lia. assert (i2 <> 0) by lia.
    inversion H2.
    assert (0 ∈ (link (future i1) (future i2))).
    {
      assert (lookup 0 (A .: Γ1) = Some A) by auto.
      eapply (proj1 formula_property) in H11; eauto.
    }
    inversion H11; subst; inversion H14; congruence.
  + simpl in H1. assert (i2 <> 0) by lia. assert (i3 <> 0) by lia.
    inversion H2.
    assert (0 ∈ (link (future i2) (future i3))).
    {
      assert (lookup 0 (dual A .: Γ2) = Some (dual A)) by auto.
      eapply (proj1 formula_property) in H11; eauto.
    }
    inversion H11; subst; inversion H14; congruence.
  + simpl in H1. assert (i1 <> 0) by lia. assert (i2 <> 0) by lia.
    inversion H.
    assert (0 ∈ (link (future i1) (future i2))).
    {
      assert (lookup 0 (A .: Γ1) = Some A) by auto.
      eapply (proj1 formula_property) in H9; eauto.
    }
    inversion H9; subst; inversion H12; congruence.
  + assert (~ List.In 0 xs).
    {
      destruct (PeanoNat.Nat.eq_dec i 0).
      + subst. simpl in H1. intro. apply H1. left. auto.
      + simpl in H1. intro. apply H1; auto.
    }
    assert (~ List.In 0 (ListDef.map S xs)).
    {
      intro. clear - H5. induction xs; auto. apply IHxs.
      simpl in H5. destruct H5; try congruence.
    }
    inversion H3.
    eapply (link_list_cons i); eauto.
  + simpl in H1. assert (i1 <> 0) by lia. assert (i2 <> 0) by lia.
    inversion H.
    assert (0 ∈ (link (future i1) (future i2))).
    {
      assert (lookup 0 (A .: Γ1) = Some A) by auto.
      eapply (proj1 formula_property) in H10; eauto.
    }
    inversion H10; subst; inversion H13; congruence.
Qed.

Lemma well_typed_final_process_is_final_wt :
  forall Γ P, Γ ⊢ P :# -> final P -> is_final P.
Proof.
  intros.
  induction H0; try (econstructor; eauto).
  apply ((proj1 struct_cong_preserves_typing) _ _ H2) in H. clear H2.
  eapply well_typed_link_list_no_0_is_link_list_wt; eauto.
Qed.

Lemma link_list_wt_implies_link_list :
  forall P xs, link_list_wt xs P -> link_list xs P.
Proof.
  intros. induction H.
  + eapply (link_cut_nn i1 i2 M1 M2); eauto.
  + econstructor; eauto.
Qed.

Lemma final_wt_implies_final :
  forall P, is_final P -> final P.
Proof.
  intros. induction H; try econstructor; eauto.
  apply link_list_wt_implies_link_list; auto.
Qed.

(******************************************************************************)
(* Canonical Cut Form                                                         *)
(******************************************************************************)
Lemma renaming_preserves_cut_listness :
  forall P r,
    cut_list P -> cut_list (rename_process P r).
Proof.
  intros.
  generalize dependent r.
  induction H; intros; simpl.
  + apply cut_list_nil.
    - destruct L; simpl; congruence.
    - destruct R; simpl; congruence.
  + apply cut_list_cons.
    - destruct L; simpl; congruence.
    - apply IHcut_list.
Qed.

Lemma upshifting_preserves_cut_listness :
  forall P k n,
    cut_list P -> cut_list (lift_process P k n).
Proof.
  intros.
  generalize dependent k.
  generalize dependent n.
  induction H; intros; simpl.
  + apply cut_list_nil; try destruct L; try destruct R; simpl; congruence.
  + apply cut_list_cons.
    - destruct L; simpl; congruence.
    - apply IHcut_list.
Qed.

Lemma downshift_preserves_cut_listness :
  forall P n,
    cut_list P -> cut_list (down1_process P n).
Proof.
  intros.
  generalize dependent n.
  induction H; intros; simpl.
  + apply cut_list_nil; try destruct L; try destruct R; simpl; congruence.
  + apply cut_list_cons.
    - destruct L; simpl; congruence.
    - apply IHcut_list.
Qed.

Lemma cut_lists_flatten_in_cut' :
  forall n Γ P Q,
  forall k,
    k <= n ->
    depth P = k ->
    Γ ⊢ (cut P Q) :# ->
    cut_list P ->
    cut_list Q ->
    exists R, (cut P Q) ≡ R /\ cut_list R.
Proof.
  induction n; intros.
  + destruct P; exfalso.
    - inversion H2.
    - simpl in H0. rewrite <- H0 in H. inversion H.
    - simpl in H0. rewrite <- H0 in H. inversion H.
    - inversion H2.
  + destruct P.
    - inversion H2.
    - inversion H2; subst.
      {
        (* decide whether P1 or P2 contains 1 which determines how to reassosciate the cut *)
        inversion H1; subst. inversion H9; subst. inversion H8; subst.
        inversion H11; subst.
        + (* 1 ∈ P1 *)
          exists (cut (down (rename_process P2 swap01))
                  (cut (rename_process P1 swap01)
                       (rename_process (up Q) swap01))).
          split.
          * eapply c_trans.
            ** eapply c_cong_cut. eapply c_cut_comm. eapply c_refl.
            ** eapply c_cut_assoc; auto.
               apply ((proj1 ctx_none_not_free) _ _ 1) in H13; auto.
          * eapply cut_list_cons.
            ** destruct P2; simpl; try congruence.
            ** eapply cut_list_cons.
               *** destruct P1; simpl; try congruence.
               *** apply renaming_preserves_cut_listness.
                   apply upshifting_preserves_cut_listness; auto.
        + (* 1 ∈ P2 *)
          exists (cut (down (rename_process P1 swap01))
                  (cut (rename_process P2 swap01)
                       (rename_process (up Q) swap01))).
          split.
          * eapply c_cut_assoc; auto.
            apply ((proj1 ctx_none_not_free) _ _ 1) in H12; auto.
          * eapply cut_list_cons.
            ** destruct P1; simpl; try congruence.
            ** eapply cut_list_cons.
               *** destruct P2; simpl; try congruence.
               *** apply renaming_preserves_cut_listness.
                   apply upshifting_preserves_cut_listness; auto.
      }
      {
        inversion H1; subst. inversion H9; subst. inversion H8; subst.
        inversion H11; subst.
        + assert (
            (cut (cut P1 P2) Q) ≡
            (cut (down (rename_process P2 swap01))
                  (cut (rename_process P1 swap01)
                       (rename_process (up Q) swap01)))
          ).
          {
            eapply c_trans.
            + eapply c_cong_cut. apply c_cut_comm. apply c_refl.
            + eapply c_cut_assoc; eauto.
              apply ((proj1 ctx_none_not_free) _ _ 1) in H13; auto.
          }

          assert ( cut_list (down (rename_process P2 swap01)) ).
          { apply downshift_preserves_cut_listness; apply renaming_preserves_cut_listness; auto. }
          assert ( cut_list (cut (rename_process P1 swap01) (rename_process (up Q) swap01)) ).
          {
            apply cut_list_cons.
            + destruct P1; simpl; congruence.
            + apply renaming_preserves_cut_listness;
              apply upshifting_preserves_cut_listness;
              auto.
          }
          assert ( depth (down (rename_process P2 swap01)) <= n ).
          {
            unfold down.
            rewrite <- (proj1 down_shift_preserves_depth).
            rewrite <- (proj1 renaming_preserves_depth).
            simpl in H; lia.
          }
          apply ((proj1 struct_cong_preserves_typing) _ _ H0) in H1.

          destruct (IHn _ _ _ _ H15 eq_refl H1 H4 H14) as [P' [? ?]].
          exists P'; split; auto.
          eapply c_trans; eauto.
        + assert (
            (cut (cut P1 P2) Q) ≡
            (cut (down (rename_process P1 swap01))
                  (cut (rename_process P2 swap01)
                       (rename_process (up Q) swap01)))
          ).
          {
            eapply c_cut_assoc; auto.
            apply ((proj1 ctx_none_not_free) _ _ 1) in H12; auto.
          }

          assert ( cut_list (rename_process P2 swap01) ).
          { apply renaming_preserves_cut_listness; auto. }
          assert ( cut_list (rename_process (up Q) swap01) ).
          { apply renaming_preserves_cut_listness; apply upshifting_preserves_cut_listness; auto. }

          simpl in H.
          assert ( depth P2 <= n ) by lia.
          assert ( depth (rename_process P2 swap01) <= n ).
          { rewrite <- ((proj1 renaming_preserves_depth) _ swap01); auto. }

          assert ( exists Γ', Γ' ⊢ cut (rename_process P2 swap01) (rename_process (up Q) swap01) :# ).
          {
            apply ((proj1 struct_cong_preserves_typing) _ _ H0) in H1.
            inversion H1; subst.
            exists (dual A1 .: Γ4); auto.
          }
          destruct H18 as [Γ' ?].

          destruct (IHn _ _ _ _ H17 eq_refl H18 H4 H14) as [P' [? ?]].

          exists (cut (down (rename_process P1 swap01)) P').
          split.
          - eapply c_trans; eauto.
            eapply c_trans.
            * eapply c_cut_comm.
            * eapply c_trans.
              ** eapply c_cong_cut; eauto. apply c_refl.
              ** eapply c_cut_comm.
          - eapply cut_list_cons; auto.
            destruct P1; simpl; congruence.
      }
    - exists (cut (seq P s) Q); split.
      * apply c_refl.
      * eapply cut_list_cons; auto. congruence.
    - inversion H2.
Qed.

Lemma cut_lists_flatten_in_cut :
  forall Γ P Q,
    Γ ⊢ (cut P Q) :# -> cut_list P -> cut_list Q ->
    exists R, (cut P Q) ≡ R /\ cut_list R.
Proof.
  intros.
  apply (cut_lists_flatten_in_cut'
          (depth P) _ _ _ (depth P) (Nat.le_refl (depth P)) eq_refl H H0 H1).
Qed.

Lemma canonical_cut_form :
  forall Γ L R, Γ ⊢ (cut L R) :# -> exists P', (cut L R) ≡ P' /\ cut_list P'.
Proof.
  intros.
  remember (cut L R).
  generalize dependent R.
  generalize dependent L.
  induction H; intros; try discriminate.
  destruct P; destruct Q;
  (* neither L nor R can be 'stop' if the cut is well-typed *)
  try ( match goal with [ H : (?A .: ?Γ) ⊢ stop :# |- _ ] => inversion H; ctx_eq_contra end );
  (* if both L and R are no cuts, then argue by reflexivity *)
  try now (
    match goal with
    | [ Heq : cut ?X ?Y = cut L R |- _ ] =>
      exists (cut X Y); split; try apply c_refl; try econstructor; try congruence
    end
  ).
  + specialize IHTypingP2 with Q1 Q2.
    destruct (IHTypingP2 eq_refl) as [P'' [? ?]].
    exists (cut (link m m0) P''); split.
    - eapply c_trans.
      * eapply c_cut_comm.
      * eapply c_trans.
        ** eapply c_cong_cut.
           *** eassumption.
           *** apply c_refl.
        ** eapply c_cut_comm.
    - eapply cut_list_cons; eauto. congruence.
  + specialize IHTypingP1 with P1 P2.
    destruct (IHTypingP1 eq_refl) as [P'' [? ?]].
    exists (cut (link m m0) P''); split.
    - eapply c_trans.
      * eapply c_cong_cut; eauto. eapply c_refl.
      * eapply c_cut_comm.
    - eapply cut_list_cons; eauto. congruence.
  + (* both operands of the cut are themselves cut lists and may be flattened into one *)
    specialize IHTypingP1 with P1 P2. destruct (IHTypingP1 eq_refl) as [P'' [? ?]].
    specialize IHTypingP2 with Q1 Q2. destruct (IHTypingP2 eq_refl) as [Q'' [? ?]].
    assert ( Γ ⊢ cut P'' Q'' :# ).
    {
      econstructor; eauto.
      + apply ((proj1 struct_cong_preserves_typing) _ _ H2 _); eauto.
      + apply ((proj1 struct_cong_preserves_typing) _ _ H4 _); eauto.
    }
    destruct (cut_lists_flatten_in_cut _ _ _ H6 H3 H5) as [R' [? ?]].
    exists R'; split; auto.
    eapply c_trans.
    - eapply c_cong_cut; eauto.
    - eauto.
  + specialize IHTypingP1 with P1 P2.
    destruct (IHTypingP1 eq_refl) as [P'' [? ?]].
    exists (cut (seq Q s) P''); split.
    - eapply c_trans.
      * eapply c_cong_cut; eauto. eapply c_refl.
      * eapply c_cut_comm.
    - eapply cut_list_cons; eauto. congruence.
  + specialize IHTypingP2 with Q1 Q2.
    destruct (IHTypingP2 eq_refl) as [P'' [? ?]].
    exists (cut (seq P s) P''); split.
    - eapply c_trans.
      * eapply c_cut_comm.
      * eapply c_trans.
        ** eapply c_cong_cut.
           *** eassumption.
           *** apply c_refl.
        ** eapply c_cut_comm.
    - eapply cut_list_cons; eauto. congruence.
Qed.

(******************************************************************************)
(* Properties about link processes                                            *)
(******************************************************************************)
Lemma link_reduces_or_contains_future :
  forall Γ M1 M2, Γ ⊢ (link M1 M2) :# ->
    (exists P', (link M1 M2) ⊳ P') \/
    (exists i, M1 = future i \/ M2 = future i).
Proof.
  intros.
  destruct M1; destruct M2; inversion H; subst.
  + right. exists n. left; reflexivity.
  + right. exists n. left; reflexivity.
  + right. exists n. right; reflexivity.
  + left.
    inversion H4; inversion H5; subst.
    inversion H3; inversion H9; subst;
    simpl in *; try discriminate.
    (* well-typed logical redex reduce according to their corresponding beta rule *)
    * exists (cut Q Q1); econstructor.
    * exists (cut Q Q2); econstructor.
    * exists (cut Q Q1).
      eapply r_struct with (P' := link (prefix (choose_left Q)) (prefix (offer_choice Q1 Q2))).
      ** eapply c_link.
      ** econstructor.
      ** apply c_refl.
    * exists (cut Q Q2).
      eapply r_struct with (P' := link (prefix (choose_right Q)) (prefix (offer_choice Q1 Q2))).
      ** eapply c_link.
      ** econstructor.
      ** apply c_refl.
    * exists (cut (cut Q0 (rename_process (up Q) swap01)) R); econstructor; eauto.
    * exists (cut (cut Q (rename_process (up Q0) swap01)) R).
      eapply r_struct with (P' := link (prefix (send Q0 R)) (prefix (receive Q))).
      ** eapply c_link.
      ** econstructor. reflexivity.
      ** apply c_refl.
    * exists Q; econstructor.
    * exists Q. eapply r_struct with (P' := link (prefix close) (prefix (wait Q))).
      ** eapply c_link.
      ** econstructor.
      ** apply c_refl.
Qed.

Corollary link_final_or_reduces :
  forall Γ M1 M2, Γ ⊢ (link M1 M2) :# ->
    final (link M1 M2) \/ (exists P', (link M1 M2) ⊳ P').
Proof.
  intros. destruct (link_reduces_or_contains_future _ _ _ H).
  + right; auto.
  + left. destruct H0 as [i [? | ?]]; subst; econstructor.
Qed.

(******************************************************************************)
(* Relation between Cut List and Link List                                    *)
(******************************************************************************)
Lemma link_list_with_0_at_0_reduces :
  forall P xs,
    link_list (0 :: xs) P -> exists Q, P ⊳ Q.
Proof.
  intros P xs H. inversion H.
  + eexists; eapply r_struct; [ eapply c_cong_cut; eauto | econstructor | apply c_refl ].
  + eexists; econstructor.
  + eexists; eapply r_struct; [ eapply c_cong_cut; [eauto | apply c_refl] | econstructor | apply c_refl ].
  + eexists; econstructor.
  + eexists; eapply r_struct.
    - eapply c_cong_cut; [eauto | apply c_refl].
    - econstructor.
    - apply c_refl.
  + eexists; econstructor.
Qed.

Local Hint Rewrite
  swap_swap_id
  down_after_up_process_id
  up_after_down_process_id
    : up_down_rename_rewrites.

Lemma link_list_with_0_at_1_reduces :
  forall Γ P xs n0,
    Γ ⊢ P :# -> link_list (n0 :: 0 :: xs) P -> exists Q, P ⊳ Q.
Proof.
  intros. inversion H0; subst.
  try
  match goal with
  | [ H : ?P ≡ (link (future 0) ?M) |- _ ]
      => destruct (link_future_equiv_link_future _ _ _ (or_intror H)) as [? [? [? [? | ?]]]]; subst
  end.
  + eexists; eapply r_struct; [ apply c_cut_comm | econstructor | apply c_refl ].
  + eexists; eapply r_struct; [ eapply c_trans; [ eapply c_cut_comm | apply c_cong_cut; [ apply c_link | apply c_refl ] ] | econstructor | apply c_refl ].
  + eexists; eapply r_struct; [ eapply c_cong_cut; [ apply c_link | apply c_refl ] | econstructor | apply c_refl ].
  + eexists; eapply r_struct; [ eapply c_cut_comm | econstructor | apply c_refl ].
  + eexists; eapply r_struct; [ eapply c_cong_cut; [ apply c_link | apply c_refl ] | econstructor | apply c_refl ].
  + simpl in H3; inversion H3; subst; try
    match goal with
    | [ H : ?P ≡ (link (future 1) ?M) |- _ ]
      => destruct (link_future_equiv_link_future _ _ _ (or_intror H)) as [? [? [? [? | ?]]]]; subst
    end;
    try match goal with
      | [ H   : link_list _ (cut ?L ((cut (link (future 1) ?M)) ?P)),
        Hwt : _ ⊢ (cut ?L ((cut (link (future 1) ?M)) ?P)) :#
        |- _ ]
        => eexists; eapply r_struct;
           [
             eapply c_comm; eapply (c_cut_assoc
              (rename_process (up L) swap01)
              (rename_process (link (future 1) M) swap01)
              (down (rename_process P swap01))
              ); autorewrite with up_down_rename_rewrites; auto;
              [ apply nfv_10_swap; apply nfv_lift_n; lia
              | apply nfv_01_swap; intro Hfv; inversion Hwt; subst;
                match goal with
                | [ Hwt1 : _ ⊢ cut (link (future 1) ?M) ?P :# |- _ ]
                  => inversion Hwt1; subst;
                     match goal with
                     | [ HwtM : (_ .: ?Γ1) ⊢ link (future 1) M :#,
                         HwtP : (_ .: ?Γ2) ⊢ P :#,
                         Hsplit : _ ≜ ?Γ1 ∘ ?Γ2
                         |- _ ]
                        => inversion Hsplit; subst;
                           assert (1 ∈ (link (future 1) M)) as Hfv1link by repeat econstructor;
                           destruct ((proj1 free_vars_decidable) P 1); auto;
                           apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in HwtM;
                           match goal with
                           | [ H : 1 ∈ P |- _ ] =>
                              apply ((proj1 free_var_in_ctx) _ _ H) in HwtP
                           end;
                           destruct HwtM, HwtP; simpl in *; subst;
                           match goal with
                           | [ Hsplitentry : split_entry _ _ _ |- _ ] => inversion Hsplitentry
                           end
                     end
                end
              ]
           | eapply r_cong_cut; eapply r_struct;
            [ apply c_cut_comm | simpl; econstructor | eapply c_refl ]
           | eapply c_refl
           ]
      | [ H   : link_list _ (cut ?L ((cut (link ?M (future 1))) ?P)),
          Hwt : _ ⊢ (cut ?L ((cut (link ?M (future 1))) ?P)) :#
          |- _ ]
        => eexists ; eapply r_struct;
            [
              eapply c_comm; eapply (c_cut_assoc
                (rename_process (up L) swap01)
                (rename_process (link M (future 1)) swap01)
                (down (rename_process P swap01))
              ); autorewrite with up_down_rename_rewrites; auto;
              [ apply nfv_10_swap; apply nfv_lift_n; lia
              | apply nfv_01_swap; intro Hfv; inversion Hwt; subst;
                match goal with
                | [ Hwt1 : _ ⊢ cut (link ?M (future 1)) ?P :# |- _ ]
                  => inversion Hwt1; subst;
                     match goal with
                     | [ HwtM : (_ .: ?Γ1) ⊢ link M (future 1) :#,
                         HwtP : (_ .: ?Γ2) ⊢ P :#,
                         Hsplit : _ ≜ ?Γ1 ∘ ?Γ2
                         |- _ ]
                        => inversion Hsplit; subst;
                           assert (1 ∈ (link M (future 1))) as Hfv1link by repeat econstructor;
                           destruct ((proj1 free_vars_decidable) P 1); auto;
                           apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in HwtM;
                           match goal with
                           | [ H : 1 ∈ P |- _ ] =>
                              apply ((proj1 free_var_in_ctx) _ _ H) in HwtP
                           end;
                           destruct HwtM, HwtP; simpl in *; subst;
                           match goal with
                           | [ Hsplitentry : split_entry _ _ _ |- _ ] => inversion Hsplitentry
                           end
                     end
                end
              ]
            | simpl; eapply r_cong_cut; eapply r_struct;
              [eapply c_trans; [eapply c_cut_comm | eapply c_cong_cut; [eapply c_link | eapply c_refl]]
              | econstructor
              | eapply c_refl
              ]
            | apply c_refl
            ]
      end.
  + eexists. eapply r_struct; [eapply c_cong_cut; [eapply c_link | eapply c_refl] | econstructor | eapply c_refl].
Qed.

Lemma link_list_rename :
  forall P xs r,
    (forall x, List.In x xs -> x > 0) ->
    bijective r -> link_list xs P -> link_list (List.map S (List.map r (List.map Nat.pred xs))) (rename_process P r).
Proof.
  intros.
  generalize dependent r.
  induction H1; intros.
  + destruct (link_future_equiv_link_future _ _  _ (or_intror H2)) as [? [? [? ?]]].
    destruct (link_future_equiv_link_future _ _  _ (or_intror H3)) as [? [? [? ?]]].
    destruct H6, H8; subst; destruct M1, M2; try congruence;
    inversion H5; inversion H7; subst;
    destruct i1, i2; try (specialize H with 0; simpl in H; exfalso; lia); simpl;
    match goal with
    | [ |- link_list [?n1; ?n2] (cut (link (future ?n1) (prefix ?s1))
                                       (link (future ?n2) (prefix ?s2))) ]
        => apply link_cut_nn with (prefix s1) (prefix s2)
    | [ |- link_list [?n1; ?n2] (cut (link (future ?n1) (prefix ?s1))
                                       (link (prefix ?s2) (future ?n2))) ]
        => apply link_cut_nn with (prefix s1) (prefix s2)
    | [ |- link_list [?n1; ?n2] (cut (link (prefix ?s1) (future ?n1))
                                       (link (future ?n2) (prefix ?s2))) ]
        => apply link_cut_nn with (prefix s1) (prefix s2)
    | [ |- link_list [?n1; ?n2] (cut (link (prefix ?s1) (future ?n1))
                                       (link (prefix ?s2) (future ?n2))) ]
        => apply link_cut_nn with (prefix s1) (prefix s2)
    end;
    try congruence; try apply c_refl; try apply c_link.
  + destruct (link_future_equiv_link_future _ _  _ (or_intror H1)) as [? [? [? ?]]].
    destruct H4; subst; simpl;
    destruct i1, i2, i3; try (specialize H with 0; simpl in H; exfalso; lia); simpl.
    - destruct x, M; try congruence; simpl.
      * inversion H3.
      * apply link_cut_nf with (prefix (rename_statement s (up_ren r))); try congruence. apply c_refl.
    - destruct x, M; try congruence; simpl.
      * inversion H3.
      * apply link_cut_nf with (prefix (rename_statement s (up_ren r))); try congruence. apply c_link.
  + destruct (link_future_equiv_link_future _ _  _ (or_intror H1)) as [? [? [? ?]]].
    destruct H4; subst; simpl;
    destruct i1, i2, i3; try (specialize H with 0; simpl in H; exfalso; lia); simpl.
    - destruct x, M; try congruence; simpl.
      * inversion H3.
      * apply link_cut_fn with (prefix (rename_statement s (up_ren r))); try congruence. apply c_refl.
    - destruct x, M; try congruence; simpl.
      * inversion H3.
      * apply link_cut_fn with (prefix (rename_statement s (up_ren r))); try congruence. apply c_link.
  + destruct i1, i2, i3, i4; try (specialize H with 0; simpl in H; exfalso; lia); simpl; econstructor.
  + destruct i; try (specialize H with 0; simpl in H; exfalso; lia); simpl.
    destruct (link_future_equiv_link_future _ _  _ (or_intror H2)) as [? [? [? [? | ?]]]]; subst.
    - simpl.
      destruct x, M; try congruence; simpl. inversion H4.
      apply link_cons_n with (prefix (rename_statement s (up_ren r))).
      * assert (bijective (up_ren r)). { apply shift_preserves_bijection; auto. }
        assert (forall x : nat, List.In x (ListDef.map S xs) -> x > 0).
        { intros. apply List.in_map_iff in H6. destruct H6 as [x' []]. lia. }
        pose proof (IHlink_list H6 _ H5).
        clear - H H7.
        repeat rewrite List.map_map in *.
        assert (
          ListDef.map (fun x : nat => S (up_ren r (Nat.pred (S x)))) xs
            = ListDef.map (fun x : nat => S (S (r (Nat.pred x)))) xs
        ).
        {
          apply List.map_ext_in. intros. specialize H with a.
          simpl in H. assert (S i = a \/ List.In a xs) by auto.
          apply H in H1. destruct a; auto. exfalso; lia.
        }
        rewrite <- H0. auto.
      * congruence.
      * apply c_refl.
    - simpl.
      destruct x, M; try congruence; simpl. inversion H4.
      apply link_cons_n with (prefix (rename_statement s (up_ren r))).
      * assert (bijective (up_ren r)). { apply shift_preserves_bijection; auto. }
        assert (forall x : nat, List.In x (ListDef.map S xs) -> x > 0).
        { intros. apply List.in_map_iff in H6. destruct H6 as [x' []]. lia. }
        pose proof (IHlink_list H6 _ H5).
        clear - H H7.
        repeat rewrite List.map_map in *.
        assert (
          ListDef.map (fun x : nat => S (up_ren r (Nat.pred (S x)))) xs
            = ListDef.map (fun x : nat => S (S (r (Nat.pred x)))) xs
        ).
        {
          apply List.map_ext_in. intros. specialize H with a.
          simpl in H. assert (S i = a \/ List.In a xs) by auto.
          apply H in H1. destruct a; auto. exfalso; lia.
        }
        rewrite <- H0. auto.
      * congruence.
      * apply c_link.
  + destruct i1, i2; try (specialize H with 0; simpl in H; exfalso; lia); simpl.
    apply link_cons_f.
    assert (bijective (up_ren r)). { apply shift_preserves_bijection; auto. }
    assert (forall x : nat, List.In x (ListDef.map S xs) -> x > 0).
    { intros. apply List.in_map_iff in H3. destruct H3 as [x' []]. lia. }
    pose proof (IHlink_list H3 _ H2).
    clear - H H4.
    repeat rewrite List.map_map in *.
    assert (
      ListDef.map (fun x : nat => S (up_ren r (Nat.pred (S x)))) xs
        = ListDef.map (fun x : nat => S (S (r (Nat.pred x)))) xs
    ).
    {
      apply List.map_ext_in. intros. specialize H with a.
      simpl in H. assert (S i1 = a \/ S i2 = a \/ List.In a xs) by auto.
      apply H in H1. destruct a; auto. exfalso; lia.
    }
    rewrite <- H0. auto.
Qed.

Lemma link_list_free_vars :
  forall P xs,
    (forall x, List.In x xs -> x > 0) ->
    link_list xs P ->
    (forall x, List.In x xs -> (Nat.pred x) ∈ P).
Proof.
  intros.
  generalize dependent x.
  induction H0; intros.
  + simpl in H4. destruct H4; subst.
    - destruct (link_future_equiv_link_future _ _ _ (or_intror H2)) as [? [? [? [? | ?]]]]; subst.
      * apply fv_cut_l. simpl in H; specialize H with x.
        replace (S (Nat.pred x)) with x by lia.
        repeat econstructor.
      * apply fv_cut_l. simpl in H; specialize H with x.
        replace (S (Nat.pred x)) with x by lia.
        apply fv_link_r; econstructor.
    - destruct H4; try contradiction; subst.
      destruct (link_future_equiv_link_future _ _ _ (or_intror H3)) as [? [? [? [? | ?]]]]; subst.
      * apply fv_cut_r; simpl in H; specialize H with x.
        replace (S (Nat.pred x)) with x by lia.
        repeat econstructor.
      * apply fv_cut_r; simpl in H; specialize H with x.
        replace (S (Nat.pred x)) with x by lia.
        apply fv_link_r; econstructor.
  + simpl in H2. destruct H2 as [? | [? | [? | ?]]]; try contradiction; subst.
    - apply fv_cut_l. simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      repeat econstructor.
    - apply fv_cut_l. simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      apply fv_link_r; econstructor.
    - apply fv_cut_r. simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      destruct (link_future_equiv_link_future _ _ _ (or_intror H1)) as [? [? [? [? | ?]]]]; subst.
      * apply fv_link_l; econstructor.
      * apply fv_link_r; econstructor.
  + simpl in H2. destruct H2 as [? | [? | [? | ?]]]; try contradiction; subst.
    - apply fv_cut_l. simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      destruct (link_future_equiv_link_future _ _ _ (or_intror H1)) as [? [? [? [? | ?]]]]; subst.
      * apply fv_link_l; econstructor.
      * apply fv_link_r; econstructor.
    - apply fv_cut_r. simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      repeat econstructor.
    - apply fv_cut_r. simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      apply fv_link_r; econstructor.
  + simpl in H1. destruct H1 as [? | [? | [? | [? | ?]]]]; try contradiction; subst.
    - apply fv_cut_l. simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      repeat econstructor.
    - apply fv_cut_l. simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      apply fv_link_r; econstructor.
    - apply fv_cut_r. simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      repeat econstructor.
    - apply fv_cut_r. simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      apply fv_link_r; econstructor.
  + simpl in H3. destruct H3; subst.
    - apply fv_cut_l. specialize H with x.
      simpl in H. replace (S (Nat.pred x)) with x by lia.
      destruct (link_future_equiv_link_future _ _ _ (or_intror H2)) as [? [? [? [? | ?]]]]; subst.
      * repeat econstructor.
      * apply fv_link_r; econstructor.
    - apply fv_cut_r. simpl in H. specialize H with x.
      pose proof (H (or_intror H3)).
      replace (S (Nat.pred x)) with x by lia.
      assert (forall x : nat, List.In x (ListDef.map S xs) -> x > 0).
      { intros. apply List.in_map_iff in H5; destruct H5. lia. }
      apply (IHlink_list H5 (S x)).
      apply List.in_map_iff. exists x; auto.
  + simpl in H1. destruct H1 as [? | [? | ?]]; subst.
    - apply fv_cut_l. specialize H with x.
      simpl in H. replace (S (Nat.pred x)) with x by lia.
      repeat econstructor.
    - apply fv_cut_l. specialize H with x.
      simpl in H. replace (S (Nat.pred x)) with x by lia.
      apply fv_link_r. econstructor.
    - apply fv_cut_r. simpl in H. specialize H with x.
      pose proof (H (or_intror (or_intror H1))).
      replace (S (Nat.pred x)) with x by lia.
      assert (forall x : nat, List.In x (ListDef.map S xs) -> x > 0).
      { intros. apply List.in_map_iff in H3; destruct H3. lia. }
      eapply (IHlink_list H3 (S x)).
      apply List.in_map_iff. exists x; auto.
Qed.

Lemma link_list_with_0_at_2_reduces_or_swap :
  forall Γ P xs n0 n1,
    Γ ⊢ P :# -> link_list (n0 :: n1 :: 0 :: xs) P ->
      (exists Q, P ⊳ Q) \/
      (exists Q Q' xs', P ≡ (cut Q Q') /\
                        link_list xs' Q' /\
                        List.In 0 xs' /\
                        length xs' <= S (S (length xs))).
Proof.
  intros.
  inversion H0; subst.
  + left. destruct (link_future_equiv_link_future _ _ _ (or_intror H7)) as [M' [? [? ?]]].
    destruct H2; subst.
    - eexists. eapply r_struct; [apply c_cut_comm | econstructor | apply c_refl].
    - eexists. eapply r_struct.
      * eapply c_trans.
        ** apply c_cut_comm.
        ** apply c_cong_cut; [apply c_link | apply c_refl].
      * econstructor.
      * apply c_refl.
  + left. eexists. eapply r_struct.
    - eapply c_trans.
      * apply c_cut_comm.
      * apply c_cong_cut; [apply c_link | apply c_refl].
    - econstructor.
    - apply c_refl.
  + left. eexists. eapply r_struct; [apply c_cut_comm | econstructor | apply c_refl].
  + inversion H3; subst.
    - left. destruct (link_future_equiv_link_future _ _ _ (or_intror H11)) as [M' [? [? ?]]].
      destruct H2; subst.
      {
        eexists. eapply r_struct.
        + eapply c_trans. { apply c_cong_cut. apply c_refl. apply c_cut_comm. }
          eapply c_comm.
          eapply (c_cut_assoc
            (rename_process (up L) swap01)
            (rename_process (link (future 1) M') swap01)
            (down (rename_process P1 swap01))
          ); autorewrite with up_down_rename_rewrites; auto.
          - apply nfv_10_swap; apply nfv_lift_n; lia.
          - apply nfv_01_swap; intro Hfv.
            assert (1 ∈ (link (future 1) M')) as Hfv1link by repeat econstructor.
            inversion H; subst. inversion H15; subst.
            apply ((proj1 free_var_in_ctx) _ _ Hfv) in H17.
            apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H18.
            destruct H17, H18; simpl in *; subst.
            inversion H13; subst. subst. inversion H18.
        + simpl. eapply r_cong_cut. eapply r_struct.
          - eapply c_cut_comm.
          - econstructor.
          - apply c_refl.
        + apply c_refl.
      }
      {
        eexists. eapply r_struct.
        + eapply c_trans. { apply c_cong_cut. apply c_refl. apply c_cut_comm. }
          eapply c_comm.
          eapply (c_cut_assoc
            (rename_process (up L) swap01)
            (rename_process (link M' (future 1)) swap01)
            (down (rename_process P1 swap01))
          ); autorewrite with up_down_rename_rewrites; auto.
          - apply nfv_10_swap; apply nfv_lift_n; lia.
          - apply nfv_01_swap; intro Hfv.
            assert (1 ∈ (link M' (future 1))) as Hfv1link by repeat econstructor.
            inversion H; subst. inversion H15; subst.
            apply ((proj1 free_var_in_ctx) _ _ Hfv) in H17.
            apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H18.
            destruct H17, H18; simpl in *; subst.
            inversion H13; subst. subst. inversion H18.
        + simpl. eapply r_cong_cut. eapply r_struct.
          - eapply c_trans; [eapply c_cut_comm | eapply c_cong_cut; [eapply c_link | apply c_refl]].
          - econstructor.
          - apply c_refl.
        + apply c_refl.
      }
    - left. eexists. eapply r_struct.
      * eapply c_trans. { apply c_cong_cut. apply c_refl. apply c_cong_cut. apply c_link. apply c_refl. }
        eapply c_comm.
        eapply (c_cut_assoc
          (rename_process (up L) swap01)
          (rename_process (link (future 1) (future (S n1))) swap01)
          (down (rename_process P swap01))
        ); autorewrite with up_down_rename_rewrites; auto.
        ** apply nfv_10_swap; apply nfv_lift_n; lia.
        ** apply nfv_01_swap; intro Hfv.
           assert (1 ∈ (link (future (S n1)) (future 1))) as Hfv1link by repeat econstructor.
           inversion H; subst. inversion H12; subst.
           apply ((proj1 free_var_in_ctx) _ _ Hfv) in H15.
           apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H14.
           destruct H14, H15; simpl in *; subst.
           inversion H10; subst. subst. inversion H15.
      * simpl. eapply r_cong_cut. eapply r_struct.
        ** apply c_cut_comm.
        ** econstructor.
        ** apply c_refl.
      * apply c_refl.
    - left. eexists. eapply r_struct.
      * eapply c_trans. { apply c_cong_cut. apply c_refl. apply c_cut_comm. }
        eapply c_comm.
        eapply (c_cut_assoc
          (rename_process (up L) swap01)
          (rename_process (link (future 1) (future i3)) swap01)
          (down (rename_process P swap01))
        ); autorewrite with up_down_rename_rewrites; auto.
        ** apply nfv_10_swap; apply nfv_lift_n; lia.
        ** apply nfv_01_swap; intro Hfv.
           assert (1 ∈ (link (future 1) (future i3))) as Hfv1link by repeat econstructor.
           inversion H; subst. inversion H12; subst.
           apply ((proj1 free_var_in_ctx) _ _ Hfv) in H14.
           apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H15.
           destruct H14, H15; simpl in *; subst.
           inversion H10; subst. subst. inversion H15.
      * simpl. eapply r_cong_cut. eapply r_struct.
        ** apply c_cut_comm.
        ** econstructor.
        ** apply c_refl.
      * apply c_refl.
    - left. eexists. eapply r_struct.
      * eapply c_trans. { apply c_cong_cut. apply c_refl. apply c_cong_cut. apply c_link. apply c_refl. }
        eapply c_comm.
        eapply (c_cut_assoc
          (rename_process (up L) swap01)
          (rename_process (link (future 1) (future (S n1))) swap01)
          (down (rename_process (link (future i3) (future i4)) swap01))
        ); autorewrite with up_down_rename_rewrites; auto.
        ** apply nfv_10_swap; apply nfv_lift_n; lia.
        ** apply nfv_01_swap; intro Hfv.
           assert (1 ∈ (link (future (S n1)) (future 1))) as Hfv1link by repeat econstructor.
           inversion H; subst. inversion H10; subst.
           apply ((proj1 free_var_in_ctx) _ _ Hfv) in H13.
           apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H12.
           destruct H12, H13; simpl in *; subst.
           inversion H8; subst. subst. inversion H13.
      * simpl. eapply r_cong_cut. eapply r_struct.
        ** apply c_cut_comm.
        ** econstructor.
        ** apply c_refl.
      * apply c_refl.
    - destruct n0.
      { left. eapply link_list_with_0_at_0_reduces in H0; eauto. }
      right.
      eexists; eexists.
      exists ((S (S n0)) :: (List.map swap01 (List.map S (0 :: xs)))).
      repeat split.
      * eapply c_trans.
        ** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
        ** eapply c_trans.
           *** eapply c_comm. eapply (c_cut_assoc
                (rename_process (up L) swap01)
                (rename_process P swap01)
                (down (rename_process L0 swap01))
               ); autorewrite with up_down_rename_rewrites; auto.
                -- apply nfv_10_swap; apply nfv_lift_n; lia.
                -- apply nfv_01_swap; intro Hfv.
                   assert (1 ∈ P) as Hfv1P. {
                      simpl in H5. replace 1 with (Nat.pred 2) by auto.
                      eapply link_list_free_vars; eauto.
                      + intros. simpl in H1. destruct H1 as [? | ?]; try lia.
                        apply List.in_map_iff in H1. destruct H1; lia.
                      + simpl; eauto.
                   }
                   inversion H; subst. inversion H12; subst.
                   apply ((proj1 free_var_in_ctx) _ _ Hfv) in H14.
                   apply ((proj1 free_var_in_ctx) _ _ Hfv1P) in H15.
                   destruct H14, H15; simpl in *; subst.
                   inversion H10. subst. subst. inversion H15.
           *** eapply c_cut_comm.
      * destruct (link_future_equiv_link_future _ _ _ (or_intror H6)) as [? [? [? [? | ?]]]]; subst.
         ** simpl; try congruence. unfold relocate; simpl.
            eapply link_cons_n; try apply c_refl.
            {
              assert (forall x, List.In x (List.map S (1 :: List.map S xs)) -> x > 0).
              { intros. simpl in H2. destruct H2 as [? | ?]; try lia.
                apply List.in_map_iff in H2. destruct H2; lia. }
              pose proof (link_list_rename _ _ _ H2 swap01_is_bijective H5).
              rewrite (List.map_map S Nat.pred _) in H8.
              rewrite List.map_id in H8.
              simpl in H8; auto.
            }
            destruct M; try congruence. inversion H1; subst. simpl. congruence.
         ** simpl; try congruence. unfold relocate; simpl.
            eapply link_cons_n; try apply c_link.
            {
              assert (forall x, List.In x (List.map S (1 :: List.map S xs)) -> x > 0).
              { intros. simpl in H2. destruct H2 as [? | ?]; try lia.
                apply List.in_map_iff in H2. destruct H2; lia. }
              pose proof (link_list_rename _ _ _ H2 swap01_is_bijective H5).
              rewrite (List.map_map S Nat.pred _) in H8.
              rewrite List.map_id in H8.
              simpl in H8; auto.
            }
            destruct M; try congruence. inversion H1; subst. simpl. congruence.
      * simpl; auto.
      * simpl. repeat rewrite List.length_map; lia.
    - left. eexists. eapply r_struct.
      * eapply c_trans. { apply c_cong_cut. apply c_refl. apply c_cong_cut. apply c_link. apply c_refl. }
        eapply c_comm.
        eapply (c_cut_assoc
          (rename_process (up L) swap01)
          (rename_process (link (future 1) (future (S n1))) swap01)
          (down (rename_process P swap01))
        ); autorewrite with up_down_rename_rewrites; auto.
        ** apply nfv_10_swap; apply nfv_lift_n; lia.
        ** apply nfv_01_swap; intro Hfv.
           assert (1 ∈ (link (future (S n1)) (future 1))) as Hfv1link by repeat econstructor.
           inversion H; subst. inversion H10; subst.
           apply ((proj1 free_var_in_ctx) _ _ Hfv) in H13.
           apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H12.
           destruct H12, H13; simpl in *; subst.
           inversion H7; subst. subst. inversion H13.
      * simpl. eapply r_cong_cut. eapply r_struct.
        ** apply c_cut_comm.
        ** econstructor.
        ** apply c_refl.
      * apply c_refl.
  + inversion H5; subst; left.
    - destruct (link_future_equiv_link_future _ _ _ (or_intror H6)) as [M' [? [? [? | ?]]]]; subst.
      {
        eexists. eapply r_struct.
        * eapply c_comm.
          eapply (c_cut_assoc
            (rename_process (up (link (future n0) (future n1))) swap01)
            (rename_process (link (future 1) M') swap01)
            (down (rename_process P2 swap01))
          ); autorewrite with up_down_rename_rewrites; auto.
          ** apply nfv_10_swap; apply nfv_lift_n; lia.
          ** apply nfv_01_swap; intro Hfv.
             assert (1 ∈ (link (future 1) M')) as Hfv1link by repeat econstructor.
             inversion H; subst. inversion H13; subst.
             apply ((proj1 free_var_in_ctx) _ _ Hfv) in H16.
             apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H15.
             destruct H15, H16; simpl in *; subst.
             inversion H11; subst. subst. inversion H16.
        * simpl. eapply r_cong_cut. eapply r_struct.
          ** apply c_cut_comm.
          ** econstructor.
          ** apply c_refl.
        * apply c_refl.
      }
      {
        eexists. eapply r_struct.
        * eapply c_trans. { eapply c_cong_cut. apply c_refl. apply c_cong_cut. apply c_link. apply c_refl. }
          eapply c_comm.
          eapply (c_cut_assoc
            (rename_process (up (link (future n0) (future n1))) swap01)
            (rename_process (link (future 1) M') swap01)
            (down (rename_process P2 swap01))
          ); autorewrite with up_down_rename_rewrites; auto.
          ** apply nfv_10_swap; apply nfv_lift_n; lia.
          ** apply nfv_01_swap; intro Hfv.
             assert (1 ∈ (link M' (future 1))) as Hfv1link by repeat econstructor.
             inversion H; subst. inversion H13; subst.
             apply ((proj1 free_var_in_ctx) _ _ Hfv) in H16.
             apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H15.
             destruct H15, H16; simpl in *; subst.
             inversion H11; subst. subst. inversion H16.
        * simpl. eapply r_cong_cut. eapply r_struct.
          ** apply c_cut_comm.
          ** econstructor.
          ** apply c_refl.
        * apply c_refl.
      }
    - eexists. eapply r_struct.
      * eapply c_comm.
        eapply (c_cut_assoc
          (rename_process (up (link (future n0) (future n1))) swap01)
          (rename_process (link (future 1) (future i2)) swap01)
          (down (rename_process P swap01))
        ); autorewrite with up_down_rename_rewrites; auto.
        ** apply nfv_10_swap; apply nfv_lift_n; lia.
        ** apply nfv_01_swap; intro Hfv.
           assert (1 ∈ (link (future 1) (future i2))) as Hfv1link by repeat econstructor.
           inversion H; subst. inversion H10; subst.
           apply ((proj1 free_var_in_ctx) _ _ Hfv) in H13.
           apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H12.
           destruct H12, H13; simpl in *; subst.
           inversion H8; subst. subst. inversion H13.
      * simpl. eapply r_cong_cut. eapply r_struct.
        ** apply c_cut_comm.
        ** econstructor.
        ** apply c_refl.
      * apply c_refl.
    - destruct (link_future_equiv_link_future _ _ _ (or_intror H6)) as [M' [? [? [? | ?]]]]; subst.
      {
        eexists. eapply r_struct.
        * eapply c_comm.
          eapply (c_cut_assoc
            (rename_process (up (link (future n0) (future n1))) swap01)
            (rename_process (link (future 1) M') swap01)
            (down (rename_process (link (future i2) (future i3)) swap01))
          ); autorewrite with up_down_rename_rewrites; auto.
          ** apply nfv_10_swap; apply nfv_lift_n; lia.
          ** apply nfv_01_swap; intro Hfv.
             assert (1 ∈ (link (future 1) M')) as Hfv1link by repeat econstructor.
             inversion H; subst. inversion H11; subst.
             apply ((proj1 free_var_in_ctx) _ _ Hfv) in H14.
             apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H13.
             destruct H13, H14; simpl in *; subst.
             inversion H9; subst. subst. inversion H14.
        * simpl. eapply r_cong_cut. eapply r_struct.
          ** apply c_cut_comm.
          ** econstructor.
          ** apply c_refl.
        * apply c_refl.
      }
      {
        eexists. eapply r_struct.
        * eapply c_trans. { eapply c_cong_cut. apply c_refl. apply c_cong_cut. apply c_link. apply c_refl. }
          eapply c_comm.
          eapply (c_cut_assoc
            (rename_process (up (link (future n0) (future n1))) swap01)
            (rename_process (link (future 1) M') swap01)
            (down (rename_process (link (future i2) (future i3)) swap01))
          ); autorewrite with up_down_rename_rewrites; auto.
          ** apply nfv_10_swap; apply nfv_lift_n; lia.
          ** apply nfv_01_swap; intro Hfv.
             assert (1 ∈ (link M' (future 1))) as Hfv1link by repeat econstructor.
             inversion H; subst. inversion H11; subst.
             apply ((proj1 free_var_in_ctx) _ _ Hfv) in H14.
             apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H13.
             destruct H13, H14; simpl in *; subst.
             inversion H9; subst. subst. inversion H14.
        * simpl. eapply r_cong_cut. eapply r_struct.
          ** apply c_cut_comm.
          ** econstructor.
          ** apply c_refl.
        * apply c_refl.
      }
    - eexists. eapply r_struct.
      * eapply c_comm.
        eapply (c_cut_assoc
          (rename_process (up (link (future n0) (future n1))) swap01)
          (rename_process (link (future 1) (future i2)) swap01)
          (down (rename_process (link (future i3) (future i4)) swap01))
        ); autorewrite with up_down_rename_rewrites; auto.
        ** apply nfv_10_swap; apply nfv_lift_n; lia.
        ** apply nfv_01_swap; intro Hfv.
           assert (1 ∈ (link (future 1) (future i2))) as Hfv1link by repeat econstructor.
           inversion H; subst. inversion H8; subst.
           apply ((proj1 free_var_in_ctx) _ _ Hfv) in H11.
           apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H10.
           destruct H10, H11; simpl in *; subst.
           inversion H6; subst. subst. inversion H11.
      * simpl. eapply r_cong_cut. eapply r_struct.
        ** apply c_cut_comm.
        ** econstructor.
        ** apply c_refl.
      * apply c_refl.
    - destruct (link_future_equiv_link_future _ _ _ (or_intror H7)) as [M' [? [? [? | ?]]]]; subst.
      {
        eexists. eapply r_struct.
        * eapply c_comm.
          eapply (c_cut_assoc
            (rename_process (up (link (future n0) (future n1))) swap01)
            (rename_process (link (future 1) M') swap01)
            (down (rename_process P swap01))
          ); autorewrite with up_down_rename_rewrites; auto.
          ** apply nfv_10_swap; apply nfv_lift_n; lia.
          ** apply nfv_01_swap; intro Hfv.
             assert (1 ∈ (link (future 1) M')) as Hfv1link by repeat econstructor.
             inversion H; subst. inversion H11; subst.
             apply ((proj1 free_var_in_ctx) _ _ Hfv) in H14.
             apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H13.
             destruct H13, H14; simpl in *; subst.
             inversion H9; subst. subst. inversion H14.
        * simpl. eapply r_cong_cut. eapply r_struct.
          ** apply c_cut_comm.
          ** econstructor.
          ** apply c_refl.
        * apply c_refl.
      }
      {
        eexists. eapply r_struct.
        * eapply c_trans. { eapply c_cong_cut. apply c_refl. apply c_cong_cut. apply c_link. apply c_refl. }
          eapply c_comm.
          eapply (c_cut_assoc
            (rename_process (up (link (future n0) (future n1))) swap01)
            (rename_process (link (future 1) M') swap01)
            (down (rename_process P swap01))
          ); autorewrite with up_down_rename_rewrites; auto.
          ** apply nfv_10_swap; apply nfv_lift_n; lia.
          ** apply nfv_01_swap; intro Hfv.
             assert (1 ∈ (link M' (future 1))) as Hfv1link by repeat econstructor.
             inversion H; subst. inversion H11; subst.
             apply ((proj1 free_var_in_ctx) _ _ Hfv) in H14.
             apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H13.
             destruct H13, H14; simpl in *; subst.
             inversion H9; subst. subst. inversion H14.
        * simpl. eapply r_cong_cut. eapply r_struct.
          ** apply c_cut_comm.
          ** econstructor.
          ** apply c_refl.
        * apply c_refl.
      }
    - eexists. eapply r_struct.
      * eapply c_comm.
        eapply (c_cut_assoc
          (rename_process (up (link (future n0) (future n1))) swap01)
          (rename_process (link (future 1) (future i2)) swap01)
          (down (rename_process P swap01))
        ); autorewrite with up_down_rename_rewrites; auto.
        ** apply nfv_10_swap; apply nfv_lift_n; lia.
        ** apply nfv_01_swap; intro Hfv.
           assert (1 ∈ (link (future 1) (future i2))) as Hfv1link by repeat econstructor.
           inversion H; subst. inversion H9; subst.
           apply ((proj1 free_var_in_ctx) _ _ Hfv) in H12.
           apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H11.
           destruct H11, H12; simpl in *; subst.
           inversion H7; subst. subst. inversion H12.
      * simpl. eapply r_cong_cut. eapply r_struct.
        ** apply c_cut_comm.
        ** econstructor.
        ** apply c_refl.
      * apply c_refl.
Qed.

Lemma link_list_with_0_at_3_reduces_or_swap :
  forall Γ P xs n0 n1 n2,
    Γ ⊢ P :# -> link_list (n0 :: n1 :: n2 :: 0 :: xs) P ->
      (exists Q, P ⊳ Q) \/
      (exists Q Q' xs', P ≡ (cut Q Q') /\
                        link_list xs' Q' /\
                        List.In 0 xs' /\
                        length xs' <= S (S (S (length xs)))).
Proof.
  intros.
  inversion H0; subst.
  + inversion H0; subst; left; eexists.
    - eapply r_struct.
      * eapply c_trans. eapply c_cut_comm. eapply c_cong_cut. apply c_link. apply c_refl.
      * econstructor.
      * apply c_refl.
    - eapply r_struct.
      * eapply c_trans. eapply c_cut_comm. eapply c_cong_cut. apply c_link. apply c_refl.
      * econstructor.
      * apply c_refl.
    - eapply r_struct.
      * eapply c_trans. eapply c_cut_comm. eapply c_cong_cut. apply c_link. apply c_refl.
      * econstructor.
      * apply c_refl.
  + simpl in H3. inversion H3; subst.
    - left.
      destruct (link_future_equiv_link_future _ _ _ (or_intror H10)) as [M' [? [? ?]]].
      destruct H2; subst.
      {
        eexists. eapply r_struct.
        + eapply c_trans. { apply c_cong_cut. apply c_refl. apply c_cut_comm. }
          eapply c_comm.
          eapply (c_cut_assoc
            (rename_process (up L) swap01)
            (rename_process (link (future 1) M') swap01)
            (down (rename_process (link (future (S n1)) (future (S n2))) swap01))
          ); autorewrite with up_down_rename_rewrites; auto.
          - apply nfv_10_swap; apply nfv_lift_n; lia.
          - apply nfv_01_swap; intro Hfv.
            assert (1 ∈ (link (future 1) M')) as Hfv1link by repeat econstructor.
            inversion H; subst. inversion H13; subst.
            apply ((proj1 free_var_in_ctx) _ _ Hfv) in H15.
            apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H16.
            destruct H15, H16; simpl in *; subst.
            inversion H11; subst. subst. inversion H16.
        + simpl. eapply r_cong_cut. eapply r_struct.
          - eapply c_cut_comm.
          - econstructor.
          - apply c_refl.
        + apply c_refl.
      }
      {
        eexists. eapply r_struct.
        + eapply c_trans. { apply c_cong_cut. apply c_refl. apply c_cut_comm. }
          eapply c_comm.
          eapply (c_cut_assoc
            (rename_process (up L) swap01)
            (rename_process (link M' (future 1)) swap01)
            (down (rename_process (link (future (S n1)) (future (S n2))) swap01))
          ); autorewrite with up_down_rename_rewrites; auto.
          - apply nfv_10_swap; apply nfv_lift_n; lia.
          - apply nfv_01_swap; intro Hfv.
            assert (1 ∈ (link M' (future 1))) as Hfv1link by repeat econstructor.
            inversion H; subst. inversion H13; subst.
            apply ((proj1 free_var_in_ctx) _ _ Hfv) in H15.
            apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H16.
            destruct H15, H16; simpl in *; subst.
            inversion H11; subst. subst. inversion H16.
        + simpl. eapply r_cong_cut. eapply r_struct.
          - eapply c_trans; [eapply c_cut_comm | eapply c_cong_cut; [eapply c_link | apply c_refl]].
          - econstructor.
          - apply c_refl.
        + apply c_refl.
      }
    - left.
      eexists. eapply r_struct.
      * eapply c_trans. { apply c_cong_cut. apply c_refl. eapply c_trans. eapply c_cut_comm. eapply c_cong_cut. apply c_link. apply c_refl. }
        eapply c_comm.
        eapply (c_cut_assoc
          (rename_process (up L) swap01)
          (rename_process (link (future 1) (future (S n2))) swap01)
          (down (rename_process P swap01))
        ); autorewrite with up_down_rename_rewrites; auto.
        ** apply nfv_10_swap; apply nfv_lift_n; lia.
        ** apply nfv_01_swap; intro Hfv.
           assert (1 ∈ (link (future (S n2)) (future 1))) as Hfv1link by repeat econstructor.
           inversion H; subst. inversion H12; subst.
           apply ((proj1 free_var_in_ctx) _ _ Hfv) in H14.
           apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H15.
           destruct H14, H15; simpl in *; subst.
           inversion H7; subst. subst. inversion H15.
      * simpl. eapply r_cong_cut. eapply r_struct.
        ** eapply c_cut_comm.
        ** econstructor.
        ** apply c_refl.
      * apply c_refl.
    - left.
      eexists. eapply r_struct.
      * eapply c_trans. { apply c_cong_cut. apply c_refl. apply c_cut_comm. }
        eapply c_comm.
        eapply (c_cut_assoc
          (rename_process (up L) swap01)
          (rename_process (link (future 1) (future i4)) swap01)
          (down (rename_process (link (future (S n1)) (future (S n2))) swap01))
        ); autorewrite with up_down_rename_rewrites; auto.
        ** apply nfv_10_swap; apply nfv_lift_n; lia.
        ** apply nfv_01_swap; intro Hfv.
           assert (1 ∈ (link (future 1) (future i4))) as Hfv1link by repeat econstructor.
           inversion H; subst. inversion H10; subst.
           apply ((proj1 free_var_in_ctx) _ _ Hfv) in H12.
           apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H13.
           destruct H12, H13; simpl in *; subst.
           inversion H7; subst. subst. inversion H13.
      * simpl. eapply r_cong_cut. eapply r_struct.
        ** eapply c_cut_comm.
        ** econstructor.
        ** apply c_refl.
      * apply c_refl.
    - destruct n0.
      { left. eapply link_list_with_0_at_0_reduces in H0; eauto. }
      right.
      eexists; eexists.
      exists ((S (S n0)) :: (List.map swap01 (List.map S (n2 :: 0 :: xs)))).
      repeat split.
      * eapply c_trans.
        ** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
        ** eapply c_trans.
           *** eapply c_comm. eapply (c_cut_assoc
                (rename_process (up L) swap01)
                (rename_process P swap01)
                (down (rename_process L0 swap01))
               ); autorewrite with up_down_rename_rewrites; auto.
                -- apply nfv_10_swap; apply nfv_lift_n; lia.
                -- apply nfv_01_swap; intro Hfv.
                   assert (1 ∈ P) as Hfv1P. {
                      simpl in H5. replace 1 with (Nat.pred 2) by auto.
                      eapply link_list_free_vars; eauto.
                      + intros. simpl in H1. destruct H1 as [? | [? | ?]]; try lia.
                        apply List.in_map_iff in H1. destruct H1; lia.
                      + simpl; eauto.
                   }
                   inversion H; subst. inversion H12; subst.
                   apply ((proj1 free_var_in_ctx) _ _ Hfv) in H14.
                   apply ((proj1 free_var_in_ctx) _ _ Hfv1P) in H15.
                   destruct H14, H15; simpl in *; subst.
                   inversion H10. subst. subst. inversion H15.
           *** eapply c_cut_comm.
      * destruct (link_future_equiv_link_future _ _ _ (or_intror H6)) as [? [? [? [? | ?]]]]; subst.
         ** simpl; try congruence. unfold relocate; simpl.
            eapply link_cons_n; try apply c_refl.
            {
              assert (forall x, List.In x (List.map S ((S n2) :: 1 :: List.map S xs)) -> x > 0).
              { intros. simpl in H2. destruct H2 as [? | [? | ?]]; try lia.
                apply List.in_map_iff in H2. destruct H2; lia. }
              pose proof (link_list_rename _ _ _ H2 swap01_is_bijective H5).
              rewrite (List.map_map S Nat.pred _) in H8.
              rewrite List.map_id in H8.
              simpl in H8; auto.
            }
            destruct M; try congruence. inversion H1; subst. simpl. congruence.
         ** simpl; try congruence. unfold relocate; simpl.
            eapply link_cons_n; try apply c_link.
            {
              assert (forall x, List.In x (List.map S ((S n2) :: 1 :: List.map S xs)) -> x > 0).
              { intros. simpl in H2. destruct H2 as [? | [? | ?]]; try lia.
                apply List.in_map_iff in H2. destruct H2; lia. }
              pose proof (link_list_rename _ _ _ H2 swap01_is_bijective H5).
              rewrite (List.map_map S Nat.pred _) in H8.
              rewrite List.map_id in H8.
              simpl in H8; auto.
            }
            destruct M; try congruence. inversion H1; subst. simpl. congruence.
      * simpl; auto.
      * simpl. repeat rewrite List.length_map; lia.
    - destruct n0.
      { left. eapply link_list_with_0_at_0_reduces in H0; eauto. }
      right.
      eexists; eexists.
      exists ((S (S n0)) :: (List.map swap01 (List.map S (0 :: xs)))).
      repeat split.
      * eapply c_trans.
        ** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
        ** eapply c_trans.
           *** eapply c_comm. eapply (c_cut_assoc
                (rename_process (up L) swap01)
                (rename_process P swap01)
                (down (rename_process (link (future (S n1)) (future (S n2))) swap01))
               ); autorewrite with up_down_rename_rewrites; auto.
                -- apply nfv_10_swap; apply nfv_lift_n; lia.
                -- apply nfv_01_swap; intro Hfv.
                   assert (1 ∈ P) as Hfv1P. {
                      replace 1 with (Nat.pred 2) by auto.
                      eapply link_list_free_vars; eauto.
                      + intros. simpl in H1. destruct H1 as [? | ?]; try lia.
                        apply List.in_map_iff in H1. destruct H1; lia.
                      + simpl; eauto.
                   }
                   inversion H; subst. inversion H10; subst.
                   apply ((proj1 free_var_in_ctx) _ _ Hfv) in H12.
                   apply ((proj1 free_var_in_ctx) _ _ Hfv1P) in H13.
                   destruct H12, H13; simpl in *; subst.
                   inversion H7. subst. subst. inversion H13.
           *** eapply c_cut_comm.
      * destruct (link_future_equiv_link_future _ _ _ (or_intror H6)) as [? [? [? [? | ?]]]]; subst.
         ** simpl; try congruence. unfold relocate; simpl.
            eapply link_cons_n; try apply c_refl.
            {
              assert (forall x, List.In x (List.map S (1 :: List.map S xs)) -> x > 0).
              { intros. simpl in H2. destruct H2 as [? | ?]; try lia.
                apply List.in_map_iff in H2. destruct H2; lia. }
              pose proof (link_list_rename _ _ _ H2 swap01_is_bijective H8).
              rewrite (List.map_map S Nat.pred _) in H5.
              rewrite List.map_id in H5.
              simpl in H5; auto.
            }
            destruct M; try congruence. inversion H1; subst. simpl. congruence.
         ** simpl; try congruence. unfold relocate; simpl.
            eapply link_cons_n; try apply c_link.
            {
              assert (forall x, List.In x (List.map S (1 :: List.map S xs)) -> x > 0).
              { intros. simpl in H2. destruct H2 as [? | ?]; try lia.
                apply List.in_map_iff in H2. destruct H2; lia. }
              pose proof (link_list_rename _ _ _ H2 swap01_is_bijective H8).
              rewrite (List.map_map S Nat.pred _) in H5.
              rewrite List.map_id in H5.
              simpl in H5; auto.
            }
            destruct M; try congruence. inversion H1; subst. simpl. congruence.
      * simpl; auto.
      * simpl. repeat rewrite List.length_map; lia.
  + simpl in H5; inversion H5; subst.
    - left.
      assert (xs = []). { destruct xs; simpl in H3; auto. congruence. } subst.
      destruct (link_future_equiv_link_future _ _ _ (or_intror H9)) as [M' [? [? ?]]].
      destruct H2; subst.
      {
        eexists. eapply r_struct.
        + eapply c_trans. { apply c_cong_cut. apply c_refl. apply c_cut_comm. }
          eapply c_comm.
          eapply (c_cut_assoc
            (rename_process (up (link (future n0) (future n1))) swap01)
            (rename_process (link (future 1) M') swap01)
            (down (rename_process P1 swap01))
          ); autorewrite with up_down_rename_rewrites; auto.
          - apply nfv_10_swap; apply nfv_lift_n; lia.
          - apply nfv_01_swap; intro Hfv.
            assert (1 ∈ (link (future 1) M')) as Hfv1link by repeat econstructor.
            inversion H; subst. inversion H13; subst.
            apply ((proj1 free_var_in_ctx) _ _ Hfv) in H15.
            apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H16.
            destruct H15, H16; simpl in *; subst.
            inversion H11; subst. subst. inversion H16.
        + simpl. eapply r_cong_cut. eapply r_struct.
          - eapply c_cut_comm.
          - econstructor.
          - apply c_refl.
        + apply c_refl.
      }
      {
        eexists. eapply r_struct.
        + eapply c_trans. { apply c_cong_cut. apply c_refl. apply c_cut_comm. }
          eapply c_comm.
          eapply (c_cut_assoc
            (rename_process (up (link (future n0) (future n1))) swap01)
            (rename_process (link M' (future 1)) swap01)
            (down (rename_process P1 swap01))
          ); autorewrite with up_down_rename_rewrites; auto.
          - apply nfv_10_swap; apply nfv_lift_n; lia.
          - apply nfv_01_swap; intro Hfv.
            assert (1 ∈ (link M' (future 1))) as Hfv1link by repeat econstructor.
            inversion H; subst. inversion H13; subst.
            apply ((proj1 free_var_in_ctx) _ _ Hfv) in H15.
            apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H16.
            destruct H15, H16; simpl in *; subst.
            inversion H11; subst. subst. inversion H16.
        + simpl. eapply r_cong_cut. eapply r_struct.
          - eapply c_trans; [eapply c_cut_comm | eapply c_cong_cut; [eapply c_link | apply c_refl]].
          - econstructor.
          - apply c_refl.
        + apply c_refl.
      }
    - left.
      eexists. eapply r_struct.
      * eapply c_trans. { apply c_cong_cut. apply c_refl. apply c_cong_cut. apply c_link. apply c_refl. }
        eapply c_comm.
        eapply (c_cut_assoc
          (rename_process (up (link (future n0) (future n1))) swap01)
          (rename_process (link (future 1) (future (S n2))) swap01)
          (down (rename_process P swap01))
        ); autorewrite with up_down_rename_rewrites; auto.
        ** apply nfv_10_swap; apply nfv_lift_n; lia.
        ** apply nfv_01_swap; intro Hfv.
           assert (1 ∈ (link (future (S n2)) (future 1))) as Hfv1link by repeat econstructor.
           inversion H; subst. inversion H10; subst.
           apply ((proj1 free_var_in_ctx) _ _ Hfv) in H13.
           apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H12.
           destruct H12, H13; simpl in *; subst.
           inversion H8; subst. subst. inversion H13.
      * simpl. eapply r_cong_cut. eapply r_struct.
        ** eapply c_cut_comm.
        ** econstructor.
        ** apply c_refl.
      * apply c_refl.
    - left.
      eexists. eapply r_struct.
      * eapply c_trans. { apply c_cong_cut. apply c_refl. apply c_cut_comm. }
        eapply c_comm.
        eapply (c_cut_assoc
          (rename_process (up (link (future n0) (future n1))) swap01)
          (rename_process (link (future 1) (future i3)) swap01)
          (down (rename_process P swap01))
        ); autorewrite with up_down_rename_rewrites; auto.
        ** apply nfv_10_swap; apply nfv_lift_n; lia.
        ** apply nfv_01_swap; intro Hfv.
           assert (1 ∈ (link (future 1) (future i3))) as Hfv1link by repeat econstructor.
           inversion H; subst. inversion H10; subst.
           apply ((proj1 free_var_in_ctx) _ _ Hfv) in H12.
           apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H13.
           destruct H12, H13; simpl in *; subst.
           inversion H8; subst. subst. inversion H13.
      * simpl. eapply r_cong_cut. eapply r_struct.
        ** eapply c_cut_comm.
        ** econstructor.
        ** apply c_refl.
      * apply c_refl.
    - left.
      eexists. eapply r_struct.
      * eapply c_trans. { apply c_cong_cut. apply c_refl. apply c_cong_cut. apply c_link. apply c_refl. }
        eapply c_comm.
        eapply (c_cut_assoc
          (rename_process (up (link (future n0) (future n1))) swap01)
          (rename_process (link (future 1) (future (S n2))) swap01)
          (down (rename_process (link (future i3) (future i4)) swap01))
        ); autorewrite with up_down_rename_rewrites; auto.
        ** apply nfv_10_swap; apply nfv_lift_n; lia.
        ** apply nfv_01_swap; intro Hfv.
           assert (1 ∈ (link (future (S n2)) (future 1))) as Hfv1link by repeat econstructor.
           inversion H; subst. inversion H8; subst.
           apply ((proj1 free_var_in_ctx) _ _ Hfv) in H11.
           apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H10.
           destruct H10, H11; simpl in *; subst.
           inversion H6; subst. subst. inversion H11.
      * simpl. eapply r_cong_cut. eapply r_struct.
        ** eapply c_cut_comm.
        ** econstructor.
        ** apply c_refl.
      * apply c_refl.
    - destruct n0.
      { left. eapply link_list_with_0_at_0_reduces in H0; eauto. }
      destruct n1.
      { left. eapply link_list_with_0_at_1_reduces in H0; eauto. }
      right.
      eexists; eexists.
      exists ((S (S n0)) :: (S (S n1)) :: (List.map swap01 (List.map S (0 :: xs)))).
      repeat split.
      * eapply c_trans.
        ** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
        ** eapply c_trans.
           *** eapply c_comm. eapply (c_cut_assoc
                (rename_process (up (link (future (S n0)) (future (S n1)))) swap01)
                (rename_process P swap01)
                (down (rename_process L swap01))
               ); autorewrite with up_down_rename_rewrites; auto.
                -- apply nfv_10_swap; apply nfv_lift_n; lia.
                -- apply nfv_01_swap; intro Hfv.
                   assert (1 ∈ P) as Hfv1P. {
                      replace 1 with (Nat.pred 2) by auto.
                      eapply link_list_free_vars; eauto.
                      + intros. simpl in H1. destruct H1 as [? | ?]; try lia.
                        apply List.in_map_iff in H1. destruct H1; lia.
                      + simpl; eauto.
                   }
                   inversion H; subst. inversion H10; subst.
                   apply ((proj1 free_var_in_ctx) _ _ Hfv) in H12.
                   apply ((proj1 free_var_in_ctx) _ _ Hfv1P) in H13.
                   destruct H12, H13; simpl in *; subst.
                   inversion H8. subst. subst. inversion H13.
           *** eapply c_cut_comm.
      * simpl; unfold relocate; simpl.
        eapply link_cons_f; try apply c_refl.
        assert (forall x, List.In x (List.map S (1 :: List.map S xs)) -> x > 0).
        { intros. simpl in H1. destruct H1 as [? | ?]; try lia.
          apply List.in_map_iff in H1. destruct H1; lia. }
        pose proof (link_list_rename _ _ _ H1 swap01_is_bijective H3).
        rewrite (List.map_map S Nat.pred _) in H2.
        rewrite List.map_id in H2.
        simpl in H2; auto.
      * simpl; auto.
      * simpl. repeat rewrite List.length_map; lia.
    - left.
      eexists. eapply r_struct.
      * eapply c_trans. { apply c_cong_cut. apply c_refl. apply c_cong_cut. apply c_link. apply c_refl. }
        eapply c_comm.
        eapply (c_cut_assoc
          (rename_process (up (link (future n0) (future n1))) swap01)
          (rename_process (link (future 1) (future (S n2))) swap01)
          (down (rename_process P swap01))
        ); autorewrite with up_down_rename_rewrites; auto.
        ** apply nfv_10_swap; apply nfv_lift_n; lia.
        ** apply nfv_01_swap; intro Hfv.
           assert (1 ∈ (link (future (S n2)) (future 1))) as Hfv1link by repeat econstructor.
           inversion H; subst. inversion H8; subst.
           apply ((proj1 free_var_in_ctx) _ _ Hfv) in H11.
           apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H10.
           destruct H10, H11; simpl in *; subst.
           inversion H4; subst. subst. inversion H11.
      * simpl. eapply r_cong_cut. eapply r_struct.
        ** eapply c_cut_comm.
        ** econstructor.
        ** apply c_refl.
      * apply c_refl.
Qed.

Lemma link_list_swap_0_1 :
  forall Γ P n0 n1 n2 n3 xs,
    0 <> n0 ->
    0 <> n1 ->
    0 <> n2 ->
    0 <> n3 ->
    Γ ⊢ P :# -> length xs > 0 -> List.In 0 xs -> link_list (n0 :: n1 :: n2 :: n3 :: xs) P ->
    exists Q Q' xs', P ≡ (cut Q Q') /\ link_list xs' Q' /\ List.In 0 xs' /\ length xs' <= S (S (S (length xs))).
Proof.
  intros.
  inversion H4; subst.
  + assert (xs = [0]).
    {
      destruct xs.
      + simpl in H8; congruence.
      + destruct xs.
        - simpl in H5. f_equal. destruct H5; auto. contradiction.
        - simpl in H8; congruence.
    }
    subst. clear H4 H5 H8.
    inversion H6; subst.
    - simpl in H7. inversion H7; subst.
      * eexists; eexists. exists [S n0; S n3; 0].
        repeat split.
        ** eapply c_trans.
          *** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
          *** eapply c_trans.
             **** eapply c_comm. eapply (c_cut_assoc
                  (rename_process (up L) swap01)
                  (rename_process (link (future (S n3)) (future 1)) swap01)
                  (down (rename_process (link (future (S n1)) (future (S n2))) swap01))
                 ); autorewrite with up_down_rename_rewrites; auto.
                  -- apply nfv_10_swap; apply nfv_lift_n; lia.
                  -- apply nfv_01_swap; intro Hfv. inversion Hfv; subst.
                     --- inversion H9; subst. congruence.
                     --- inversion H9; subst. congruence.
             **** eapply c_cut_comm.
        ** destruct (link_future_equiv_link_future _ _ _ (or_intror H10)) as [? [? [? [? | ?]]]]; subst.
           *** destruct n0, n3; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cut_fn; try eapply c_refl.
               destruct M; try congruence. inversion H4; subst.
               simpl. congruence.
           *** destruct n0, n3; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cut_fn; try eapply c_link.
               destruct M; try congruence. inversion H4; subst.
               simpl. congruence.
        ** simpl. auto.
        ** simpl; lia.
      * eexists; eexists. exists [S n0; S n2; S n3; 0].
        repeat split.
        ** eapply c_trans.
          *** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
          *** eapply c_trans.
             **** eapply c_comm. eapply (c_cut_assoc
                  (rename_process (up L) swap01)
                  (rename_process P swap01)
                  (down (rename_process L0 swap01))
                 ); autorewrite with up_down_rename_rewrites; auto.
                  -- apply nfv_10_swap; apply nfv_lift_n; lia.
                  -- apply nfv_01_swap; intro Hfv.
                     assert (1 ∈ P) as Hfv1P. {
                        simpl in H9. replace 1 with (Nat.pred 2) by auto.
                        eapply link_list_free_vars; eauto.
                        + intro; simpl. lia.
                        + simpl; auto.
                      }
                     inversion H3; subst. inversion H16; subst.
                     apply ((proj1 free_var_in_ctx) _ _ Hfv) in H18.
                     apply ((proj1 free_var_in_ctx) _ _ Hfv1P) in H19.
                     destruct H18, H19; simpl in *; subst. inversion H14. subst. subst. inversion H19.
             **** eapply c_cut_comm.
        ** destruct (link_future_equiv_link_future _ _ _ (or_intror H10)) as [? [? [? [? | ?]]]]; subst.
           *** destruct n0, n3; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cons_n; try eapply c_refl.
               { simpl.
                assert (forall x, List.In x (List.map S [S n2; S (S n3); 1]) -> x > 0).
                { intros. simpl in H5. lia. }
                pose proof (link_list_rename _ _ _ H5 swap01_is_bijective H9).
                rewrite (List.map_map S Nat.pred _) in H12.
                simpl in H12. destruct n2; try congruence.
               }
               destruct M; try congruence. inversion H4; subst.
               simpl. congruence.
           *** destruct n0, n3; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cons_n; try eapply c_link.
               { simpl.
                assert (forall x, List.In x (List.map S [S n2; S (S n3); 1]) -> x > 0).
                { intros. simpl in H5. lia. }
                pose proof (link_list_rename _ _ _ H5 swap01_is_bijective H9).
                rewrite (List.map_map S Nat.pred _) in H12.
                simpl in H12. destruct n2; try congruence.
               }
               destruct M; try congruence. inversion H4; subst.
               simpl. congruence.
        ** simpl. auto.
        ** simpl; lia.
      * eexists; eexists. exists [S n0; S n3; 0].
        repeat split.
        ** eapply c_trans.
          *** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
          *** eapply c_trans.
             **** eapply c_comm. eapply (c_cut_assoc
                  (rename_process (up L) swap01)
                  (rename_process P swap01)
                  (down (rename_process (link (future (S n1)) (future (S n2))) swap01))
                 ); autorewrite with up_down_rename_rewrites; auto.
                  -- apply nfv_10_swap; apply nfv_lift_n; lia.
                  -- apply nfv_01_swap; intro Hfv.
                     assert (1 ∈ P) as Hfv1P. {
                        simpl in H12. replace 1 with (Nat.pred 2) by auto.
                        eapply link_list_free_vars; eauto.
                        + intro; simpl. lia.
                        + simpl; auto.
                      }
                     inversion H3; subst. inversion H14; subst.
                     apply ((proj1 free_var_in_ctx) _ _ Hfv) in H16.
                     apply ((proj1 free_var_in_ctx) _ _ Hfv1P) in H17.
                     destruct H16, H17; simpl in *; subst. inversion H11. subst. subst. inversion H17.
             **** eapply c_cut_comm.
        ** destruct (link_future_equiv_link_future _ _ _ (or_intror H10)) as [? [? [? [? | ?]]]]; subst.
           *** destruct n0, n3; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cons_n; try eapply c_refl.
               { simpl.
                assert (forall x, List.In x (List.map S [S (S n3); 1]) -> x > 0).
                { intros. simpl in H5. lia. }
                pose proof (link_list_rename _ _ _ H5 swap01_is_bijective H12).
                rewrite (List.map_map S Nat.pred _) in H9.
                simpl in H9; auto.
               }
               destruct M; try congruence. inversion H4; subst.
               simpl. congruence.
           *** destruct n0, n3; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cons_n; try eapply c_link.
               { simpl.
                assert (forall x, List.In x (List.map S [S (S n3); 1]) -> x > 0).
                { intros. simpl in H5. lia. }
                pose proof (link_list_rename _ _ _ H5 swap01_is_bijective H12).
                rewrite (List.map_map S Nat.pred _) in H9.
                simpl in H9; auto.
               }
               destruct M; try congruence. inversion H4; subst.
               simpl. congruence.
        ** simpl. auto.
        ** simpl; lia.
    - simpl in H9. inversion H9; subst.
      * eexists; eexists. exists [S n0; S n1; 0].
        repeat split.
        ** eapply c_trans.
          *** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
          *** eapply c_trans.
             **** eapply c_comm. eapply (c_cut_assoc
                  (rename_process (up (link (future n0) (future n1))) swap01)
                  (rename_process P swap01)
                  (down (rename_process (link (future (S n2)) (future (S n3))) swap01))
                 ); autorewrite with up_down_rename_rewrites; auto.
                  -- apply nfv_10_swap; apply nfv_lift_n; lia.
                  -- apply nfv_01_swap; intro Hfv. inversion Hfv; subst;
                     inversion H7; subst; congruence.
             **** eapply c_cut_comm.
        ** destruct (link_future_equiv_link_future _ _ _ (or_intror H11)) as [? [? [? [? | ?]]]]; subst.
           *** destruct n0, n1; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cut_nf; try eapply c_refl.
               destruct M; try congruence. inversion H4; subst.
               simpl. congruence.
           *** destruct n0, n1; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cut_nf; try eapply c_link.
               destruct M; try congruence. inversion H4; subst.
               simpl. congruence.
        ** simpl. auto.
        ** simpl; lia.
      * eexists; eexists. exists [S n0; S n1; S n3; 0].
        repeat split.
        ** eapply c_trans.
          *** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
          *** eapply c_trans.
             **** eapply c_comm. eapply (c_cut_assoc
                  (rename_process (up (link (future n0) (future n1))) swap01)
                  (rename_process (link (future (S n3)) (future 1)) swap01)
                  (down (rename_process P swap01))
                 ); autorewrite with up_down_rename_rewrites; auto.
                  -- apply nfv_10_swap; apply nfv_lift_n; lia.
                  -- apply nfv_01_swap; intro Hfv.
                     assert (1 ∈ (link (future (S n3)) (future 1))) as Hfv1link. {
                        apply fv_link_r; econstructor.
                      }
                     inversion H3; subst. inversion H13; subst.
                     apply ((proj1 free_var_in_ctx) _ _ Hfv) in H15.
                     apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H16.
                     destruct H15, H16; simpl in *; subst. inversion H8. subst. subst. inversion H16.
             **** eapply c_cut_comm.
        ** destruct (link_future_equiv_link_future _ _ _ (or_intror H11)) as [? [? [? [? | ?]]]]; subst.
           *** destruct n0, n1, n3; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cut_ff.
           *** destruct n0, n1, n3; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cut_ff.
        ** simpl. auto.
        ** simpl; lia.
      * eexists; eexists. exists [S n0; S n1; S n3; 0].
        repeat split.
        ** eapply c_trans.
          *** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
          *** eapply c_trans.
             **** eapply c_comm. eapply (c_cut_assoc
                  (rename_process (up (link (future n0) (future n1))) swap01)
                  (rename_process P swap01)
                  (down (rename_process L swap01))
                 ); autorewrite with up_down_rename_rewrites; auto.
                  -- apply nfv_10_swap; apply nfv_lift_n; lia.
                  -- apply nfv_01_swap; intro Hfv.
                     assert (1 ∈ P) as Hfv1P. {
                        simpl in H7. replace 1 with (Nat.pred 2) by auto.
                        eapply link_list_free_vars; eauto.
                        + intro; simpl. lia.
                        + simpl; auto.
                      }
                     inversion H3; subst. inversion H14; subst.
                     apply ((proj1 free_var_in_ctx) _ _ Hfv) in H16.
                     apply ((proj1 free_var_in_ctx) _ _ Hfv1P) in H17.
                     destruct H16, H17; simpl in *; subst. inversion H12. subst. subst. inversion H17.
             **** eapply c_cut_comm.
        ** destruct (link_future_equiv_link_future _ _ _ (or_intror H11)) as [? [? [? [? | ?]]]]; subst.
           *** destruct n0, n1, n3; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cons_f; try eapply c_refl.
               simpl.
               assert (forall x, List.In x (List.map S [S (S n3); 1]) -> x > 0).
               { intros. simpl in H5. lia. }
               pose proof (link_list_rename _ _ _ H5 swap01_is_bijective H7).
               rewrite (List.map_map S Nat.pred _) in H10.
               simpl in H9; auto.
           *** destruct n0, n1, n3; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cons_f; try eapply c_link.
               simpl.
               assert (forall x, List.In x (List.map S [S (S n3); 1]) -> x > 0).
               { intros. simpl in H5. lia. }
               pose proof (link_list_rename _ _ _ H5 swap01_is_bijective H7).
               rewrite (List.map_map S Nat.pred _) in H10.
               simpl in H10; auto.
        ** simpl; auto.
        ** simpl; lia.
      * simpl in H10. inversion H10. simpl in H7. inversion H7.
  + destruct xs. inversion H7.
    inversion H6; subst.
    - simpl in H11. inversion H11; subst.
      * assert (xs = []). { destruct xs; simpl in H17; auto. congruence. } subst.
        assert (n = 0). { simpl in H5; destruct H5; auto; contradiction. } subst.
        eexists; eexists. exists [S n0; S n3; 0].
        repeat split.
        ** eapply c_trans.
          *** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
          *** eapply c_trans.
             **** eapply c_comm. eapply (c_cut_assoc
                  (rename_process (up L) swap01)
                  (rename_process (link (future (S n3)) (future 1)) swap01)
                  (down (rename_process (link (future (S n1)) (future (S n2))) swap01))
                 ); autorewrite with up_down_rename_rewrites; auto.
                  -- apply nfv_10_swap; apply nfv_lift_n; lia.
                  -- apply nfv_01_swap; intro Hfv.
                     inversion Hfv; subst; inversion H13; subst; congruence.
             **** eapply c_cut_comm.
        ** destruct (link_future_equiv_link_future _ _ _ (or_intror H14)) as [? [? [? [? | ?]]]]; subst.
           *** destruct n0, n3; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cut_fn; try eapply c_refl.
               destruct M; try congruence. inversion H9; subst.
               simpl. congruence.
           *** destruct n0, n3; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cut_fn; try eapply c_link.
               destruct M; try congruence. inversion H9; subst.
               simpl. congruence.
        ** simpl. auto.
        ** simpl; lia.
      * eexists; eexists.
        exists ((S n0) :: (S n2) :: (S n3) :: (List.map swap01 (List.map S (n :: xs)))).
        repeat split.
        ** eapply c_trans.
          *** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
          *** eapply c_trans.
             **** eapply c_comm. eapply (c_cut_assoc
                  (rename_process (up L) swap01)
                  (rename_process P swap01)
                  (down (rename_process L0 swap01))
                 ); autorewrite with up_down_rename_rewrites; auto.
                  -- apply nfv_10_swap; apply nfv_lift_n; lia.
                  -- apply nfv_01_swap; intro Hfv.
                     assert (1 ∈ P) as Hfv1P. {
                        simpl in H13. replace 1 with (Nat.pred 2) by auto.
                        eapply link_list_free_vars; eauto.
                        + intros. simpl in H9. destruct H9 as [? | [? | [? | ?]]]; try lia.
                          apply List.in_map_iff in H9. destruct H9; lia.
                        + simpl in H5; destruct H5; subst; simpl; auto.
                          right. right. right.
                          rewrite List.map_map. apply List.in_map_iff. exists 0; auto.
                     }
                     inversion H3; subst. inversion H20; subst.
                     apply ((proj1 free_var_in_ctx) _ _ Hfv) in H22.
                     apply ((proj1 free_var_in_ctx) _ _ Hfv1P) in H23.
                     destruct H22, H23; simpl in *; subst. inversion H18. subst. subst. inversion H23.
             **** eapply c_cut_comm.
        ** destruct (link_future_equiv_link_future _ _ _ (or_intror H14)) as [? [? [? [? | ?]]]]; subst.
           *** destruct n0; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cons_n; try eapply c_refl.
               { simpl.
                assert (forall x, List.In x (List.map S (S n2 :: S n3 :: S n :: List.map S xs)) -> x > 0).
                { intros. intros. simpl in H10. destruct H10 as [? | [? | [? | ?]]]; try lia.
                  apply List.in_map_iff in H10. destruct H10; lia. }
                pose proof (link_list_rename _ _ _ H10 swap01_is_bijective H13).
                rewrite (List.map_map S Nat.pred _) in H16.
                rewrite List.map_id in H16.
                simpl in H16; auto. destruct n2, n3; try congruence.
               }
               destruct M; try congruence. inversion H9; subst.
               simpl. congruence.
           *** destruct n0; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cons_n; try eapply c_link.
               { simpl.
                assert (forall x, List.In x (List.map S (S n2 :: S n3 :: S n :: List.map S xs)) -> x > 0).
                { intros. intros. simpl in H10. destruct H10 as [? | [? | [? | ?]]]; try lia.
                  apply List.in_map_iff in H10. destruct H10; lia. }
                pose proof (link_list_rename _ _ _ H10 swap01_is_bijective H13).
                rewrite (List.map_map S Nat.pred _) in H16.
                rewrite List.map_id in H16.
                simpl in H16; auto. destruct n2, n3; try congruence.
               }
               destruct M; try congruence. inversion H9; subst.
               simpl. congruence.
        ** simpl. right. right. right. destruct n; auto.
           simpl in H5. destruct H5; try congruence. right.
           rewrite List.map_map. apply List.in_map_iff. exists 0; auto.
        ** simpl. repeat rewrite List.length_map.
           simpl in *; lia.
      * eexists; eexists.
        exists ((S n0) :: (S n3) :: (List.map swap01 (List.map S (n :: xs)))).
        repeat split.
        ** eapply c_trans.
          *** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
          *** eapply c_trans.
             **** eapply c_comm. eapply (c_cut_assoc
                  (rename_process (up L) swap01)
                  (rename_process P swap01)
                  (down (rename_process (link (future (S n1)) (future (S n2))) swap01))
                 ); autorewrite with up_down_rename_rewrites; auto.
                  -- apply nfv_10_swap; apply nfv_lift_n; lia.
                  -- apply nfv_01_swap; intro Hfv.
                     inversion Hfv; subst; inversion H13; subst; congruence.
             **** eapply c_cut_comm.
        ** destruct (link_future_equiv_link_future _ _ _ (or_intror H14)) as [? [? [? [? | ?]]]]; subst.
           *** destruct n0; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cons_n; try eapply c_refl.
               { simpl.
                assert (forall x, List.In x (List.map S (S n3 :: S n :: List.map S xs)) -> x > 0).
                { intros. intros. simpl in H10. destruct H10 as [? | [? | ?]]; try lia.
                  apply List.in_map_iff in H10. destruct H10; lia. }
                pose proof (link_list_rename _ _ _ H10 swap01_is_bijective H16).
                rewrite (List.map_map S Nat.pred _) in H13.
                rewrite List.map_id in H13.
                simpl in H13. destruct n3; try congruence.
               }
               destruct M; try congruence. inversion H9; subst.
               simpl. congruence.
           *** destruct n0; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cons_n; try eapply c_link.
               { simpl.
                assert (forall x, List.In x (List.map S (S n3 :: S n :: List.map S xs)) -> x > 0).
                { intros. intros. simpl in H10. destruct H10 as [? | [? | ?]]; try lia.
                  apply List.in_map_iff in H10. destruct H10; lia. }
                pose proof (link_list_rename _ _ _ H10 swap01_is_bijective H16).
                rewrite (List.map_map S Nat.pred _) in H13.
                rewrite List.map_id in H13.
                simpl in H13. destruct n3; try congruence.
               }
               destruct M; try congruence. inversion H9; subst.
               simpl. congruence.
        ** simpl. right. right. destruct n; auto.
           simpl in H5. destruct H5; try congruence. right.
           rewrite List.map_map. apply List.in_map_iff. exists 0; auto.
        ** simpl. repeat rewrite List.length_map.
           simpl in *; lia.
    - simpl in H13. inversion H13; subst.
      * assert (xs = []). { destruct xs; simpl in H14; auto. congruence. } subst.
        assert (n = 0). { simpl in H5; destruct H5; auto; contradiction. } subst.
        eexists; eexists. exists [S n0; S n1; 0].
        repeat split.
        ** eapply c_trans.
          *** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
          *** eapply c_trans.
             **** eapply c_comm. eapply (c_cut_assoc
                  (rename_process (up (link (future n0) (future n1))) swap01)
                  (rename_process P swap01)
                  (down (rename_process (link (future (S n2)) (future (S n3))) swap01))
                 ); autorewrite with up_down_rename_rewrites; auto.
                  -- apply nfv_10_swap; apply nfv_lift_n; lia.
                  -- apply nfv_01_swap; intro Hfv.
                     inversion Hfv; subst; inversion H11; subst; congruence.
             **** eapply c_cut_comm.
        ** destruct (link_future_equiv_link_future _ _ _ (or_intror H16)) as [? [? [? [? | ?]]]]; subst.
           *** destruct n0, n1; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cut_nf; try eapply c_refl.
               destruct M; try congruence. inversion H9; subst.
               simpl. congruence.
           *** destruct n0, n1; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cut_nf; try eapply c_link.
               destruct M; try congruence. inversion H9; subst.
               simpl. congruence.
        ** simpl. auto.
        ** simpl; lia.
      * assert (xs = []). { destruct xs; simpl in H14; auto. congruence. } subst.
        assert (n = 0). { simpl in H5; destruct H5; auto; contradiction. } subst.
        eexists; eexists. exists [S n0; S n1; S n3; 0].
        repeat split.
        ** eapply c_trans.
          *** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
          *** eapply c_trans.
             **** eapply c_comm. eapply (c_cut_assoc
                  (rename_process (up (link (future n0) (future n1))) swap01)
                  (rename_process (link (future (S n3)) (future 1)) swap01)
                  (down (rename_process P swap01))
                 ); autorewrite with up_down_rename_rewrites; auto.
                  -- apply nfv_10_swap; apply nfv_lift_n; lia.
                  -- apply nfv_01_swap; intro Hfv.
                     assert (1 ∈ (link (future (S n3)) (future 1))) as Hfv1link. {
                        apply fv_link_r; econstructor.
                     }
                     inversion H3; subst. inversion H18; subst.
                     apply ((proj1 free_var_in_ctx) _ _ Hfv) in H20.
                     apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H21.
                     destruct H20, H21; simpl in *; subst. inversion H12. subst. subst. inversion H21.
             **** eapply c_cut_comm.
        ** destruct (link_future_equiv_link_future _ _ _ (or_intror H16)) as [? [? [? [? | ?]]]]; subst.
           *** destruct n0, n1, n3; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cut_ff.
           *** destruct n0, n1, n3; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cut_ff.
        ** simpl. auto.
        ** simpl; lia.
      * eexists; eexists.
        exists ((S n0) :: (S n1) :: (List.map swap01 (List.map S (n :: xs)))).
        repeat split.
        ** eapply c_trans.
          *** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
          *** eapply c_trans.
             **** eapply c_comm. eapply (c_cut_assoc
                  (rename_process (up (link (future n0) (future n1))) swap01)
                  (rename_process (link (future (S n)) (future i4)) swap01)
                  (down (rename_process (link (future (S n2)) (future (S n3))) swap01))
                 ); autorewrite with up_down_rename_rewrites; auto.
                  -- apply nfv_10_swap; apply nfv_lift_n; lia.
                  -- apply nfv_01_swap; intro Hfv.
                     inversion Hfv; subst; inversion H11; subst; congruence.
             **** eapply c_cut_comm.
        ** simpl. rewrite <- H14.
           destruct n0, n1; try congruence; unfold relocate; simpl.
           apply link_cut_ff.
        ** simpl. right. right. destruct n; auto. right.
           simpl in H5. destruct H5; try congruence.
           rewrite List.map_map. apply List.in_map_iff. exists 0; auto.
        ** simpl. repeat rewrite List.length_map.
           simpl in *; lia.
      * eexists; eexists.
        exists ((S n0) :: (S n1) :: (S n3) :: (List.map swap01 (List.map S (n :: xs)))).
        repeat split.
        ** eapply c_trans.
          *** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
          *** eapply c_trans.
             **** eapply c_comm. eapply (c_cut_assoc
                  (rename_process (up (link (future n0) (future n1))) swap01)
                  (rename_process P swap01)
                  (down (rename_process L swap01))
                 ); autorewrite with up_down_rename_rewrites; auto.
                  -- apply nfv_10_swap; apply nfv_lift_n; lia.
                  -- apply nfv_01_swap; intro Hfv.
                     assert (1 ∈ P) as Hfv1P. {
                        simpl in H13. replace 1 with (Nat.pred 2) by auto.
                        eapply link_list_free_vars; eauto.
                        + intros. simpl in H9. destruct H9 as [? | [? | ?]]; try lia.
                          apply List.in_map_iff in H9. destruct H9; lia.
                        + simpl in H5; destruct H5; subst; simpl; auto.
                          right. right.
                          rewrite List.map_map. apply List.in_map_iff. exists 0; auto.
                     }
                     inversion H3; subst. inversion H18; subst.
                     apply ((proj1 free_var_in_ctx) _ _ Hfv) in H20.
                     apply ((proj1 free_var_in_ctx) _ _ Hfv1P) in H21.
                     destruct H20, H21; simpl in *; subst. inversion H16. subst. subst. inversion H21.
             **** eapply c_cut_comm.
        ** destruct (link_future_equiv_link_future _ _ _ (or_intror H15)) as [? [? [? [? | ?]]]]; subst.
           *** destruct n0, n1, n3; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cons_f; try eapply c_refl. simpl.
               assert (forall x, List.In x (List.map S (S (S n3) :: S n :: List.map S xs)) -> x > 0).
               { intros. intros. simpl in H10. destruct H10 as [? | [? | ?]]; try lia.
                 apply List.in_map_iff in H10. destruct H10; lia. }
               pose proof (link_list_rename _ _ _ H10 swap01_is_bijective H11).
               rewrite (List.map_map S Nat.pred _) in H14.
               rewrite List.map_id in H14.
               simpl in H14; auto.
           *** destruct n0, n1, n3; simpl; try congruence.
               unfold relocate. simpl.
               eapply link_cons_f; try eapply c_link. simpl.
               assert (forall x, List.In x (List.map S (S (S n3) :: S n :: List.map S xs)) -> x > 0).
               { intros. intros. simpl in H10. destruct H10 as [? | [? | ?]]; try lia.
                 apply List.in_map_iff in H10. destruct H10; lia. }
               pose proof (link_list_rename _ _ _ H10 swap01_is_bijective H11).
               rewrite (List.map_map S Nat.pred _) in H14.
               rewrite List.map_id in H14.
               simpl in H14; auto.
        ** simpl. right. right. right. destruct n; auto.
           simpl in H5. destruct H5; try congruence. right.
           rewrite List.map_map. apply List.in_map_iff. exists 0; auto.
        ** simpl. repeat rewrite List.length_map.
           simpl in *; lia.
      * eexists; eexists.
        exists ((S n0) :: (S n1) :: (List.map swap01 (List.map S (n :: xs)))).
        repeat split.
        ** eapply c_trans.
          *** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
          *** eapply c_trans.
             **** eapply c_comm. eapply (c_cut_assoc
                  (rename_process (up (link (future n0) (future n1))) swap01)
                  (rename_process P swap01)
                  (down (rename_process (link (future (S n2)) (future (S n3))) swap01))
                 ); autorewrite with up_down_rename_rewrites; auto.
                  -- apply nfv_10_swap; apply nfv_lift_n; lia.
                  -- apply nfv_01_swap; intro Hfv; inversion Hfv; inversion H11; subst; congruence.
             **** eapply c_cut_comm.
        ** destruct n0, n1, n3; try congruence; simpl. unfold relocate; simpl.
           apply link_cons_f.
           assert (forall x, List.In x (List.map S (S n :: List.map S xs)) -> x > 0).
           { intros. intros. simpl in H9. destruct H9 as [? | ?]; try lia.
             apply List.in_map_iff in H9. destruct H9; lia. }
           pose proof (link_list_rename _ _ _ H9 swap01_is_bijective H14).
           rewrite (List.map_map S Nat.pred _) in H10.
           rewrite List.map_id in H10.
           simpl in H10; auto.
        ** simpl. right. right. destruct n; auto. right.
           simpl in H5. destruct H5; try congruence.
           rewrite List.map_map. apply List.in_map_iff. exists 0; auto.
        ** simpl. repeat rewrite List.length_map.
           simpl in *; lia.
Qed.

(* Idea: If zero is in the list, then let the left most ν bubble upwards
         towards the corresponding link until AxCut applies *)
Lemma link_list_with_0_reduces' :
  forall n k,
    k <= n ->
      forall xs Γ P,
        length xs = k -> Γ ⊢ P :# ->
          List.In 0 xs -> link_list xs P -> exists P', P ⊳ P'.
Proof.
  induction n; intros.
  + assert (k = 0) by lia; subst. rewrite List.length_zero_iff_nil in H4; subst. inversion H2.
  + destruct xs. inversion H2.
    destruct xs. { inversion H3; simpl in H6; inversion H6. }
    destruct xs. {
      simpl in H2; destruct H2 as [? | [? | ?]]; subst;
      [eapply link_list_with_0_at_0_reduces in H3 | eapply link_list_with_0_at_1_reduces in H3 | contradiction]; eauto.
    }
    destruct xs. {
      simpl in H2; destruct H2 as [? | [? | [? | ?]]]; subst; try contradiction.
      + eapply link_list_with_0_at_0_reduces; eauto.
      + eapply link_list_with_0_at_1_reduces; eauto.
      + eapply link_list_with_0_at_2_reduces_or_swap in H3; eauto; destruct H3; eauto.
        destruct H0 as [Q [Q' [xs' [? [? [? ?]]]]]].
        assert (length xs' <= n). { simpl in *; lia. }
        assert (exists Γ', Γ' ⊢ Q' :#).
        { apply ((proj1 struct_cong_preserves_typing) _ _ H0 _) in H1. inversion H1; eexists; eauto. }
        destruct H6 as [Γ' ?].
        destruct (IHn _ H5 xs' _ _ eq_refl H6 H3 H2) as [Q'' ?].
        eexists. eapply r_struct.
        * apply H0.
        * eapply r_struct.
          ** eapply c_cut_comm.
          ** eapply r_cong_cut; eauto.
          ** eapply c_cut_comm.
        * apply c_refl.
    }
    simpl in H2. destruct H2 as [? | [? | [? | [? | ?]]]]; subst; try contradiction.
    - eapply link_list_with_0_at_0_reduces; eauto.
    - eapply link_list_with_0_at_1_reduces; eauto.
    - eapply link_list_with_0_at_2_reduces_or_swap in H3; eauto; destruct H3; eauto.
      destruct H0 as [Q [Q' [xs' [? [? [? ?]]]]]].
      assert (length xs' <= n). { simpl in *; lia. }
      assert (exists Γ', Γ' ⊢ Q' :#).
      { apply ((proj1 struct_cong_preserves_typing) _ _ H0 _) in H1. inversion H1; eexists; eauto. }
      destruct H6 as [Γ' ?].
      destruct (IHn _ H5 xs' _ _ eq_refl H6 H3 H2) as [Q'' ?].
      eexists. eapply r_struct.
      * apply H0.
      * eapply r_struct.
        ** eapply c_cut_comm.
        ** eapply r_cong_cut; eauto.
        ** eapply c_cut_comm.
      * apply c_refl.
    - eapply link_list_with_0_at_3_reduces_or_swap in H3; destruct H3; eauto.
      destruct H0 as [Q [Q' [xs' [? [? [? ?]]]]]].
      assert (length xs' <= n). { simpl in *; lia. }
      assert (exists Γ', Γ' ⊢ Q' :#).
      { apply ((proj1 struct_cong_preserves_typing) _ _ H0 _) in H1. inversion H1; eexists; eauto. }
      destruct H6 as [Γ' ?].
      destruct (IHn _ H5 xs' _ _ eq_refl H6 H3 H2) as [Q'' ?].
      eexists. eapply r_struct.
      * apply H0.
      * eapply r_struct.
        ** eapply c_cut_comm.
        ** eapply r_cong_cut; eauto.
        ** eapply c_cut_comm.
      * apply c_refl.
    - destruct n0. eapply link_list_with_0_at_0_reduces; eauto.
      destruct n1. eapply link_list_with_0_at_1_reduces; eauto.
      destruct n2.
      {
        eapply link_list_with_0_at_2_reduces_or_swap in H3; eauto; destruct H3; eauto.
        destruct H0 as [Q [Q' [xs' [? [? [? ?]]]]]].
        assert (length xs' <= n). { simpl in *; lia. }
        assert (exists Γ', Γ' ⊢ Q' :#).
        { apply ((proj1 struct_cong_preserves_typing) _ _ H0 _) in H1. inversion H1; eexists; eauto. }
        destruct H7 as [Γ' ?].
        destruct (IHn _ H6 xs' _ _ eq_refl H7 H4 H3) as [Q'' ?].
        eexists. eapply r_struct.
        * apply H0.
        * eapply r_struct.
          ** eapply c_cut_comm.
          ** eapply r_cong_cut; eauto.
          ** eapply c_cut_comm.
        * apply c_refl.
      }
      destruct n3.
      {
        eapply link_list_with_0_at_3_reduces_or_swap in H3; destruct H3; eauto.
        destruct H0 as [Q [Q' [xs' [? [? [? ?]]]]]].
        assert (length xs' <= n). { simpl in *; lia. }
        assert (exists Γ', Γ' ⊢ Q' :#).
        { apply ((proj1 struct_cong_preserves_typing) _ _ H0 _) in H1. inversion H1; eexists; eauto. }
        destruct H7 as [Γ' ?].
        destruct (IHn _ H6 xs' _ _ eq_refl H7 H4 H3) as [Q'' ?].
        eexists. eapply r_struct.
        * apply H0.
        * eapply r_struct.
          ** eapply c_cut_comm.
          ** eapply r_cong_cut; eauto.
          ** eapply c_cut_comm.
        * apply c_refl.
      }
      eapply link_list_swap_0_1 in H3; eauto.
      * destruct H3 as [Q [Q' [xs' [? [? [? ?]]]]]].
        assert (length xs' <= n). { simpl in *; lia. }
          assert (exists Γ', Γ' ⊢ Q' :#).
          { apply ((proj1 struct_cong_preserves_typing) _ _ H0 _) in H1. inversion H1; eexists; eauto. }
          destruct H7 as [Γ' ?].
          destruct (IHn _ H6 xs' _ _ eq_refl H7 H4 H3) as [Q'' ?].
          eexists. eapply r_struct.
          ** apply H0.
          ** eapply r_struct.
             *** eapply c_cut_comm.
             *** eapply r_cong_cut; eauto.
             *** eapply c_cut_comm.
          ** apply c_refl.
      * destruct xs. inversion H2. simpl; lia.
Qed.

Lemma link_list_with_0_reduces :
  forall xs Γ P,
    Γ ⊢ P :# -> List.In 0 xs -> link_list xs P -> exists P', P ⊳ P'.
Proof.
  intros.
  eapply (link_list_with_0_reduces' (length xs) (length xs)); eauto.
Qed.

Lemma decide_cut_list_link_list :
  forall Γ P, Γ ⊢ P :# -> cut_list P ->
    (exists xs, link_list xs P) \/ (exists P', P ⊳ P').
Proof.
  intros.
  generalize dependent Γ.
  induction H0; intros.
  + destruct L; destruct R;
    try match goal with
    | [ H : no_root_cut (cut ?X ?Y) |- _ ] => unfold no_root_cut in H; specialize H with X Y; congruence
    end;
    inversion H1; subst;
    try ( match goal with [ H : (?A .: ?Γ) ⊢ stop :# |- _ ] => inversion H; ctx_eq_contra end ).
    - apply link_reduces_or_contains_future in H6.
      apply link_reduces_or_contains_future in H7.
      destruct H6 as [[P' ?] | [i1 ?]].
      * right. exists (cut P' (link m1 m2)). apply r_cong_cut; auto.
      * destruct H7 as [[P'' ?] | [i2 ?]].
        ** right. exists (cut (link m m0) P''). eapply r_struct.
           -- apply c_cut_comm.
           -- apply r_cong_cut; eauto.
           -- apply c_cut_comm.
        ** left. destruct H2, H3; subst.
           -- destruct m0, m2; eexists.
              ++ eapply link_cut_ff.
              ++ apply link_cut_nf with (prefix s); [congruence | apply c_refl].
              ++ apply link_cut_fn with (prefix s); [congruence | apply c_refl].
              ++ apply link_cut_nn with (prefix s) (prefix s0);
                  [ congruence | congruence | apply c_refl | apply c_refl ].
           -- destruct m0, m1; eexists.
              ++ eapply link_cut_ff.
              ++ apply link_cut_nf with (prefix s); [congruence | apply c_link].
              ++ apply link_cut_fn with (prefix s); [congruence | apply c_refl].
              ++ apply link_cut_nn with (prefix s) (prefix s0);
                  [ congruence | congruence | apply c_refl | apply c_link ].
           -- destruct m, m2; eexists.
              ++ eapply link_cut_ff.
              ++ apply link_cut_nf with (prefix s); [congruence | apply c_refl].
              ++ apply link_cut_fn with (prefix s); [congruence | apply c_link].
              ++ apply link_cut_nn with (prefix s) (prefix s0);
                  [ congruence | congruence | apply c_link | apply c_refl ].
           -- destruct m, m1; eexists.
              ++ eapply link_cut_ff.
              ++ apply link_cut_nf with (prefix s); [congruence | apply c_link].
              ++ apply link_cut_fn with (prefix s); [congruence | apply c_link].
              ++ apply link_cut_nn with (prefix s) (prefix s0);
                  [ congruence | congruence | apply c_link | apply c_link ].
    - right.
      exists (cut (link m m0) (subst_process R ((prefix s) ⋅ id_subst))).
      eapply r_struct.
      * eapply c_cut_comm.
      * eapply r_cong_cut; econstructor.
      * apply c_cut_comm.
    - right.
      exists (cut (subst_process L ((prefix s) ⋅ id_subst)) (link m m0)).
      apply r_cong_cut; econstructor.
    - right.
      exists (cut (subst_process L ((prefix s) ⋅ id_subst)) (seq R s0)).
      apply r_cong_cut; econstructor.
  + inversion H1; subst.
    destruct (IHcut_list _ H7).
    - destruct L.
      * (* Lemma : well-typed link either reduces or has a future *)
        apply link_reduces_or_contains_future in H6.
        destruct H6 as [[P' ?] | [i ?]].
        ** right. exists (cut P' P). apply r_cong_cut; auto.
        ** destruct H2 as [xs' ?].
           destruct (List.in_dec PeanoNat.Nat.eq_dec 0 xs').
           {  (* 0 in xs', i.e. we can reduce P *)
              destruct (link_list_with_0_reduces _ _ _ H7 i0 H2) as [P' ?].
              right. exists (cut (link m m0) P'). eapply r_struct.
              + eapply c_cut_comm.
              + eapply r_cong_cut; eauto.
              + apply c_cut_comm.
           }
           { (* 0 ∉ xs', we use xs'' = pred xs' *)
             left.
             destruct H3, m0; subst.
             + eexists (i :: n0 :: (List.map pred xs')).
               apply link_cons_f.
               rewrite List.map_map.
               assert ( forall a, List.In a xs' -> (fun x : nat => S (Init.Nat.pred x)) a = id a ).
               { intros. destruct a; auto. congruence. }
               rewrite ((proj2 List.map_ext_in_iff) H3).
               rewrite List.map_id; auto.
             + eexists (i :: (List.map pred xs')).
               apply link_cons_n with (prefix s); try congruence; try apply c_refl.
               rewrite List.map_map.
               assert ( forall a, List.In a xs' -> (fun x : nat => S (Init.Nat.pred x)) a = id a ).
               { intros. destruct a; auto. congruence. }
               rewrite ((proj2 List.map_ext_in_iff) H3).
               rewrite List.map_id; auto.
             + destruct m.
               - eexists (n1 :: n0 :: (List.map pred xs')).
                 apply link_cons_f.
                 rewrite List.map_map.
                 assert ( forall a, List.In a xs' -> (fun x : nat => S (Init.Nat.pred x)) a = id a ).
                 { intros. destruct a; auto. congruence. }
                 rewrite ((proj2 List.map_ext_in_iff) H5).
                 rewrite List.map_id; auto.
               - eexists (n0 :: (List.map pred xs')).
                 apply link_cons_n with (prefix s); try congruence; try apply c_link.
                 rewrite List.map_map.
                 assert ( forall a, List.In a xs' -> (fun x : nat => S (Init.Nat.pred x)) a = id a ).
                 { intros. destruct a; auto. congruence. }
                 rewrite ((proj2 List.map_ext_in_iff) H5).
                 rewrite List.map_id; auto.
             + discriminate.
           }
      * exfalso. unfold no_root_cut in H; try congruence.
      * right. exists (cut (subst_process L ((prefix s) ⋅ id_subst)) P).
        apply r_cong_cut; econstructor.
      * inversion H6; ctx_eq_contra.
    - destruct H2 as [P' ?].
      right. exists (cut L P').
      eapply r_struct.
      * eapply c_cut_comm.
      * eapply r_cong_cut; eauto.
      * apply c_cut_comm.
Qed.

Corollary cut_list_final_or_reduces :
  forall Γ P, Γ ⊢ P :# -> cut_list P -> final P \/ (exists P', P ⊳ P').
Proof.
  intros Γ P Hwt Hct.
  destruct (decide_cut_list_link_list _ _ Hwt Hct).
  + destruct H as [xs H0].
    destruct xs. inversion H0. destruct xs.
    - left. inversion H0; subst; inversion H2.
    - destruct (List.in_dec PeanoNat.Nat.eq_dec 0 (n :: n0 :: xs)).
      * right. apply (link_list_with_0_reduces (n :: n0 :: xs) _ _ Hwt); auto.
      * left. eapply final_list; eauto. apply c_refl.
  + right; auto.
Qed.
