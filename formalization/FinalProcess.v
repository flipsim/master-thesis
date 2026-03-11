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
(* Final Processes                                                            *)
(******************************************************************************)
Inductive link_list : list nat -> process -> Prop :=
  | link_cut_ll : forall i1 i2 M1 M2,
                    link_list [i1; i2] (cut (link (future i1) M1) (link (future i2) M2))
  | link_cut_lr : forall i1 i2 M1 M2,
                    link_list [i1; i2] (cut (link (future i1) M1) (link M2 (future i2)))
  | link_cut_rl : forall i1 i2 M1 M2,
                    link_list [i1; i2] (cut (link M1 (future i1)) (link (future i2) M2))
  | link_cut_rr : forall i1 i2 M1 M2,
                    link_list [i1; i2] (cut (link M1 (future i1)) (link M2 (future i2)))
  | link_cons_l   : forall i M xs P,
                      link_list (List.map S xs) P ->
                      link_list (i :: xs) (cut (link (future i) M) P)
  | link_cons_r   : forall i M xs P,
                      link_list (List.map S xs) P ->
                      link_list (i :: xs) (cut (link M (future i)) P).

(* Inductive link_list : list nat -> process -> Prop :=
  | link_single_l : forall i M, link_list [i] (link (future i) M)
  | link_single_r : forall i M, link_list [i] (link M (future i))
  | link_cons_l   : forall i M xs P,
                      link_list (List.map S xs) P ->
                      link_list (i :: xs) (cut (link (future i) M) P)
  | link_cons_r   : forall i M xs P,
                      link_list (List.map S xs) P ->
                      link_list (i :: xs) (cut (link M (future i)) P). *)

Inductive final : process -> Prop :=
  | final_stop : final stop
  | final_future_l : forall i M, final (link (future i) M)
  | final_future_r : forall i M, final (link M (future i))
  | final_list : forall xs P P',
                  ~ (List.In 0 xs) ->
                  (* (forall x, List.In x xs -> x <> 0) -> *)
                  link_list xs P' ->
                  P ≡ P' ->
                  final P.

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
(* useful lemmas for below
   if x in xs and x > 0 and link_list xs P then pred x free in P
*)
Lemma link_list_with_0_at_0_reduces :
  forall P xs,
    link_list (0 :: xs) P -> exists Q, P ⊳ Q.
Proof.
  intros P xs H. inversion H;
  try match goal with
  | [ H : cut (link (future 0) ?M1) ?P2 = P |- _ ]
      => exists (subst_process P2 ((downM M1) ⋅ id_subst)); econstructor; eauto
  | [ H : cut (link ?M1 (future 0)) ?P2 = P |- _ ]
      => exists (subst_process P2 ((downM M1) ⋅ id_subst));
         econstructor; [ eapply c_cong_cut; [eapply c_link | eapply c_refl] | econstructor | apply c_refl ]
  end.
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
  intros. inversion H0; subst;
  try match goal with
    | [ H : _ ⊢ cut ?P1 (link (future 0) ?M) :# |- _]
        => exists (subst_process P1 ((downM M) ⋅ id_subst));
           eapply r_struct; [ eapply c_cut_comm | econstructor | apply c_refl]
    | [ H : _ ⊢ cut ?P1 (link ?M (future 0)) :# |- _]
        => exists (subst_process P1 ((downM M) ⋅ id_subst));
           eapply r_struct;
           [eapply c_trans; [eapply c_cut_comm | eapply c_cong_cut; [eapply c_link | eapply c_refl]]
                             | econstructor | apply c_refl ]
    end;
  simpl in H4; inversion H4; subst;
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
                         apply ((proj1 free_var_in_ctx) _ _ H1) in HwtP;
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
    end;
  try match goal with
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
                         apply ((proj1 free_var_in_ctx) _ _ H1) in HwtP;
                         destruct HwtM, HwtP; simpl in *; subst;
                         match goal with
                         | [ Hsplitentry : split_entry _ _ _ |- _ ] => inversion Hsplitentry
                         end
                   end
              end
            ]
          | eapply r_cong_cut; eapply r_struct;
            [ eapply c_trans; [ eapply c_cut_comm | eapply c_cong_cut; simpl; apply c_link; eapply c_refl ]
            | simpl; econstructor
            | eapply c_refl ]
          | eapply c_refl
          ]
    end.
Qed.

Lemma link_list_rename :
  forall P xs r,
    (forall x, List.In x xs -> x > 0) ->
    bijective r -> link_list xs P -> link_list (List.map S (List.map r (List.map Nat.pred xs))) (rename_process P r).
Proof.
  intros.
  generalize dependent r.
  induction H1; intros;
  try destruct i1, i2; try (specialize H with 0; simpl in H; exfalso; lia); try (simpl; econstructor).
  + destruct i; try (specialize H with 0; simpl in H; exfalso; lia).
    simpl. econstructor.
    assert (bijective (up_ren r)). { apply shift_preserves_bijection; auto. }
    assert (forall x : nat, List.In x (ListDef.map S xs) -> x > 0).
    { intros. apply List.in_map_iff in H3. destruct H3 as [x0 []]. lia. }
    pose proof (IHlink_list H3 _ H2).
    clear - H H4.
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
  + destruct i; try (specialize H with 0; simpl in H; exfalso; lia).
    simpl. econstructor.
    assert (bijective (up_ren r)). { apply shift_preserves_bijection; auto. }
    assert (forall x : nat, List.In x (ListDef.map S xs) -> x > 0).
    { intros. apply List.in_map_iff in H3. destruct H3 as [x0 []]. lia. }
    pose proof (IHlink_list H3 _ H2).
    clear - H H4.
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
  + simpl in H1. destruct H1; subst.
    - apply fv_cut_l. simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      repeat econstructor.
    - destruct H0; try contradiction; subst.
      apply fv_cut_r; simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      repeat econstructor.
  + simpl in H1. destruct H1; subst.
    - apply fv_cut_l. simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      repeat econstructor.
    - destruct H0; try contradiction; subst.
      apply fv_cut_r; simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      apply fv_link_r; econstructor.
  + simpl in H1. destruct H1; subst.
    - apply fv_cut_l. simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      apply fv_link_r; econstructor.
    - destruct H0; try contradiction; subst.
      apply fv_cut_r; simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      repeat econstructor.
  + simpl in H1. destruct H1; subst.
    - apply fv_cut_l. simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      apply fv_link_r; econstructor.
    - destruct H0; try contradiction; subst.
      apply fv_cut_r; simpl in H; specialize H with x.
      replace (S (Nat.pred x)) with x by lia.
      apply fv_link_r; econstructor.
  + simpl in H1. destruct H1; subst.
    - apply fv_cut_l. specialize H with x.
      simpl in H. replace (S (Nat.pred x)) with x by lia.
      repeat econstructor.
    - apply fv_cut_r. simpl in H. specialize H with x.
      pose proof (H (or_intror H1)).
      replace (S (Nat.pred x)) with x by lia.
      assert (forall x : nat, List.In x (ListDef.map S xs) -> x > 0).
      { intros. apply List.in_map_iff in H3; destruct H3. lia. }
      apply (IHlink_list H3 (S x)).
      apply List.in_map_iff. exists x; auto.
  + simpl in H1. destruct H1; subst.
    - apply fv_cut_l. specialize H with x.
      simpl in H. replace (S (Nat.pred x)) with x by lia.
      apply fv_link_r. econstructor.
    - apply fv_cut_r. simpl in H. specialize H with x.
      pose proof (H (or_intror H1)).
      replace (S (Nat.pred x)) with x by lia.
      assert (forall x : nat, List.In x (ListDef.map S xs) -> x > 0).
      { intros. apply List.in_map_iff in H3; destruct H3. lia. }
      eapply (IHlink_list H3 (S x)).
      apply List.in_map_iff. exists x; auto.
Qed.

Lemma link_list_swap_0_1 :
  forall Γ P n0 n1 xs,
    0 <> n0 ->
    0 <> n1 ->
    Γ ⊢ P :# -> List.In 0 xs -> link_list (n0 :: n1 :: xs) P ->
    exists Q Q' xs', P ≡ (cut Q Q') /\ link_list xs' Q' /\ List.In 0 xs' /\ length xs' <= S (length xs).
Proof.
  intros.
  inversion H3; subst; try now inversion H2.
  + simpl in H7. inversion H7; subst.
    - assert (xs = [0]).
      {
        destruct xs.
        + simpl in H6; congruence.
        + destruct xs.
          - simpl in H6. simpl in H2. destruct H2.
            * subst. auto.
            * contradiction.
          - simpl in H6. inversion H6.
      }
      assert (i2 = 1).
      { rewrite H4 in H6. inversion H6; subst; auto. }
      subst.
      eexists; eexists. exists [S n0; 0].
      repeat split.
      * eapply c_trans.
        ** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
        ** eapply c_trans.
           *** eapply c_comm. eapply (c_cut_assoc
                (rename_process (up (link (future n0) M)) swap01)
                (rename_process (link (future 1) M2) swap01)
                (down (rename_process (link (future (S n1)) M1) swap01))
               ); autorewrite with up_down_rename_rewrites; auto;
                [ apply nfv_10_swap; apply nfv_lift_n; lia
                | apply nfv_01_swap; intro Hfv; inversion H1; subst
                ].
                assert (1 ∈ (link (future 1) M2)) as Hfv1link by repeat econstructor.
                inversion H11; subst. inversion H9; subst.
                apply ((proj1 free_var_in_ctx) _ _ Hfv) in H13.
                apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H14.
                destruct H13, H14; simpl in *; subst. inversion H9. inversion H14.
           *** eapply c_cut_comm.
      * simpl. destruct n0; try congruence. econstructor.
      * simpl. right; left; auto.
      * simpl; lia.
    - assert (xs = [0]).
      {
        destruct xs.
        + simpl in H6; congruence.
        + destruct xs.
          - simpl in H6. simpl in H2. destruct H2.
            * subst. auto.
            * contradiction.
          - simpl in H6. inversion H6.
      }
      assert (i2 = 1).
      { rewrite H4 in H6. inversion H6; subst; auto. }
      subst.
      eexists; eexists. exists [S n0; 0].
      repeat split.
      * eapply c_trans.
        ** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
        ** eapply c_trans.
           *** eapply c_comm. eapply (c_cut_assoc
                (rename_process (up (link (future n0) M)) swap01)
                (rename_process (link M2 (future 1)) swap01)
                (down (rename_process (link (future (S n1)) M1) swap01))
               ); autorewrite with up_down_rename_rewrites; auto;
                [ apply nfv_10_swap; apply nfv_lift_n; lia
                | apply nfv_01_swap; intro Hfv; inversion H1; subst
                ].
                assert (1 ∈ (link M2 (future 1))) as Hfv1link by repeat econstructor.
                inversion H11; subst. inversion H9; subst.
                apply ((proj1 free_var_in_ctx) _ _ Hfv) in H13.
                apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H14.
                destruct H13, H14; simpl in *; subst. inversion H9. inversion H14.
           *** eapply c_cut_comm.
      * simpl. destruct n0; try congruence. econstructor.
      * simpl. right; left; auto.
      * simpl; lia.
    - assert (xs = [0]).
      {
        destruct xs.
        + simpl in H6; congruence.
        + destruct xs.
          - simpl in H6. simpl in H2. destruct H2.
            * subst. auto.
            * contradiction.
          - simpl in H6. inversion H6.
      }
      assert (i2 = 1).
      { rewrite H4 in H6. inversion H6; subst; auto. }
      subst.
      eexists; eexists. exists [S n0; 0].
      repeat split.
      * eapply c_trans.
        ** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
        ** eapply c_trans.
           *** eapply c_comm. eapply (c_cut_assoc
                (rename_process (up (link (future n0) M)) swap01)
                (rename_process (link (future 1) M2) swap01)
                (down (rename_process (link M1 (future (S n1))) swap01))
               ); autorewrite with up_down_rename_rewrites; auto;
                [ apply nfv_10_swap; apply nfv_lift_n; lia
                | apply nfv_01_swap; intro Hfv; inversion H1; subst
                ].
                assert (1 ∈ (link (future 1) M2)) as Hfv1link by repeat econstructor.
                inversion H11; subst. inversion H9; subst.
                apply ((proj1 free_var_in_ctx) _ _ Hfv) in H13.
                apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H14.
                destruct H13, H14; simpl in *; subst. inversion H9. inversion H14.
           *** eapply c_cut_comm.
      * simpl. destruct n0; try congruence. econstructor.
      * simpl. right; left; auto.
      * simpl; lia.
    - assert (xs = [0]).
      {
        destruct xs.
        + simpl in H6; congruence.
        + destruct xs.
          - simpl in H6. simpl in H2. destruct H2.
            * subst. auto.
            * contradiction.
          - simpl in H6. inversion H6.
      }
      assert (i2 = 1).
      { rewrite H4 in H6. inversion H6; subst; auto. }
      subst.
      eexists; eexists. exists [S n0; 0].
      repeat split.
      * eapply c_trans.
        ** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
        ** eapply c_trans.
           *** eapply c_comm. eapply (c_cut_assoc
                (rename_process (up (link (future n0) M)) swap01)
                (rename_process (link M2 (future 1)) swap01)
                (down (rename_process (link M1 (future (S n1))) swap01))
               ); autorewrite with up_down_rename_rewrites; auto;
                [ apply nfv_10_swap; apply nfv_lift_n; lia
                | apply nfv_01_swap; intro Hfv; inversion H1; subst
                ].
                assert (1 ∈ (link M2 (future 1))) as Hfv1link by repeat econstructor.
                inversion H11; subst. inversion H9; subst.
                apply ((proj1 free_var_in_ctx) _ _ Hfv) in H13.
                apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H14.
                destruct H13, H14; simpl in *; subst. inversion H9. inversion H14.
           *** eapply c_cut_comm.
      * simpl. destruct n0; try congruence. econstructor.
      * simpl. right; left; auto.
      * simpl; lia.
    - assert (forall x, List.In x (List.map S (List.map S xs)) -> x > 0).
      { intros. apply List.in_map_iff in H4; destruct H4. lia. }
      pose proof (link_list_rename _ _ _ H4 swap01_is_bijective H8).
      rewrite (List.map_map S Nat.pred _) in H5.
      simpl in H5.
      rewrite List.map_id in H5.
      eexists; eexists.
      exists ((S n0) :: (List.map swap01 (List.map S xs))).
      repeat split.
      * eapply c_trans.
        ** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
        ** eapply c_trans.
           *** eapply c_comm. eapply (c_cut_assoc
                (rename_process (up (link (future n0) M)) swap01)
                (rename_process P swap01)
                (down (rename_process (link (future (S n1)) M0) swap01))
               ); autorewrite with up_down_rename_rewrites; auto;
                [ apply nfv_10_swap; apply nfv_lift_n; lia
                | apply nfv_01_swap; intro Hfv; inversion H1; subst
                ].
                assert (1 ∈ P).
                {
                  replace 1 with (Nat.pred 2) by auto.
                  assert (List.In 2 (List.map S (List.map S xs))).
                  { rewrite List.map_map. apply List.in_map_iff. exists 0; auto. }
                  apply (link_list_free_vars _ _ H4 H8 2 H6).
                }
                inversion H13; subst. inversion H14; subst.
                destruct ((proj1 free_vars_decidable) (link (future (S n1)) M0) 1); auto.
                apply ((proj1 free_var_in_ctx) _ _ Hfv) in H16.
                apply ((proj1 free_var_in_ctx) _ _ H6) in H17.
                destruct H16, H17; simpl in *; subst. inversion H14. inversion H18.
           *** eapply c_cut_comm.
      * destruct n0; try congruence. simpl. unfold relocate. simpl.
        econstructor; eauto.
      * simpl. right.
        rewrite List.map_map.
        apply List.in_map_iff. exists 0; split; auto.
      * simpl. repeat rewrite List.length_map. lia.
    - assert (forall x, List.In x (List.map S (List.map S xs)) -> x > 0).
      { intros. apply List.in_map_iff in H4; destruct H4. lia. }
      pose proof (link_list_rename _ _ _ H4 swap01_is_bijective H8).
      rewrite (List.map_map S Nat.pred _) in H5.
      simpl in H5.
      rewrite List.map_id in H5.
      eexists; eexists.
      exists ((S n0) :: (List.map swap01 (List.map S xs))).
      repeat split.
      * eapply c_trans.
        ** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
        ** eapply c_trans.
           *** eapply c_comm. eapply (c_cut_assoc
                (rename_process (up (link (future n0) M)) swap01)
                (rename_process P swap01)
                (down (rename_process (link M0 (future (S n1))) swap01))
               ); autorewrite with up_down_rename_rewrites; auto;
                [ apply nfv_10_swap; apply nfv_lift_n; lia
                | apply nfv_01_swap; intro Hfv; inversion H1; subst
                ].
                assert (1 ∈ P).
                {
                  replace 1 with (Nat.pred 2) by auto.
                  assert (List.In 2 (List.map S (List.map S xs))).
                  { rewrite List.map_map. apply List.in_map_iff. exists 0; auto. }
                  apply (link_list_free_vars _ _ H4 H8 2 H6).
                }
                inversion H13; subst. inversion H14; subst.
                destruct ((proj1 free_vars_decidable) (link M0 (future (S n1))) 1); auto.
                apply ((proj1 free_var_in_ctx) _ _ Hfv) in H16.
                apply ((proj1 free_var_in_ctx) _ _ H6) in H17.
                destruct H16, H17; simpl in *; subst. inversion H14. inversion H18.
           *** eapply c_cut_comm.
      * destruct n0; try congruence. simpl. unfold relocate. simpl.
        econstructor; eauto.
      * simpl. right.
        rewrite List.map_map.
        apply List.in_map_iff. exists 0; split; auto.
      * simpl. repeat rewrite List.length_map. lia.
  + simpl in H7. inversion H7; subst.
    - assert (xs = [0]).
      {
        destruct xs.
        + simpl in H6; congruence.
        + destruct xs.
          - simpl in H6. simpl in H2. destruct H2.
            * subst. auto.
            * contradiction.
          - simpl in H6. inversion H6.
      }
      assert (i2 = 1).
      { rewrite H4 in H6. inversion H6; subst; auto. }
      subst.
      eexists; eexists. exists [S n0; 0].
      repeat split.
      * eapply c_trans.
        ** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
        ** eapply c_trans.
           *** eapply c_comm. eapply (c_cut_assoc
                (rename_process (up (link M (future n0))) swap01)
                (rename_process (link (future 1) M2) swap01)
                (down (rename_process (link (future (S n1)) M1) swap01))
               ); autorewrite with up_down_rename_rewrites; auto;
                [ apply nfv_10_swap; apply nfv_lift_n; lia
                | apply nfv_01_swap; intro Hfv; inversion H1; subst
                ].
                assert (1 ∈ (link (future 1) M2)) as Hfv1link by repeat econstructor.
                inversion H11; subst. inversion H9; subst.
                apply ((proj1 free_var_in_ctx) _ _ Hfv) in H13.
                apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H14.
                destruct H13, H14; simpl in *; subst. inversion H9. inversion H14.
           *** eapply c_cut_comm.
      * simpl. destruct n0; try congruence. econstructor.
      * simpl. right; left; auto.
      * simpl; lia.
    - assert (xs = [0]).
      {
        destruct xs.
        + simpl in H6; congruence.
        + destruct xs.
          - simpl in H6. simpl in H2. destruct H2.
            * subst. auto.
            * contradiction.
          - simpl in H6. inversion H6.
      }
      assert (i2 = 1).
      { rewrite H4 in H6. inversion H6; subst; auto. }
      subst.
      eexists; eexists. exists [S n0; 0].
      repeat split.
      * eapply c_trans.
        ** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
        ** eapply c_trans.
           *** eapply c_comm. eapply (c_cut_assoc
                (rename_process (up (link M (future n0))) swap01)
                (rename_process (link M2 (future 1)) swap01)
                (down (rename_process (link (future (S n1)) M1) swap01))
               ); autorewrite with up_down_rename_rewrites; auto;
                [ apply nfv_10_swap; apply nfv_lift_n; lia
                | apply nfv_01_swap; intro Hfv; inversion H1; subst
                ].
                assert (1 ∈ (link M2 (future 1))) as Hfv1link by repeat econstructor.
                inversion H11; subst. inversion H9; subst.
                apply ((proj1 free_var_in_ctx) _ _ Hfv) in H13.
                apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H14.
                destruct H13, H14; simpl in *; subst. inversion H9. inversion H14.
           *** eapply c_cut_comm.
      * simpl. destruct n0; try congruence. econstructor.
      * simpl. right; left; auto.
      * simpl; lia.
    - assert (xs = [0]).
      {
        destruct xs.
        + simpl in H6; congruence.
        + destruct xs.
          - simpl in H6. simpl in H2. destruct H2.
            * subst. auto.
            * contradiction.
          - simpl in H6. inversion H6.
      }
      assert (i2 = 1).
      { rewrite H4 in H6. inversion H6; subst; auto. }
      subst.
      eexists; eexists. exists [S n0; 0].
      repeat split.
      * eapply c_trans.
        ** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
        ** eapply c_trans.
           *** eapply c_comm. eapply (c_cut_assoc
                (rename_process (up (link M (future n0))) swap01)
                (rename_process (link (future 1) M2) swap01)
                (down (rename_process (link M1 (future (S n1))) swap01))
               ); autorewrite with up_down_rename_rewrites; auto;
                [ apply nfv_10_swap; apply nfv_lift_n; lia
                | apply nfv_01_swap; intro Hfv; inversion H1; subst
                ].
                assert (1 ∈ (link (future 1) M2)) as Hfv1link by repeat econstructor.
                inversion H11; subst. inversion H9; subst.
                apply ((proj1 free_var_in_ctx) _ _ Hfv) in H13.
                apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H14.
                destruct H13, H14; simpl in *; subst. inversion H9. inversion H14.
           *** eapply c_cut_comm.
      * simpl. destruct n0; try congruence. econstructor.
      * simpl. right; left; auto.
      * simpl; lia.
    - assert (xs = [0]).
      {
        destruct xs.
        + simpl in H6; congruence.
        + destruct xs.
          - simpl in H6. simpl in H2. destruct H2.
            * subst. auto.
            * contradiction.
          - simpl in H6. inversion H6.
      }
      assert (i2 = 1).
      { rewrite H4 in H6. inversion H6; subst; auto. }
      subst.
      eexists; eexists. exists [S n0; 0].
      repeat split.
      * eapply c_trans.
        ** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
        ** eapply c_trans.
           *** eapply c_comm. eapply (c_cut_assoc
                (rename_process (up (link M (future n0))) swap01)
                (rename_process (link M2 (future 1)) swap01)
                (down (rename_process (link M1 (future (S n1))) swap01))
               ); autorewrite with up_down_rename_rewrites; auto;
                [ apply nfv_10_swap; apply nfv_lift_n; lia
                | apply nfv_01_swap; intro Hfv; inversion H1; subst
                ].
                assert (1 ∈ (link M2 (future 1))) as Hfv1link by repeat econstructor.
                inversion H11; subst. inversion H9; subst.
                apply ((proj1 free_var_in_ctx) _ _ Hfv) in H13.
                apply ((proj1 free_var_in_ctx) _ _ Hfv1link) in H14.
                destruct H13, H14; simpl in *; subst. inversion H9. inversion H14.
           *** eapply c_cut_comm.
      * simpl. destruct n0; try congruence. econstructor.
      * simpl. right; left; auto.
      * simpl; lia.
    - assert (forall x, List.In x (List.map S (List.map S xs)) -> x > 0).
      { intros. apply List.in_map_iff in H4; destruct H4. lia. }
      pose proof (link_list_rename _ _ _ H4 swap01_is_bijective H8).
      rewrite (List.map_map S Nat.pred _) in H5.
      simpl in H5.
      rewrite List.map_id in H5.
      eexists; eexists.
      exists ((S n0) :: (List.map swap01 (List.map S xs))).
      repeat split.
      * eapply c_trans.
        ** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
        ** eapply c_trans.
           *** eapply c_comm. eapply (c_cut_assoc
                (rename_process (up (link M (future n0))) swap01)
                (rename_process P swap01)
                (down (rename_process (link (future (S n1)) M0) swap01))
               ); autorewrite with up_down_rename_rewrites; auto;
                [ apply nfv_10_swap; apply nfv_lift_n; lia
                | apply nfv_01_swap; intro Hfv; inversion H1; subst
                ].
                assert (1 ∈ P).
                {
                  replace 1 with (Nat.pred 2) by auto.
                  assert (List.In 2 (List.map S (List.map S xs))).
                  { rewrite List.map_map. apply List.in_map_iff. exists 0; auto. }
                  apply (link_list_free_vars _ _ H4 H8 2 H6).
                }
                inversion H13; subst. inversion H14; subst.
                destruct ((proj1 free_vars_decidable) (link (future (S n1)) M0) 1); auto.
                apply ((proj1 free_var_in_ctx) _ _ Hfv) in H16.
                apply ((proj1 free_var_in_ctx) _ _ H6) in H17.
                destruct H16, H17; simpl in *; subst. inversion H14. inversion H18.
           *** eapply c_cut_comm.
      * destruct n0; try congruence. simpl. unfold relocate. simpl.
        econstructor; eauto.
      * simpl. right.
        rewrite List.map_map.
        apply List.in_map_iff. exists 0; split; auto.
      * simpl. repeat rewrite List.length_map. lia.
    - assert (forall x, List.In x (List.map S (List.map S xs)) -> x > 0).
      { intros. apply List.in_map_iff in H4; destruct H4. lia. }
      pose proof (link_list_rename _ _ _ H4 swap01_is_bijective H8).
      rewrite (List.map_map S Nat.pred _) in H5.
      simpl in H5.
      rewrite List.map_id in H5.
      eexists; eexists.
      exists ((S n0) :: (List.map swap01 (List.map S xs))).
      repeat split.
      * eapply c_trans.
        ** eapply c_cong_cut; [ eapply c_refl | eapply c_cut_comm ].
        ** eapply c_trans.
           *** eapply c_comm. eapply (c_cut_assoc
                (rename_process (up (link M (future n0))) swap01)
                (rename_process P swap01)
                (down (rename_process (link M0 (future (S n1))) swap01))
               ); autorewrite with up_down_rename_rewrites; auto;
                [ apply nfv_10_swap; apply nfv_lift_n; lia
                | apply nfv_01_swap; intro Hfv; inversion H1; subst
                ].
                assert (1 ∈ P).
                {
                  replace 1 with (Nat.pred 2) by auto.
                  assert (List.In 2 (List.map S (List.map S xs))).
                  { rewrite List.map_map. apply List.in_map_iff. exists 0; auto. }
                  apply (link_list_free_vars _ _ H4 H8 2 H6).
                }
                inversion H13; subst. inversion H14; subst.
                destruct ((proj1 free_vars_decidable) (link M0 (future (S n1))) 1); auto.
                apply ((proj1 free_var_in_ctx) _ _ Hfv) in H16.
                apply ((proj1 free_var_in_ctx) _ _ H6) in H17.
                destruct H16, H17; simpl in *; subst. inversion H14. inversion H18.
           *** eapply c_cut_comm.
      * destruct n0; try congruence. simpl. unfold relocate. simpl.
        econstructor; eauto.
      * simpl. right.
        rewrite List.map_map.
        apply List.in_map_iff. exists 0; split; auto.
      * simpl. repeat rewrite List.length_map. lia.
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
  + destruct xs. inversion H3.
    destruct xs.
    - inversion H3; simpl in H7; inversion H7.
    - destruct (PeanoNat.Nat.eq_dec 0 n0).
      { eapply link_list_with_0_at_0_reduces; rewrite <- e in H3; eauto. }
      {
        destruct (PeanoNat.Nat.eq_dec 0 n1).
        + (* n0 <> 0 /\ n1 = 0 *)
          eapply link_list_with_0_at_1_reduces; eauto. rewrite <- e in H3; eauto.
        + (* n0 <> 0 /\ n1 <> 0 *)
          assert (List.In 0 xs). { simpl in H2; destruct H2 as [|[|]]; congruence. }
          destruct (link_list_swap_0_1 _ _ _ _ _ n2 n3 H1 H4 H3) as [Q' [Q'' [xs' [? [? [? ?]]]]]].
          assert (length xs' <= n). { simpl in *; lia. }
          assert (exists Γ', Γ' ⊢ Q'' :#).
          { apply ((proj1 struct_cong_preserves_typing) _ _ H5 _) in H1. inversion H1; eexists; eauto. }
          destruct H10 as [Γ' ?].
          destruct (IHn _ H9 xs' _ _ eq_refl H10 H7 H6) as [Q''' ?].
          eexists. eapply r_struct.
          - apply H5.
          - eapply r_struct.
            * eapply c_cut_comm.
            * eapply r_cong_cut; eauto.
            * eapply c_cut_comm.
          - apply c_refl.
      }
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
        ** left. destruct H2; destruct H3; subst; exists [i1; i2]; econstructor.
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
             left. exists (i :: (List.map pred xs')).
             destruct H3; subst.
             + apply link_cons_l.
               rewrite List.map_map.
               assert ( forall a, List.In a xs' -> (fun x : nat => S (Init.Nat.pred x)) a = id a ).
               { intros. destruct a; auto. congruence. }
               rewrite ((proj2 List.map_ext_in_iff) H3).
               rewrite List.map_id; auto.
             + apply link_cons_r.
               rewrite List.map_map.
               assert ( forall a, List.In a xs' -> (fun x : nat => S (Init.Nat.pred x)) a = id a ).
               { intros. destruct a; auto. congruence. }
               rewrite ((proj2 List.map_ext_in_iff) H3).
               rewrite List.map_id; auto.
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
    - left. inversion H0; subst; inversion H3.
    - destruct (List.in_dec PeanoNat.Nat.eq_dec 0 (n :: n0 :: xs)).
      * right. apply (link_list_with_0_reduces (n :: n0 :: xs) _ _ Hwt); auto.
      * left. eapply final_list; eauto. apply c_refl.
  + right; auto.
Qed.

(******************************************************************************)
(* Properties about Irreducible Processes                                     *)
(******************************************************************************)
(* 
Inductive struct_cong_d : nat -> process -> process -> Prop :=
  (* axioms for equivalence of processes *)
  | c_link_d : forall ml mr,
              struct_cong_d 0 (link ml mr) (link mr ml)
  | c_cut_comm_d : forall P Q,
                  struct_cong_d 0 (cut P Q) (cut Q P)
  | c_cut_assoc_d : forall P Q R P' Q' R',
                    ~ (1 ∈ P) /\ ~ (1 ∈ R') -> (* these premises guarantee that the typing judgements have the proper form *)
                    P' = down (rename_process P swap01) ->
                    Q' = rename_process Q swap01 ->
                    R' = rename_process (up R) swap01 ->
                    struct_cong_d 0 (cut (cut P Q) R) (cut P' (cut Q' R'))

  (* rules to make the relation an equivalence *)
  | c_refl_d : forall P, struct_cong_d 0 P P
  | c_comm_d : forall n P Q, struct_cong_d n P Q -> struct_cong_d (S n) Q P
  | c_trans_d : forall n1 n2 P Q R,
                struct_cong_d n1 P Q ->
                struct_cong_d n2 Q R ->
                struct_cong_d (S (Nat.max n1 n2)) P R

  (* rules to make the relation a congruence *)
  | c_cong_link_d : forall n1 m1 m1' n2 m2 m2',
                    struct_congM_d n1 m1 m1' ->
                    struct_congM_d n2 m2 m2' ->
                    struct_cong_d (S (Nat.max n1 n2)) (link m1 m2) (link m1' m2')
  | c_cong_cut_d : forall n1 P P' n2 Q Q',
                  struct_cong_d n1 P P' ->
                  struct_cong_d n2 Q Q' ->
                  struct_cong_d (S (Nat.max n1 n2)) (cut P Q) (cut P' Q')
  | c_cong_seq_d : forall n1 P P' n2 s s',
                  struct_cong_d n1 P P' ->
                  struct_congS_d n2 s s' ->
                  struct_cong_d (S (Nat.max n1 n2)) (seq P s) (seq P' s')

with struct_congM_d : nat -> message -> message -> Prop :=
  | c_cong_fut_d : forall n, struct_congM_d 0 (future n) (future n)
  | c_cong_prefix_d : forall n s s', struct_congS_d n s s' -> struct_congM_d (S n) (prefix s) (prefix s')

with struct_congS_d : nat -> statement -> statement -> Prop :=
  | c_cong_choose_l_d : forall n P P',
                        struct_cong_d n P P' ->
                        struct_congS_d (S n) (choose_left P) (choose_left P')
  | c_cong_choose_r_d : forall n P P',
                        struct_cong_d n P P' ->
                        struct_congS_d (S n) (choose_right P) (choose_right P')
  | c_cong_choice_d : forall n1 P P' n2 Q Q',
                      struct_cong_d n1 P P' ->
                      struct_cong_d n2 Q Q' ->
                      struct_congS_d (S (Nat.max n1 n2)) (offer_choice P Q) (offer_choice P' Q')
  | c_cong_send_d : forall n1 P P' n2 Q Q',
                    struct_cong_d n1 P P' ->
                    struct_cong_d n2 Q Q' ->
                    struct_congS_d (S (Nat.max n1 n2)) (send P Q) (send P' Q')
  | c_cong_receive_d : forall n P P', struct_cong_d n P P' -> struct_congS_d (S n) (receive P) (receive P')
  | c_cong_close_d : struct_congS_d 0 close close
  | c_cong_wait_d : forall n P P', struct_cong_d n P P' -> struct_congS_d (S n) (wait P) (wait P').

Scheme struct_congP_depth_ind := Induction for struct_cong_d Sort Prop
  with struct_congM_depth_ind := Induction for struct_congM_d Sort Prop
  with struct_congS_depth_ind := Induction for struct_congS_d Sort Prop.
Combined Scheme struct_cong_depth_ind from struct_congP_depth_ind, struct_congM_depth_ind, struct_congS_depth_ind.

Lemma struct_cong_d_from_struct_cong :
  (forall P P', P ≡ P' -> exists k, struct_cong_d k P P') /\
  (forall M M', M !≡ M' -> exists k, struct_congM_d k M M') /\
  (forall s s', s $≡ s' -> exists k, struct_congS_d k s s').
Proof.
  apply struct_cong_ind; intros;
    try (now (exists 0; econstructor; eauto));
    try (now (destruct H; exists (S x); econstructor; eauto)).
  + destruct H; destruct H0. exists (S (Nat.max x x0)).
    eapply c_trans_d; eauto.
  + destruct H; destruct H0. exists (S (Nat.max x x0)).
    eapply c_cong_link_d; eauto.
  + destruct H; destruct H0. exists (S (Nat.max x x0)).
    eapply c_cong_cut_d; eauto.
  + destruct H; destruct H0. exists (S (Nat.max x x0)).
    eapply c_cong_seq_d; eauto.
  + destruct H; destruct H0. exists (S (Nat.max x x0)).
    eapply c_cong_choice_d; eauto.
  + destruct H; destruct H0. exists (S (Nat.max x x0)).
    eapply c_cong_send_d; eauto.
Qed.

Definition irreducible P := forall Q, ~ (P ⊳ Q).

Lemma stop_equiv_stop_d :
  forall P n, (forall k, k <= n -> struct_cong_d k stop P \/ struct_cong_d k P stop -> P = stop).
Proof.
  intros.
  generalize dependent k.
  generalize dependent P.
  induction n; intros.
  + inversion H; subst. destruct H0; inversion H0; auto.
  + destruct H0.
    - inversion H0; subst; auto.
      * assert (n0 <= n) by lia.
        apply (IHn _ _ H2).
        right; auto.
      * assert (Q = stop).
        {
          assert (n1 <= n) by lia.
          apply (IHn _ _ H3).
          left; auto.
        }
        subst.
        assert (n2 <= n) by lia.
        apply (IHn _ _ H3).
        left; auto.
    - inversion H0; subst; auto.
      * assert (n0 <= n) by lia.
        apply (IHn _ _ H2).
        left; auto.
      * assert (Q = stop).
        {
          assert (n2 <= n) by lia.
          apply (IHn _ _ H3).
          right; auto.
        }
        subst.
        assert (n1 <= n) by lia.
        apply (IHn _ _ H3).
        right; auto.
Qed.

Lemma stop_equiv_stop : forall P, stop ≡ P -> P = stop.
Proof.
  intros. apply struct_cong_d_from_struct_cong in H.
  destruct H.
  apply (stop_equiv_stop_d P x x (Nat.le_refl x)); left; auto.
Qed.

Lemma stop_irreducible : forall P, P = stop -> irreducible P.
Proof.
  intros P Hstop Q Hred.
  induction Hred; try discriminate; subst.
  apply IHHred.
  apply stop_equiv_stop; auto.
Qed.

Lemma link_future_equiv_link_future :
  forall i M P n,
    struct_cong_d n (link (future i) M) P \/ struct_cong_d n P (link (future i) M) ->
    exists M' n', struct_congM_d n' M' M /\ (P = (link (future i) M') \/ P = (link M' (future i))).
Proof.
  intros.
  generalize dependent P.
  generalize dependent M.
  induction n; intros.
  + destruct H.
    - inversion H; subst.
      * exists M. admit.
      * exists M. admit.
    - inversion H; subst.
      * admit.
      * admit.
  + destruct H.
    - inversion H; subst.
Admitted.


Lemma link_future_irreducible :
  forall i M P,
    P ≡ (link (future i) M) ->
    irreducible P.
Proof.
Admitted.

Lemma ax_cut_inversion_not_0 :
  forall M P Q i,
    i <> 0 ->
    cut (link (future i) M) P ⊳ Q ->
    exists P', P ⊳ P'.
Proof.
Admitted.


Lemma link_chain_irreducible :
  forall P xs,
    (forall x, List.In x xs -> x <> 0) ->
    link_chain xs P ->
    irreducible P.
Proof.
  intros.
  intros Q Hred.
  induction H0.
  + apply (stop_irreducible stop eq_refl Q); auto.
  + assert (i <> 0). { specialize H with i; simpl in H; apply H; auto. }
    inversion Hred; subst.
    admit.
  + admit.
Admitted. *)

(* argue as follows:
   use link_tree (similar to link_list but all future of links are free by construction)
   show that link_treenes is preserved under struct cong
   then by induction on depth of red relation, show that every link_tree is irred
   every link_list is a special case of a link_tree, thus irreducbile
*)
(* Lemma final_iff_irreducible :
  forall Γ P, Γ ⊢ P :# -> (final P <-> irreducible P).
Proof.
  intros; split.
  + intro Hfinal. destruct Hfinal as [xs P P' Hnzero Hchain Hequiv].
    induction Hchain.
    - apply stop_irreducible.
      apply c_comm in Hequiv.
      apply stop_equiv_stop; auto.
    - admit.
    - admit.
  + intro Hirred. *)
