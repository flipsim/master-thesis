From FD Require Import Syntax.
From FD Require Import Types.
From FD Require Import Contexts.
From FD Require Import Typing.
From FD Require Import Renaming.

From Stdlib Require Import List.
Open Scope list_scope.
From Stdlib Require Import Lia.

(******************************************************************************)
(* Substitution Lists                                                         *)
(******************************************************************************)
Definition subst_list := list message.

(* samples the first n values of σ *)
Fixpoint subst_list_from_subst' (σ : substitution) (n k : nat) : subst_list :=
  match n with
  | O    => nil
  | S n' => (σ k) :: subst_list_from_subst' σ n' (S k)
  end.

Definition subst_list_from_subst (σ : substitution) (n : nat) : subst_list :=
  subst_list_from_subst' σ n 0.

Fixpoint generate_id_list' (n k : nat) : subst_list :=
  match n with
  | O    => nil
  | S n' => future k :: (generate_id_list' n' (S k))
  end.

Definition generate_id_list (n : nat) : subst_list := generate_id_list' n 0.

Lemma id_list_from_id_subst' :
  forall n k, subst_list_from_subst' id_subst n k = generate_id_list' n k.
Proof.
  induction n; intros; auto.
  unfold subst_list_from_subst, generate_id_list;
  unfold id_subst; simpl. f_equal.
  fold id_subst. apply IHn.
Qed.

Corollary id_list_from_id_subst :
  forall n, subst_list_from_subst id_subst n = generate_id_list n.
Proof.
  intro n. apply (id_list_from_id_subst' n 0).
Qed.

(******************************************************************************)
(* Typing for Substitutions                                                   *)
(******************************************************************************)
Inductive well_typed_subst : ctx type -> subst_list -> ctx type -> Prop :=
  | subst_ctx_nil : forall Γ, ctx_eq Γ empty_ctx ->
      well_typed_subst nil nil Γ
  | subst_ctx_cons_some :
      forall A Γ M σ Δ_M Δ_σ Δ,
        Δ_M ⊢ M :! A ->
        well_typed_subst Γ σ Δ_σ ->
        Δ ≜ Δ_M ∘ Δ_σ ->
        well_typed_subst (Some A :: Γ) (M :: σ) Δ
  | subst_ctx_cons_none :
      forall Γ t σ Δ,
        well_typed_subst Γ σ Δ ->
        well_typed_subst (None :: Γ) (t :: σ) Δ.

(******************************************************************************)
(* Properties of Substitutions and Substitution Lists                         *)
(******************************************************************************)
Lemma subst_list_from_id_wellty' :
  forall Γ k l,
    k <= length Γ ->
    well_typed_subst (ListDef.firstn k Γ)
                     (generate_id_list' k l)
                     (repeat None l ++ ListDef.firstn k Γ).
Proof.
  intros.
  generalize dependent Γ.
  generalize dependent l.
  induction k; intros.
  + simpl. econstructor.
    apply ctx_lookup_eq_empty. intro n.
    rewrite app_nil_r.
    apply ctx_lookup_repeat_none.
  + destruct Γ.
    - inversion H.
    - simpl.
      destruct o eqn:E.
      * econstructor.
        ** assert ( (repeat None l) ++ (t .: repeat None k) ⊢ future l :! t ).
           {
             econstructor. intros n.
             destruct (PeanoNat.Nat.eq_dec l n).
             + subst. rewrite ctx_lookup_after_insert.
               rewrite ctx_lookup_app_minus; rewrite repeat_length; try lia.
               rewrite PeanoNat.Nat.sub_diag. reflexivity.
             + rewrite ctx_lookup_singleton_neq; auto.
               destruct (Compare_dec.lt_dec n l).
               - rewrite ctx_lookup_app.
                 * apply ctx_lookup_repeat_none.
                 * rewrite repeat_length. auto.
               - assert (n >= l) by lia.
                 rewrite ctx_lookup_app_minus; rewrite repeat_length; try lia.
                 destruct (n - l) eqn:Enl.
                 * exfalso. assert (0 = 1) by lia; congruence.
                 * simpl. apply ctx_lookup_repeat_none. 
           }
           eassumption.
        ** eapply (IHk (S l)). simpl in H. lia.
        ** replace (repeat None (S l)) with (repeat (@None type) l ++ (None :: nil)).
           -- rewrite <- app_assoc.
              eapply ctx_split_distribution.
              --- induction l; simpl; econstructor; auto; econstructor.
              --- simpl; repeat try econstructor.
                  apply ctx_split_empty_refl.
                  *** apply ctx_lookup_eq_empty. intro n. apply ctx_lookup_repeat_none.
                  *** simpl in H.
                      rewrite repeat_length.
                      rewrite firstn_length_le; lia.
           -- replace ((@None type) :: nil) with (repeat (@None type) 1) by reflexivity.
              replace (S l) with (l + 1) by lia.
              rewrite repeat_app. reflexivity.
      * econstructor.
        replace (None :: firstn k Γ) with ((cons None nil) ++ firstn k Γ) by reflexivity.
        assert (repeat (@None type) l ++ None :: nil = repeat None (S l)).
        {
          replace (None :: nil) with (repeat (@None type) 1) by auto.
          replace (S l) with (l + 1) by lia.
          rewrite repeat_app; reflexivity.
        }
        rewrite app_assoc.
        rewrite H0.
        apply IHk. simpl in H. lia.
Qed.

Lemma subst_list_from_id_wellty :
  forall Γ,
    well_typed_subst Γ (subst_list_from_subst id_subst (length Γ)) Γ.
Proof.
  intros.
  rewrite id_list_from_id_subst.
  pose proof (subst_list_from_id_wellty' Γ (length Γ) 0 (PeanoNat.Nat.le_refl (length Γ))).
  simpl in H.
  rewrite firstn_all in H.
  assumption.
Qed.

Lemma subst_list_id_scons :
  forall M k l,
    subst_list_from_subst' (M ⋅ id_subst) k (S l)
      = subst_list_from_subst' id_subst k l.
Proof.
  intros.
  generalize dependent l.
  induction k; intros; rewrite id_list_from_id_subst'.
  + unfold subst_list_from_subst'. reflexivity.
  + unfold subst_list_from_subst'. simpl.
    unfold id_subst, generate_id_list; simpl.
    f_equal. fold subst_list_from_subst'. fold id_subst.
    rewrite <- id_list_from_id_subst'.
    apply (IHk (S l)).
Qed.

Lemma ctx_skip_Sn :
  forall {A} (Γ : ctx A) k,
    S k <= length Γ ->
    skipn k Γ = (lookup k Γ) :: (skipn (S k) Γ).
Proof.
  intros.
  generalize dependent Γ.
  induction k; intros.
  + destruct Γ.
    - inversion H.
    - simpl. reflexivity.
  + destruct Γ; try destruct Γ.
    - inversion H.
    - inversion H. inversion H1.
    - simpl. eapply IHk. simpl in *. lia.
Qed.

Lemma ctx_skip_Sn_length :
  forall {A} (Γ : ctx A) k,
    S k < length Γ ->
    skipn (length Γ - S k) Γ = (lookup (length Γ - S k) Γ) :: (skipn (length Γ - k) Γ).
Proof.
  intros.
  replace (length Γ - k) with (S (length Γ - S k)) by lia.
  eapply ctx_skip_Sn. lia.
Qed.

Lemma well_typed_subst_partitions_split' :
  forall Γ Γ1 Γ2 Δ σ,
    Γ ≜ Γ1 ∘ Γ2 ->
    (forall k,
      k <= length Γ ->
      well_typed_subst (skipn (length Γ - k) Γ) (subst_list_from_subst' σ k (length Γ - k)) Δ ->
      (exists Δ1 Δ2,
           Δ ≜ Δ1 ∘ Δ2
        /\ well_typed_subst (skipn (length Γ1 - k) Γ1) (subst_list_from_subst' σ k (length Γ1 - k)) Δ1
        /\ well_typed_subst (skipn (length Γ2 - k) Γ2) (subst_list_from_subst' σ k (length Γ2 - k)) Δ2)).
Proof.
  intros.
  generalize dependent Δ.
  generalize dependent Γ1.
  generalize dependent Γ2.
  generalize dependent Γ.

  induction k; intros.
  + repeat rewrite PeanoNat.Nat.sub_0_r in *.
    rewrite skipn_all in H1.
    unfold subst_list_from_subst' in *; simpl in *.
    inversion H1; subst.
    exists (repeat None (length Δ)), (repeat None (length Δ)).
    repeat split.
    - induction Δ; simpl; try repeat econstructor.
      * unfold ctx_eq in H2; specialize H2 with 0; simpl in H2. subst. econstructor.
      * apply IHΔ.
        ** assert (a = None).
           { unfold ctx_eq in H2; specialize H2 with 0; simpl in H2. subst. econstructor. }
           subst.
           econstructor.
           apply (proj2 (ctx_empty_insert_none nil _)). eassumption.
        ** assert (a = None).
           { unfold ctx_eq in H2; specialize H2 with 0; simpl in H2. subst. econstructor. }
           subst.
           apply (proj2 (ctx_empty_insert_none nil _)). eassumption.
    - rewrite skipn_all.
      econstructor. intro n. rewrite (lookup_ctx_nil empty_ctx); auto.
      rewrite ctx_lookup_repeat_none. reflexivity.
    - rewrite skipn_all.
      econstructor. intro n. rewrite (lookup_ctx_nil empty_ctx); auto.
      rewrite ctx_lookup_repeat_none. reflexivity.

  + destruct (PeanoNat.Nat.eq_dec (S k) (length Γ)).
    {
      destruct (ctx_split_preserves_length _ _ _ H).
      rewrite e. rewrite <- H2. rewrite <- H3.
      rewrite PeanoNat.Nat.sub_diag.
      rewrite e in H1.
      rewrite PeanoNat.Nat.sub_diag in H1.
      simpl in H1. simpl.

      destruct Γ.
      + exfalso. inversion e.
      + assert (k <= length (o :: Γ)) by lia.
        assert (k = length Γ) by (simpl in H0; simpl in e; lia).
        inversion H1; subst.
        inversion H; subst.
        inversion H7; subst.
        - simpl in *.
          assert (length Γ <= length (Some A :: Γ)) by (simpl; lia).
          pose proof (IHk (Some A :: Γ) H5 _ _ H Δ_σ).
          replace (length (Some A :: Γ) - length Γ) with 1 in H6.
          * apply H6 in H12.
            clear H6.
            destruct H12 as [Δ1 [Δ2 [? [? ?]]]].

            assert (exists Δ', Δ' ≜ Δ_M ∘ Δ1 /\ Δ ≜ Δ' ∘ Δ2).
            {
              clear - H6 H13.
              apply ctx_comm in H6. apply ctx_comm in H13.
              destruct (ctx_assoc _ _ _ _ _ H13 H6) as [Δ' [? ?]].
              exists Δ'. apply ctx_comm in H, H0; split; auto.
            }
            destruct H12 as [Δ' [? ?]].
            exists Δ', Δ2; split; auto. split.
            ** econstructor; eauto.
               replace (length (Some A :: Γ3)) with (S (length Γ)) in H8.
               replace (S (length Γ) - (length Γ)) with 1 in H8 by lia.
               simpl in H8. assumption.
            ** econstructor; eauto.
               replace (length (None :: Γ4)) with (S (length Γ)) in H9.
               replace (S (length Γ) - (length Γ)) with 1 in H9 by lia.
               simpl in H9. assumption.
          * replace (length (Some A :: Γ)) with (S (length Γ)) by reflexivity.
            lia.
        - simpl in *.
          assert (length Γ <= length (Some A :: Γ)) by (simpl; lia).
          pose proof (IHk (Some A :: Γ) H5 _ _ H Δ_σ).
          replace (length (Some A :: Γ) - length Γ) with 1 in H6.
          * apply H6 in H12.
            clear H6.
            destruct H12 as [Δ1 [Δ2 [? [? ?]]]].

            assert (exists Δ', Δ' ≜ Δ_M ∘ Δ2 /\ Δ ≜ Δ1 ∘ Δ').
            {
              clear - H6 H13.
              apply ctx_comm in H13.
              destruct (ctx_assoc _ _ _ _ _ H13 H6) as [Δ' [? ?]].
              exists Δ'. apply ctx_comm in H; split; auto.
            }
            destruct H12 as [Δ' [? ?]].
            exists Δ1, Δ'; split; auto. split.
            ** econstructor; eauto.
               replace (length (None :: Γ3)) with (S (length Γ)) in H8.
               replace (S (length Γ) - (length Γ)) with 1 in H8 by lia.
               simpl in H8. assumption.
            ** econstructor; eauto.
               replace (length (Some A :: Γ4)) with (S (length Γ)) in H9.
               replace (S (length Γ) - (length Γ)) with 1 in H9 by lia.
               simpl in H9. assumption.
          * replace (length (Some A :: Γ)) with (S (length Γ)) by reflexivity.
            lia.
        - simpl in *.
          inversion H; subst.
          assert (length Γ <= length (None :: Γ)) by (simpl; lia).
          pose proof (IHk (None :: Γ) H5 _ _ H Δ).
          replace (length (None :: Γ) - length Γ) with 1 in H6.
          * apply H6 in H11. clear H6.
            destruct H11 as [Δ1 [Δ2 [? [? ?]]]].
            exists Δ1, Δ2; split; auto; split; inversion H7; subst.
            ** econstructor.
               replace (length (None :: Γ3)) with (S (length Γ)) in H8.
               replace (S (length Γ) - (length Γ)) with 1 in H8 by lia.
               simpl in H8. assumption.
            ** econstructor; eauto.
               replace (length (None :: Γ4)) with (S (length Γ)) in H9.
               replace (S (length Γ) - (length Γ)) with 1 in H9 by lia.
               simpl in H9. assumption.
          * replace (length (None :: Γ)) with (S (length Γ)) by reflexivity.
            lia.
    }
    {
      destruct (ctx_split_preserves_length _ _ _ H).
      rewrite ctx_skip_Sn_length; rewrite <- H2; try lia.
      rewrite ctx_skip_Sn_length; rewrite <- H3; try lia.

      rewrite ctx_skip_Sn_length in H1; try lia.
      inversion H1; subst.
      + replace (S (length Γ - S k)) with (length Γ - k) in H10 by lia.
        assert (k <= length Γ) by lia.
        (* use H10 for induction hypothesis *)
        pose proof (IHk Γ H5 Γ2 Γ1 H Δ_σ H10).
        destruct H6 as [Δ1 [Δ2 [? [? ?]]]].

        pose proof (decide_ctx_split_partition _ _ _
                    (length Γ - S k) (Some A) H H4).
        destruct H12.
        - (* exixsts (Δ_M ∘ Δ1),  Δ2 *)
          assert (exists Δ', Δ' ≜ Δ_M ∘ Δ1 /\ Δ ≜ Δ' ∘ Δ2).
          {
            apply ctx_comm in H6.
            apply ctx_comm in H11.
            destruct (ctx_assoc _ _ _ _ _ H11 H6) as [Δ' [? ?]].
            apply ctx_comm in H13, H14.
            exists Δ'; split; auto.
          }
          destruct H13 as [Δ' [? ?]].
          exists Δ', Δ2; split; auto. split.
          * simpl. destruct H12. rewrite H12.
            econstructor; eauto.
            replace (S (length Γ - S k)) with (length Γ - k) by lia.
            rewrite H2.
            auto.
          * simpl. destruct H12. rewrite H15.
            econstructor; eauto.
            replace (S (length Γ - S k)) with (length Γ - k) by lia.
            rewrite H3.
            auto.
        - (* exists Δ1, (Δ_M ∘ Δ2)*)
          assert (exists Δ', Δ' ≜ Δ_M ∘ Δ2 /\ Δ ≜ Δ1 ∘ Δ').
          {
            apply ctx_comm in H11.
            destruct (ctx_assoc _ _ _ _ _ H11 H6) as [Δ' [? ?]].
            apply ctx_comm in H13.
            exists Δ'; split; auto.
          }
          destruct H13 as [Δ' [? ?]].
          exists Δ1, Δ'; split; auto. split.
          * simpl. destruct H12. rewrite H12.
            econstructor; eauto.
            replace (S (length Γ - S k)) with (length Γ - k) by lia.
            rewrite H2.
            auto.
          * simpl. destruct H12. rewrite H15.
            econstructor; eauto.
            replace (S (length Γ - S k)) with (length Γ - k) by lia.
            rewrite H3.
            auto.
      + replace (S (length Γ - S k)) with (length Γ - k) in H9 by lia.
        assert (k <= length Γ) by lia.
        pose proof (IHk Γ H5 Γ2 Γ1 H Δ H9).
        destruct H6 as [Δ1 [Δ2 [? [? ?]]]].
        pose proof (decide_ctx_split_partition _ _ _ (length Γ - S k) None H H4).
        destruct H10.
        - destruct H10. rewrite H10. rewrite H11. simpl.
          exists Δ1, Δ2; split; auto. split.
          * econstructor.
            replace (S (length Γ - S k)) with (length Γ - k) by lia.
            rewrite H2. auto.
          * econstructor.
            replace (S (length Γ - S k)) with (length Γ - k) by lia.
            rewrite H3. auto.
        - destruct H10. rewrite H10. rewrite H11. simpl.
          exists Δ1, Δ2; split; auto. split.
          * econstructor.
            replace (S (length Γ - S k)) with (length Γ - k) by lia.
            rewrite H2. auto.
          * econstructor.
            replace (S (length Γ - S k)) with (length Γ - k) by lia.
            rewrite H3. auto.
    }
Qed.

Lemma well_typed_subst_partitions_split :
  forall Γ Γ1 Γ2 Δ σ,
    Γ ≜ Γ1 ∘ Γ2 ->
    well_typed_subst Γ (subst_list_from_subst σ (length Γ)) Δ ->
    (exists Δ1 Δ2,
         Δ ≜ Δ1 ∘ Δ2
      /\ well_typed_subst Γ1 (subst_list_from_subst σ (length Γ1)) Δ1
      /\ well_typed_subst Γ2 (subst_list_from_subst σ (length Γ2)) Δ2).
Proof.
  intros.
  destruct (ctx_split_preserves_length _ _ _ H) as [? ?].
  pose proof (well_typed_subst_partitions_split' _ _ _ Δ σ H (length Γ) (PeanoNat.Nat.le_refl (length Γ))).
  rewrite <- H1 in *. rewrite <- H2 in *.
  rewrite PeanoNat.Nat.sub_diag in H3. rewrite skipn_0 in H3.
  apply H3 in H0. assumption.
Qed.

Lemma up_subst_1_upM :
  forall σ n k,
    subst_list_from_subst' (up_subst σ) n (S k)
      = map upM (subst_list_from_subst' σ n k).
Proof.
  intros.
  generalize dependent k.
  induction n; intros.
  + reflexivity.
  + simpl. f_equal. apply IHn.
Qed.

Lemma subst_upM_well_typed :
  forall Γ Δ Σ,
    well_typed_subst Γ Σ Δ ->
    well_typed_subst Γ (map upM Σ) (None :: Δ).
Proof.
  intros.
  generalize dependent Σ.
  generalize dependent Δ.
  induction Γ; intros.
  + inversion H; subst. simpl.
    econstructor. eapply (proj1 (ctx_empty_insert_none nil _)).
    assumption.
  + inversion H; subst.
    - simpl. econstructor; eauto.
      * apply ((proj1 (proj2 up_shift_sound)) M nil _) in H2.
        simpl in H2. apply H2.
      * econstructor. econstructor. auto.
    - simpl. econstructor. apply IHΓ; auto.
Qed.

Lemma up_subst_well_typed :
  forall Γ Δ A σ,
    well_typed_subst Γ (subst_list_from_subst σ (length Γ)) Δ ->
    well_typed_subst (A .: Γ) (subst_list_from_subst (up_subst σ) (length (A .: Γ))) (A .: Δ).
Proof.
  intros.
  unfold subst_list_from_subst.
  unfold subst_list_from_subst'.
  simpl.
  fold subst_list_from_subst'.
  econstructor.
  + assert (A .: (repeat None (length Δ)) ⊢ future 0 :! A).
    {
      econstructor. intro n. induction n; auto.
      simpl. rewrite (lookup_ctx_nil empty_ctx); auto.
      rewrite ctx_lookup_repeat_none. reflexivity.
    }
    apply H0.
  + rewrite up_subst_1_upM. eapply subst_upM_well_typed. eassumption.
  + econstructor.
    - econstructor.
    - apply ctx_split_empty_refl.
      * intro n. rewrite (lookup_ctx_nil empty_ctx); auto.
        rewrite ctx_lookup_repeat_none; auto.
      * rewrite repeat_length; auto.
Qed.

Lemma subst_on_empty_ctx :
  forall Γ Σ Δ,
    ctx_eq Γ empty_ctx ->
    well_typed_subst Γ Σ Δ ->
    ctx_eq Δ empty_ctx.
Proof.
  intros.
  generalize dependent Σ.
  (* generalize dependent Δ. *)
  induction Γ; intros.
  + inversion H0; auto.
  + assert (a = None).
    { unfold ctx_eq in H; specialize H with 0; assumption. }
    rewrite H1 in *. inversion H0; subst.
    eapply IHΓ.
    - apply (ctx_empty_insert_none nil _); assumption.
    - eassumption.
Qed.

Lemma subst_none_prefix :
  forall Γ k Σ Δ,
    well_typed_subst ((repeat None k) ++ Γ) Σ Δ ->
    well_typed_subst Γ (skipn k Σ) Δ.
Proof.
  intros.
  generalize dependent Σ.
  induction k; intros.
  + assumption.
  + simpl in H. inversion H; subst.
    simpl. eapply IHk; auto.
Qed.

Lemma subst_on_singleton_list :
  forall nl nr Σ' Σ Δ A M,
    length Σ' = nl ->
    well_typed_subst ((repeat None nl) ++ (A .: repeat None nr))
                     (Σ' ++ (M :: Σ))
                     Δ ->
    Δ ⊢ M :! A.
Proof.
  intros.
  apply subst_none_prefix in H0.
  rewrite skipn_app in H0. rewrite H in H0. rewrite PeanoNat.Nat.sub_diag in H0.
  simpl in H0.
  rewrite <- H in H0.
  rewrite skipn_all in H0; simpl in H0.
  inversion H0; subst.
  apply subst_on_empty_ctx in H7.
  + apply ctx_comm in H8.
    apply ctx_split_empty_neutral in H8; auto.
    rewrite H8; auto.
  + intro n. rewrite ctx_lookup_repeat_none. rewrite lookup_ctx_nil; auto.
Qed.

(* Substitution Lemma *)
Lemma substitution_preserves_typing :
  (forall Γ P, Γ ⊢ P :# ->
    forall Δ σ,
      well_typed_subst Γ (subst_list_from_subst σ (length Γ)) Δ ->
      Δ ⊢ subst_process P σ :#)
  /\
  (forall Γ M A, Γ ⊢ M :! A ->
    forall Δ σ,
      well_typed_subst Γ (subst_list_from_subst σ (length Γ)) Δ ->
      Δ ⊢ subst_message M σ :! A)
  /\
  (forall Γ s A, Γ ⊢ s :$ A ->
    forall Δ σ,
      well_typed_subst Γ (subst_list_from_subst σ (length Γ)) Δ ->
      Δ ⊢ subst_statement s σ :$ A).
Proof.
  apply typing_ind; intros; simpl.
  + destruct (well_typed_subst_partitions_split _ _ _ _ _ c H1) as [Δ1 [Δ2 [? [? ?]]]].
    econstructor; eauto.
  + destruct (well_typed_subst_partitions_split _ _ _ _ _ c H1) as [Δ1 [Δ2 [? [? ?]]]].
    econstructor; eauto.
    - apply (up_subst_well_typed _ _ A) in H3; eauto.
    - apply (up_subst_well_typed _ _ (dual A)) in H4; eauto.
  + destruct (well_typed_subst_partitions_split _ _ _ _ _ c H1) as [Δ1 [Δ2 [? [? ?]]]].
    econstructor; eauto.
    apply (up_subst_well_typed _ _ A) in H3; eauto.
  + econstructor. eapply subst_on_empty_ctx; eauto.
  + assert (exists k, Γ = (repeat None i) ++ (A .: (repeat None k))).
    {
      clear - c.
      generalize dependent Γ.
      induction i; intros.
      + destruct Γ.
        - exfalso. unfold ctx_eq in c; specialize c with 0. simpl in c. congruence.
        - simpl. exists (length Γ).
          assert (o = Some A) by  (unfold ctx_eq in c; apply (c 0)). rewrite H in *.
          unfold ".:" in *; simpl in *. f_equal.
          apply ctx_eq_single_empty in c; auto.
      + destruct Γ.
        - exfalso.
          unfold ctx_eq in c; specialize c with (S i).
          rewrite lookup_ctx_nil in c; auto.
          rewrite ctx_lookup_after_insert in c.
          congruence.
        - specialize IHi with Γ.
          assert (ctx_eq Γ (insert i A empty_ctx)).
          {
            intro n.
            unfold ctx_eq in c; specialize c with (S n).
            simpl in c. assumption.
          }
          apply IHi in H.
          destruct H.
          exists x. rewrite H.
          assert (o = None).
          { unfold ctx_eq in c; specialize c with 0. simpl in c. auto. }
          rewrite H0.
          reflexivity.
    }
    destruct H0.
    assert (exists Σ', length Σ' = i /\
      (subst_list_from_subst σ (length Γ)) = Σ' ++ (σ i) :: (subst_list_from_subst' σ (length Γ - (S i)) (S i))).
    {
      assert (length Γ > 0).
      {
        rewrite H0.
        rewrite length_app.
        simpl. lia.
      }
      assert (i < length Γ).
      {
        rewrite H0.
        rewrite length_app.
        rewrite repeat_length. simpl.
        lia.
      }
      clear - H H1 H2.
      (* generalize dependent Γ. *)
      induction i; intros.
      + 
      (* + assert (length Γ = S x).
        { rewrite H0. simpl. rewrite repeat_length; auto. } *)
        exists nil.
        split; auto. simpl.
        destruct (length Γ); try now inversion H1.
        simpl.
        rewrite PeanoNat.Nat.sub_0_r.
        reflexivity.
      + assert (i < length Γ) by lia.
        destruct (IHi H0) as [Σ [? ?]].
        exists (Σ ++ (σ i) :: nil).
        split.
        - rewrite length_app; simpl. lia.
        - rewrite H4.
          rewrite <- app_assoc.
          f_equal. simpl. f_equal.

          destruct (length Γ - S i) eqn:E.
          * exfalso.
            assert (0 > 1) by lia. inversion H5.
          * replace (length Γ - S (S i)) with n by lia.
            reflexivity.
    }
    destruct H1 as [Σ' [? ?]].
    rewrite H0 in H at 1.
    rewrite H2 in H.
    apply subst_on_singleton_list in H; auto.
  + econstructor; eauto.
  + apply (up_subst_well_typed _ _ (dual A)) in H0.
    econstructor; eauto.
  + apply (up_subst_well_typed _ _ (dual B)) in H0.
    econstructor; eauto.
  + econstructor.
    * apply (up_subst_well_typed _ _ (dual A)) in H1; eauto.
    * apply (up_subst_well_typed _ _ (dual B)) in H1; eauto.
  + destruct (well_typed_subst_partitions_split _ _ _ _ _ c H1) as [Δ1 [Δ2 [? [? ?]]]].
    econstructor; eauto.
    - apply (up_subst_well_typed _ _ (dual A)) in H3; eauto.
    - apply (up_subst_well_typed _ _ (dual B)) in H4; eauto.
  + econstructor.
    apply (up_subst_well_typed _ _ (dual B)) in H0.
    apply (up_subst_well_typed _ _ (dual A)) in H0.
    eauto.
  + econstructor. eapply subst_on_empty_ctx; eauto.
  + econstructor; eauto.
Qed.
