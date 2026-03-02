From FD Require Import Syntax.
From FD Require Import Types.
From FD Require Import Typing.
From FD Require Import Contexts.
From FD Require Import Reduction.
From FD Require Import Renaming.
From FD Require Import StructCong.
From FD Require Import FreeVars.
From FD Require Import Substitution.

From Stdlib Require Import List.

Theorem preservation :
  forall P Q Γ, Γ ⊢ P :# -> P ⊳ Q -> Γ ⊢ Q :#.
Proof.
  intros P Q Γ H_wellty H_red.
  generalize dependent Γ.
  induction H_red; intros Γ H_wellty.
  + inversion H_wellty; subst.
    inversion H4; inversion H5; subst.
    inversion H1; subst.
    inversion H8; subst.

    assert (exists Γ', Γ' ≜ Γ2 ∘ Γ3 /\ Γ ≜ Γ' ∘ Γ4) as H_new_ctxs.
    {
      apply ctx_comm in H3.
      destruct (ctx_assoc _ _ _ _ _ H2 H3) as [Γ' [? ?]].
      exists Γ'; split.
      + apply ctx_comm in H; assumption.
      + apply ctx_comm in H0; assumption.
    }
    destruct H_new_ctxs as [Γ' [? ?]].

    eapply t_cut.
    - apply H0.
    - eapply t_cut.
      * assert ((dual (dual B)) .: Γ' ≜ (dual (dual B)) .: Γ2 ∘ None :: Γ3).
        { econstructor. econstructor. assumption. }
        apply H6.
      * apply H9.
      * rewrite dual_involutive.
        apply ((proj1 up_shift_sound) P nil _) in H7.
        simpl in H7. apply swap01_preserves_typing in H7.
        apply H7.
    - rewrite dual_involutive. assumption.
  + inversion H_wellty; subst. inversion H3; inversion H4; subst.
    inversion H2; inversion H8; subst.
    econstructor; eauto.
    rewrite dual_involutive.
    simpl in H11. inversion H11. apply (f_equal dual) in H0.
    rewrite dual_involutive in H0. rewrite <- H0.
    assumption.
  + inversion H_wellty; subst. inversion H3; inversion H4; subst.
    inversion H2; inversion H8; subst.
    econstructor; eauto.
    rewrite dual_involutive.
    simpl in H11. inversion H11. apply (f_equal dual) in H6.
    rewrite dual_involutive in H6. rewrite <- H6.
    assumption.
  + inversion H_wellty; subst. inversion H4. inversion H2; subst.
    inversion H3; subst. inversion H5; subst.
    rewrite (ctx_split_with_empty _ _ _ H H1). assumption.
  + inversion H_wellty; subst. inversion H3; subst.
    inversion H6; subst.
    inversion H2; subst.
    inversion H8; subst.
    - assert (Γ1 = Γ6).
      {
        (* first show that Γ5 ≃ empty_ctx *)
        assert (ctx_eq Γ5 empty_ctx).
        {
          eapply ctx_lookup_eq_empty.
          intro n.
          unfold ctx_eq in H5; specialize H5 with (S n); simpl in H5.
          rewrite (lookup_ctx_nil empty_ctx) in H5.
          assumption. auto.
        }
        eapply ctx_split_empty_neutral; eauto.
      }
      subst.

      assert (A0 = A).
      { unfold ctx_eq in H5; specialize H5 with 0; simpl in H5. injection H5; auto. }
      subst.

      pose proof
        (proj1 ((proj1 (proj2 down_shift_sound)) M nil Γ6 (dual A)
               ((proj1 (proj2 ctx_none_not_free)) M _ _ 0 H7 eq_refl)) H7).
      simpl in H.

      eapply substitution_preserves_typing.
      * eapply H4.
      * simpl.
        econstructor.
        ** apply H.
        ** fold subst_list_from_subst'.
           fold subst_list_from_subst.
           rewrite subst_list_id_scons.
           apply subst_list_from_id_wellty.
        ** apply H1.
    - exfalso.
      unfold ctx_eq in H5. specialize H5 with 0; simpl in H5. discriminate.
  + inversion H_wellty; subst.
    eapply substitution_preserves_typing.
    - eapply H3.
    - simpl. econstructor.
      * simpl. econstructor. apply H4.
      * fold subst_list_from_subst'.
        rewrite subst_list_id_scons.
        apply subst_list_from_id_wellty.
      * apply ctx_comm in H1. apply H1.
  + inversion H_wellty; subst. econstructor; eauto.
  + inversion H_wellty; subst. econstructor; eauto.
  + apply ((proj1 struct_cong_preserves_typing) _ _ H) in H_wellty.
    apply IHH_red in H_wellty.
    apply ((proj1 struct_cong_preserves_typing) _ _ H0) in H_wellty.
    assumption.
Qed.
