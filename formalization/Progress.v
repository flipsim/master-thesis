From FD Require Import Syntax.
From FD Require Import Types.
From FD Require Import StructCong.
From FD Require Import Reduction.
From FD Require Import Contexts.
From FD Require Import Typing.
From FD Require Import FreeVars.
From FD Require Import FinalProcess.

From Stdlib Require Import Lia.

Theorem progress :
  forall Γ P, Γ ⊢ P :# -> (exists P', P ⊳ P') \/ is_final P.
Proof.
  intros.
  enough ((exists P' : process, P ⊳ P') \/ final P).
  {
    destruct H0; auto. right. eapply well_typed_final_process_is_final_wt; eauto.
  }
  induction H.
  + apply or_comm.
    apply (link_final_or_reduces _ _ _ (t_ax _ _ _ _ _ _ H H0 H1)).
  + (* restructure cut into canonical form *)
    assert (Γ ⊢ (cut P Q) :# ) by (econstructor; eauto).
    destruct (canonical_cut_form _ _ _ H2) as [P' [? ?]].

    (* decide whether canonical form is final or reduces *)
    assert (Γ ⊢ P' :#). { apply ((proj1 struct_cong_preserves_typing) _ _ H3) in H2; auto. }
    destruct (cut_list_final_or_reduces _ _ H5 H4).
    - inversion H6; subst.
      * inversion H4.
      * inversion H4.
      * inversion H4.
      * right. eapply final_list; eauto.
        eapply c_trans; eauto.
    - destruct H6 as [P'' ?].
      left. exists P''. eapply r_struct; eauto. apply c_refl.
  + left.
    exists (subst_process P ((prefix s) ⋅ id_subst)).
    econstructor.
  + right. econstructor.
Qed.

Corollary progress_for_closed_processes :
  forall Γ P, ctx_eq Γ empty_ctx -> Γ ⊢ P :# -> (exists P', P ⊳ P') \/ (P = stop).
Proof.
  intros.
  destruct (progress _ _ H0); auto.
  right. inversion H1; subst; auto;
  exfalso.
  + assert (i ∈ link (future i) M) by repeat econstructor.
    assert (~ i ∈ link (future i) M).
    { apply ((proj1 ctx_none_not_free) _ _ _ H0). apply ctx_lookup_eq_empty; auto. }
    congruence.
  + assert (i ∈ link M (future i)). { apply fv_link_r; econstructor. }
    assert (~ i ∈ link M (future i)).
    { apply ((proj1 ctx_none_not_free) _ _ _ H0). apply ctx_lookup_eq_empty; auto. }
    congruence.
  + destruct xs.
    - inversion H3.
    - apply (proj1 struct_cong_preserves_typing _ _ H4) in H0.
      assert ((Nat.pred n) ∈ P').
      {
        apply (link_list_free_vars _ (n :: xs)); auto.
        + intros. destruct x; try lia. congruence.
        + apply link_list_wt_implies_link_list; auto.
        + simpl. left; auto.
      }
      assert (~ (Nat.pred n) ∈ P').
      {
        apply ((proj1 ctx_none_not_free) _ _ _ H0).
        apply ctx_lookup_eq_empty; auto.
      }
      congruence.
Qed.
