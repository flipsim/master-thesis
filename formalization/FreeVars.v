From FD Require Import Syntax.
From FD Require Import Types.
From FD Require Import Typing.
From FD Require Import Contexts.

From Stdlib Require Import ssreflect.
From Stdlib Require Import List.
From Stdlib Require Import Lia.

Lemma formula_property :
  (forall (p : process),
    forall Γ n x, Γ ⊢ p :# -> lookup n Γ = Some x -> n ∈ p)
  /\
  (forall (m : message),
    forall Γ A n x, Γ ⊢ m :! A -> lookup n Γ = Some x -> occurs_free_message n m)
  /\
  (forall (s : statement),
    forall Γ A n x, Γ ⊢ s :$ A -> lookup n Γ = Some x -> occurs_free_statement n s).
Proof.
  apply syntax_ind; intros;
  try (
    inversion H0; inversion H1; subst; econstructor; eapply H; eauto
  ).
  + inversion H1; subst.
    symmetry in H2.
    pose proof (decide_ctx_split_partition _ _ _ _ _ H5 H2).
    destruct H3 as [[] | []].
    - apply fv_link_l. eapply H; eauto.
    - apply fv_link_r. eapply H0; eauto.
  + inversion H1; subst.
    symmetry in H2.
    pose proof (decide_ctx_split_partition _ _ _ _ _ H5 H2).
    destruct H3 as [[] | []].
    - apply fv_cut_l. eapply H; eauto.
    - apply fv_cut_r. eapply H0; eauto.
  + inversion H1; subst.
    symmetry in H2.
    pose proof (decide_ctx_split_partition _ _ _ _ _ H5 H2).
    destruct H3 as [[] | []].
    - apply fv_seq_l. eapply H; eauto.
    - apply fv_seq_r. eapply H0; eauto.
  + inversion H. clear - H0 H1.
    unfold ctx_eq in H1. specialize H1 with n.
    rewrite (lookup_ctx_nil empty_ctx eq_refl) in H1.
    congruence.
  + inversion H; subst.
    destruct (PeanoNat.Nat.eq_dec n0 n).
    - subst. econstructor.
    - unfold ctx_eq in H3.
      specialize H3 with n0.
      rewrite ctx_lookup_singleton_neq in H3; auto.
      congruence.
  + inversion H1; subst. econstructor. eapply H; eauto.
  + inversion H1; subst.
    symmetry in H2.
    pose proof (decide_ctx_split_partition _ _ _ _ _ H5 H2).
    destruct H3 as [[] | []].
    - apply fv_send_l. eapply H; eauto.
    - apply fv_send_r. eapply H0; eauto.
  + inversion H. unfold ctx_eq in H1; specialize H1 with n.
    rewrite (lookup_ctx_nil empty_ctx eq_refl) in H1.
    congruence.
Qed.

Lemma free_var_in_ctx :
  (forall n p, n ∈ p ->
    forall Γ, Γ ⊢ p :# -> exists x, lookup n Γ = Some x)
  /\
  (forall n m, occurs_free_message n m ->
    forall Γ A, Γ ⊢ m :! A -> exists x, lookup n Γ = Some x)
  /\
  (forall n s, occurs_free_statement n s ->
    forall Γ A, Γ ⊢ s :$ A -> exists x, lookup n Γ = Some x).
Proof.
  apply fv_ind; intros.
  + inversion H0; subst.
    specialize H with Γ1 A.
    destruct (H H5).
    exists x.
    eapply ctx_split_lookup_in_partition; eauto.
  + inversion H0; subst.
    specialize H with Γ2 (dual A).
    destruct (H H6).
    exists x.
    apply ctx_comm in H3.
    eapply ctx_split_lookup_in_partition; eauto.
  + inversion H0; subst.
    destruct (H (A .: Γ1) H5).
    exists x.
    simpl in H1.
    eapply ctx_split_lookup_in_partition; eauto.
  + inversion H0; subst.
    apply ctx_comm in H3.
    destruct (H ((dual A) .: Γ2) H6).
    exists x.
    simpl in H1.
    eapply ctx_split_lookup_in_partition; eauto.
  + inversion H0; subst.
    destruct (H (A .: Γ1) H5).
    exists x.
    simpl in H1.
    eapply ctx_split_lookup_in_partition; eauto.
  + inversion H0; subst.
    destruct (H Γ2 A H6).
    exists x.
    simpl in H1.
    apply ctx_comm in H3.
    eapply ctx_split_lookup_in_partition; eauto.
  + inversion H; subst. exists A.
    unfold ctx_eq in H2.
    specialize H2 with n.
    rewrite ctx_lookup_after_insert in H2.
    assumption.
  + inversion H0; subst.
    destruct (H Γ A H3).
    exists x. assumption.
  + inversion H0; subst.
    destruct (H (dual A0 .: Γ) H3).
    exists x. assumption.
  + inversion H0; subst.
    destruct (H (dual B .: Γ) H3).
    exists x. assumption.
  + inversion H0; subst.
    destruct (H (dual A0 .: Γ) H4).
    exists x. assumption.
  + inversion H0; subst.
    destruct (H (dual B .: Γ) H6).
    exists x. assumption.
  + inversion H0; subst.
    destruct (H (dual A0 .: Γ1) H5).
    exists x.
    eapply ctx_split_lookup_in_partition; eauto.
  + inversion H0; subst.
    destruct (H (dual B .: Γ2) H7).
    exists x.
    apply ctx_comm in H3.
    eapply ctx_split_lookup_in_partition; eauto.
  + inversion H0; subst.
    destruct (H (dual A0 .: (dual B .: Γ)) H3).
    exists x. assumption.
  + inversion H0; subst.
    destruct (H Γ H3).
    exists x. assumption.
Qed.

Lemma ctx_none_not_free :
  (forall (p : process),
    forall Γ n, Γ ⊢ p :# -> lookup n Γ = None -> ~ (n ∈ p))
  /\
  (forall (m : message),
    forall Γ A n, Γ ⊢ m :! A -> lookup n Γ = None -> ~ (occurs_free_message n m))
  /\
  (forall (s : statement),
    forall Γ A n, Γ ⊢ s :$ A -> lookup n Γ = None -> ~ (occurs_free_statement n s)).
Proof.
  apply syntax_ind; intros; intro Hfv.
  + inversion H1; subst; inversion Hfv; subst.
    - eapply H; eauto. symmetry in H2.
      destruct (decide_ctx_split_partition _ _ _ _ _ H5 H2) as [[] | []]; eauto.
    - eapply H0; eauto. symmetry in H2.
      destruct (decide_ctx_split_partition _ _ _ _ _ H5 H2) as [[] | []]; eauto.
  + inversion H1; subst; inversion Hfv; subst.
    - eapply H; eauto. symmetry in H2.
      destruct (decide_ctx_split_partition _ _ _ _ _ H5 H2) as [[] | []]; eauto.
    - eapply H0; eauto. symmetry in H2.
      destruct (decide_ctx_split_partition _ _ _ _ _ H5 H2) as [[] | []]; eauto.
  + inversion H1; subst; inversion Hfv; subst.
    - eapply H; eauto. symmetry in H2.
      destruct (decide_ctx_split_partition _ _ _ _ _ H5 H2) as [[] | []]; eauto.
    - eapply H0; eauto. symmetry in H2.
      destruct (decide_ctx_split_partition _ _ _ _ _ H5 H2) as [[] | []]; eauto.
  + inversion Hfv.
  + inversion Hfv; subst. inversion H; subst.
    unfold ctx_eq in H3; specialize H3 with n.
    rewrite ctx_lookup_after_insert in H3.
    congruence.
  + inversion H1; subst; inversion Hfv; subst.
    eapply H; eauto. inversion H0; subst. eauto.
  + inversion H1; subst; inversion Hfv; subst. inversion H0; subst.
    eapply H; eauto. eauto.
  + inversion H1; subst; inversion Hfv; subst. inversion H0; subst.
    eapply H; eauto. eauto.
  + inversion H1; subst; inversion Hfv; subst. inversion H1; subst.
    - eapply H; eauto. simpl. auto.
    - eapply H0; eauto. simpl. auto.
  + inversion H1; subst; inversion Hfv; subst.
    - eapply H; eauto. symmetry in H2.
      destruct (decide_ctx_split_partition _ _ _ _ _ H5 H2) as [[] | []]; eauto.
    - eapply H0; eauto. symmetry in H2.
      destruct (decide_ctx_split_partition _ _ _ _ _ H5 H2) as [[] | []]; eauto.
  + inversion H1; subst; inversion Hfv; subst. inversion H0; subst.
    eapply H; eauto. eauto.
  + inversion Hfv.
  + inversion H0; inversion Hfv; subst. eapply H; eauto.
Qed.

Lemma n_fv_down_Sn :
  (forall (p : process),
    forall n k, k < n -> n ∈ (down1_process p k) -> (S n) ∈ p)
  /\
  (forall (m : message),
    forall n k, k < n -> occurs_free_message n (down1_message m k) -> occurs_free_message (S n) m)
  /\
  (forall (s : statement),
    forall n k, k < n -> occurs_free_statement n (down1_statement s k) -> occurs_free_statement (S n) s).
Proof.
  apply syntax_ind; intros.
  + simpl in H2; inversion H2; subst.
    - apply fv_link_l. eapply (H n k); auto.
    - apply fv_link_r. eapply (H0 n k); auto.
  + simpl in H2; inversion H2; subst.
    - apply fv_cut_l. eapply (H (S n) (S k)); auto. lia.
    - apply fv_cut_r. eapply (H0 (S n) (S k)); auto. lia.
  + simpl in H2; inversion H2; subst.
    - apply fv_seq_l. eapply (H (S n) (S k)); auto. lia.
    - apply fv_seq_r. eapply (H0 n k); auto.
  + inversion H0.
  + unfold down1_message in H0.
    destruct (Nat.ltb k n) eqn:E.
    - apply PeanoNat.Nat.ltb_lt in E.
      inversion H0; subst.
      replace (S (Nat.pred n)) with (n) by lia.
      constructor.
    - exfalso.
      apply PeanoNat.Nat.ltb_ge in E.
      inversion H0; subst.
      assert (k < k) by lia.
      eapply PeanoNat.Nat.lt_irrefl; eauto.
  + simpl in H1; inversion H1; subst. econstructor. eapply H; eauto.
  + simpl in H1; inversion H1; subst. econstructor. eapply (H (S n) (S k)); eauto. lia.
  + simpl in H1; inversion H1; subst. econstructor. eapply (H (S n) (S k)); eauto. lia.
  + simpl in H2; inversion H2; subst.
    - apply fv_choice_l. eapply (H (S n) (S k)); auto. lia.
    - apply fv_choice_r. eapply (H0 (S n) (S k)); auto. lia.
  + simpl in H2; inversion H2; subst.
    - apply fv_send_l. eapply (H (S n) (S k)); auto. lia.
    - apply fv_send_r. eapply (H0 (S n) (S k)); auto. lia.
  + simpl in H1; inversion H1; subst; econstructor. eapply (H (S (S n)) (S (S k))); eauto; lia.
  + inversion H0.
  + inversion H1; subst. econstructor. eapply H; eauto.
Qed.

Lemma n_fv_down_n :
  (forall (p : process),
    forall n k, k >= n -> n ∈ p -> n ∈ (down1_process p k))
  /\
  (forall (m : message),
    forall n k, k >= n -> occurs_free_message n m -> occurs_free_message n (down1_message m k))
  /\
  (forall (s : statement),
    forall n k, k >= n -> occurs_free_statement n s -> occurs_free_statement n (down1_statement s k)).
Proof.
  apply syntax_ind; intros.
  + simpl in H2; inversion H2; subst.
    - apply fv_link_l. eapply (H n k); auto.
    - apply fv_link_r. eapply (H0 n k); auto.
  + simpl in H2; inversion H2; subst.
    - apply fv_cut_l. eapply (H (S n) (S k)); auto. lia.
    - apply fv_cut_r. eapply (H0 (S n) (S k)); auto. lia.
  + simpl in H2; inversion H2; subst.
    - apply fv_seq_l. eapply (H (S n) (S k)); auto. lia.
    - apply fv_seq_r. eapply (H0 n k); auto.
  + inversion H0.
  + unfold down1_message in H0.
    destruct (Nat.ltb k n) eqn:E.
    - exfalso.
      apply PeanoNat.Nat.ltb_lt in E.
      inversion H0; subst. assert (k < k) by lia.
      apply PeanoNat.Nat.lt_irrefl in H1.
      auto.
    - unfold down1_message. rewrite E. assumption.
  + simpl in H1; inversion H1; subst. econstructor. eapply H; eauto.
  + simpl in H1; inversion H1; subst. econstructor. eapply (H (S n) (S k)); eauto. lia.
  + simpl in H1; inversion H1; subst. econstructor. eapply (H (S n) (S k)); eauto. lia.
  + simpl in H2; inversion H2; subst.
    - apply fv_choice_l. eapply (H (S n) (S k)); auto. lia.
    - apply fv_choice_r. eapply (H0 (S n) (S k)); auto. lia.
  + simpl in H2; inversion H2; subst.
    - apply fv_send_l. eapply (H (S n) (S k)); auto. lia.
    - apply fv_send_r. eapply (H0 (S n) (S k)); auto. lia.
  + simpl in H1; inversion H1; subst; econstructor. eapply (H (S (S n)) (S (S k))); eauto; lia.
  + inversion H0.
  + inversion H1; subst. econstructor. eapply H; eauto.
Qed.

Lemma nfv_renaming :
  (forall (p : process),
    forall n (r : renaming), bijective r
      -> ~ (n ∈ p) -> ~ ((r n) ∈ (rename_process p r)))
  /\
  (forall (m : message),
    forall n (r : renaming), bijective r
      -> ~ (occurs_free_message n m) -> ~ (occurs_free_message (r n) (rename_message m r)))
  /\
  (forall (s : statement),
    forall n (r : renaming), bijective r
      -> ~ (occurs_free_statement n s) -> ~ (occurs_free_statement (r n) (rename_statement s r))).
Proof.
  apply syntax_ind; intros; intro H_nfv; inversion H_nfv; subst.
  + eapply H; eauto.
    intro H_fv. apply H2. apply fv_link_l. assumption.
  + eapply H0; eauto.
    intro H_fv. apply H2. apply fv_link_r. assumption.
  + eapply (H (S n) (up_ren r)); eauto.
    - apply shift_preserves_bijection; auto.
    - intro H_fv. apply H2. apply fv_cut_l; auto.
  + eapply (H0 (S n) (up_ren r)); eauto.
    - apply shift_preserves_bijection; auto.
    - intro H_fv. apply H2. apply fv_cut_r; auto.
  + eapply (H (S n) (up_ren r)); eauto.
    - apply shift_preserves_bijection; auto.
    - intro H_fv. apply H2. apply fv_seq_l; auto.
  + eapply (H0 n r); eauto.
    intro H_fv. apply H2. apply fv_seq_r; auto.
  + apply H0. simpl in H_nfv.
    destruct H.
    assert (g (r n0) = g (r n)).
    { f_equal; assumption. }
    repeat rewrite c in H; subst.
    destruct (H0 (fv_future n)).
  + eapply (H n r); eauto.
    intro H_fv. apply H1. apply fv_prefix; auto.
  + eapply (H (S n) (up_ren r)); eauto.
    - apply shift_preserves_bijection; auto.
    - intro H_fv. apply H1. apply fv_choose_left; auto.
  + eapply (H (S n) (up_ren r)); eauto.
    - apply shift_preserves_bijection; auto.
    - intro H_fv. apply H1. apply fv_choose_right; auto.
  + eapply (H (S n) (up_ren r)); eauto.
    - apply shift_preserves_bijection; auto.
    - intro H_fv. apply H2. apply fv_choice_l; auto.
  + eapply (H0 (S n) (up_ren r)); eauto.
    - apply shift_preserves_bijection; auto.
    - intro H_fv. apply H2. apply fv_choice_r; auto.
  + eapply (H (S n) (up_ren r)); eauto.
    - apply shift_preserves_bijection; auto.
    - intro H_fv. apply H2. apply fv_send_l; auto.
  + eapply (H0 (S n) (up_ren r)); eauto.
    - apply shift_preserves_bijection; auto.
    - intro H_fv. apply H2. apply fv_send_r; auto.
  + eapply (H (S (S n)) (up_ren (up_ren r))); eauto.
    - repeat apply shift_preserves_bijection; auto.
    - intro H_fv. apply H1. apply fv_receive; auto.
  + eapply (H n r); eauto.
    intro H_fv. apply H1. apply fv_wait; auto.
Qed.

(* TODO: lift_process p n k -> ~ (n ∈ p) *)
