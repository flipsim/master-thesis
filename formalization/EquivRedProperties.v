From FD Require Import Syntax.
From FD Require Import Reduction.
From FD Require Import FreeVars.
From FD Require Import Renaming.
From FD Require Import FreeVars.
From FD Require Import StructCong.
From FD Require Import Contexts.
From FD Require Import Typing.
From FD Require Import Preservation.
From FD Require Import ConfluenceDefs.
From FD Require Import DirectedCong.
From FD Require Import AxCutCtx.
From FD Require Import ParallelReduction.

From Stdlib Require Import Lia.
From Stdlib Require Import Arith.Wf_nat.

Local Hint Rewrite
  swap_swap_id
  down_after_up_process_id
  up_after_down_process_id
  up_ren_swap_swap_idM
  up_ren_swap_swap_idE
  swap_swap_idE
  down_after_up_idE
    : up_down_rename_rewrites.

(******************************************************************************)
(* up_subst_n                                                                 *)
(******************************************************************************)
(* Definition for up_subst_n is in DirectedCongruence.v *)
(* Here are some more helpful lemmata about it *)

Lemma up_subst_Sn :
  forall j σ, up_subst (up_subst_n j σ) = up_subst_n (S j) σ.
Proof. auto. Qed.

Lemma substitutions_compose :
  (forall P σ1 σ2,
    subst_process (subst_process P σ1) σ2
      = subst_process P (fun x => subst_message (σ1 x) σ2)) /\
  (forall M σ1 σ2,
    subst_message (subst_message M σ1) σ2
      = subst_message M (fun x => subst_message (σ1 x) σ2)) /\
  (forall s σ1 σ2,
    subst_statement (subst_statement s σ1) σ2
      = subst_statement s (fun x => subst_message (σ1 x) σ2)).
Proof.
  apply syntax_ind; intros; simpl;
  try assert (
    forall x,
      (fun x : nat => subst_message (up_subst σ1 x) (up_subst σ2)) x
       = (up_subst (fun x : nat => subst_message (σ1 x) σ2)) x
  ) by (
    intros [|]; auto; simpl;
    replace (up_subst σ2) with (up_subst_n 1 σ2) by auto;
    unfold upM; rewrite (proj1 (proj2 subst_up_lift_commute)); auto
  );
  try rewrite H; try rewrite H0; auto; f_equal; apply subst_extensional; auto.
  intros [|[|]]; auto; simpl. unfold upM.
  replace (up_subst (up_subst σ2)) with (up_subst_n 1 (up_subst σ2)) by auto.
  rewrite (proj1 (proj2 subst_up_lift_commute)); simpl.
  replace (up_subst σ2) with (up_subst_n 1 σ2) by auto.
  rewrite (proj1 (proj2 subst_up_lift_commute)).
  auto.
Qed.

Lemma up_subst_n_additive :
  forall n1 n2 σ,
    up_subst_n n1 (up_subst_n n2 σ) = up_subst_n (n1 + n2) σ.
Proof.
  induction n1; intros; simpl; auto. rewrite IHn1. auto.
Qed.

Lemma well_formedness_under_up_subst :
  forall E j n σ,
    well_formed_axcut_ctx j E ->
    j < n ->
    well_formed_axcut_ctx j (subst_ctx E (up_subst_n n σ)).
Proof.
  induction E; intros; auto; simpl; econstructor;
  replace (up_subst (up_subst_n n σ)) with (up_subst_n (S n) σ) by auto.
  + eapply nfv_under_substitution_extensional; intros.
    destruct (Compare_dec.lt_dec n0 (S n)).
    - rewrite up_subst_n_lt; auto.
      intro. inversion H2; subst. inversion H. congruence.
    - rewrite up_subst_n_ge; try lia.
      apply nfv_lift_n. lia.
  + apply IHE; try lia. inversion H; auto.
  + eapply nfv_under_substitution_extensional; intros.
    destruct (Compare_dec.lt_dec n0 (S n)).
    - rewrite up_subst_n_lt; auto.
      intro. inversion H2; subst. inversion H. congruence.
    - rewrite up_subst_n_ge; try lia.
      apply nfv_lift_n. lia.
  + apply IHE; try lia. inversion H; auto.
Qed.

Lemma down_after_lift_Sk_lift_k :
  (forall P, forall n1 n2 k, n1 <= n2 -> n2 <= n1 + k ->
    down1_process (lift_process P n1 (S k)) n2 = lift_process P n1 k)
  /\
  (forall M, forall n1 n2 k, n1 <= n2 -> n2 <= n1 + k ->
    down1_message (lift_message M n1 (S k)) n2 = lift_message M n1 k)
  /\
  (forall s, forall n1 n2 k, n1 <= n2 -> n2 <= n1 + k ->
    down1_statement (lift_statement s n1 (S k)) n2 = lift_statement s n1 k).
Proof.
  apply syntax_ind; intros; simpl; auto;
  try (now (rewrite H; try rewrite H0; auto; try lia)).
  unfold relocate.
  destruct (Nat.leb n1 n) eqn:E.
  + apply PeanoNat.Nat.leb_le in E.
    assert (n2 < (S k + n)) by lia.
    apply PeanoNat.Nat.ltb_lt in H1; rewrite H1; auto.
  + apply PeanoNat.Nat.leb_nle in E.
    assert (~ n2 < n) by lia.
    apply PeanoNat.Nat.ltb_nlt in H1; rewrite H1; auto.
Qed.

Lemma up_subst_down_commute :
  (forall P, forall σ k j,
    ~ (j ∈ P) -> j <= k ->
    down1_process (subst_process P (up_subst_n (S k) σ)) j =
    subst_process (down1_process P j) (up_subst_n k σ)) /\
  (forall M, forall σ k j,
    ~ (occurs_free_message j M) -> j <= k ->
    down1_message (subst_message M (up_subst_n (S k) σ)) j =
    subst_message (down1_message M j) (up_subst_n k σ)) /\
  (forall s, forall σ k j,
    ~ (occurs_free_statement j s) -> j <= k ->
    down1_statement (subst_statement s (up_subst_n (S k) σ)) j =
    subst_statement (down1_statement s j) (up_subst_n k σ)).
Proof.
  apply syntax_ind; intros; simpl;
  try replace (up_subst (up_subst_n k σ)) with (up_subst_n (S k) σ) by auto;
  try replace (up_subst (up_subst_n (S k) σ)) with (up_subst_n (S (S k)) σ) by auto;
  try (now (try rewrite H; try rewrite H0; auto; try lia; intro Hfv; try apply H1; try apply H0; free_var_econstructor; eauto)).
  + assert (j <> n). { intro. apply H; subst. free_var_econstructor; eauto. }
    destruct (Nat.ltb j n) eqn:E.
    - apply PeanoNat.Nat.ltb_lt in E. destruct n; try (exfalso; lia); simpl.
      destruct (Nat.ltb n k) eqn:E1.
      * apply PeanoNat.Nat.ltb_lt in E1.
        rewrite up_subst_n_lt; auto; simpl.
        unfold relocate; simpl. apply PeanoNat.Nat.ltb_lt in E; rewrite E.
        auto.
      * apply PeanoNat.Nat.ltb_nlt in E1.
        rewrite up_subst_n_ge; try lia.
        unfold upM.
        rewrite (proj1 (proj2 shift_additive)).
        rewrite PeanoNat.Nat.add_1_r.
        rewrite (proj1 (proj2 down_after_lift_Sk_lift_k)); auto. lia.
    - apply PeanoNat.Nat.ltb_nlt in E.
      rewrite up_subst_n_lt; try lia; simpl.
      apply PeanoNat.Nat.ltb_nlt in E; rewrite E.
      rewrite up_subst_n_lt; auto.
      apply PeanoNat.Nat.ltb_nlt in E; lia.
  + replace (up_subst (up_subst_n (S (S k)) σ)) with (up_subst_n (S (S (S k))) σ) by auto.
    rewrite H; auto. intro Hfv. apply H0. free_var_econstructor. auto. lia.
Qed.

Lemma up_subst_lift_commute :
  (forall P, forall σ k j,
    j <= k ->
    lift_process (subst_process P (up_subst_n k σ)) j 1 =
    subst_process (lift_process P j 1) (up_subst_n (S k) σ)) /\
  (forall M, forall σ k j,
    j <= k ->
    lift_message (subst_message M (up_subst_n k σ)) j 1 =
    subst_message (lift_message M j 1) (up_subst_n (S k) σ)) /\
  (forall s, forall σ k j,
    j <= k ->
    lift_statement (subst_statement s (up_subst_n k σ)) j 1 =
    subst_statement (lift_statement s j 1) (up_subst_n (S k) σ)).
Proof.
  apply syntax_ind; intros; simpl;
  try replace (up_subst (up_subst_n k σ)) with (up_subst_n (S k) σ) by auto;
  try replace (up_subst (up_subst_n (S k) σ)) with (up_subst_n (S (S k)) σ) by auto;
  try (now (try rewrite H; try rewrite H0; auto; try lia; intro Hfv; try apply H1; try apply H0; free_var_econstructor; eauto)).
  destruct (Compare_dec.lt_dec n k).
  - rewrite up_subst_n_lt; auto.
    unfold relocate. destruct (Nat.leb j n) eqn:E; simpl.
    * unfold relocate. rewrite E. rewrite up_subst_n_lt; auto.
    * unfold relocate. rewrite E. rewrite up_subst_Sn.
      rewrite up_subst_n_lt; auto.
  - rewrite up_subst_n_ge; try lia.
    unfold relocate.
    assert (j <= n) by lia. apply PeanoNat.Nat.leb_le in H0; rewrite H0; simpl.
    rewrite up_subst_n_ge; try lia. unfold upM.
    rewrite (proj1 (proj2 shift_shift_raise_bound)); try lia; simpl.
    rewrite (proj1 (proj2 shift_shift_raise_bound)) with (n2 := 0); try lia.
    auto.
Qed.

(******************************************************************************)
(* Substitution and evaluation contexts                                       *)
(******************************************************************************)
Lemma subst_ctx_preserves_length :
  forall E σ,
    length_axcut_ctx (subst_ctx E σ) = length_axcut_ctx E.
Proof.
  induction E; intros; simpl; auto.
Qed.

Lemma subst_over_fill_hole :
  forall E M j σ,
    well_formed_axcut_ctx j E ->
    σ j = future j ->
    subst_process (fill_hole E M) σ
      = fill_hole (subst_ctx E σ) (subst_message M (up_subst_n (length_axcut_ctx E) σ)).
Proof.
  induction E; intros; simpl.
  + inversion H; subst. rewrite H0; auto.
  + inversion H; subst. rewrite H0; auto.
  + f_equal. rewrite IHE with (j := S j).
    - f_equal; f_equal.
      replace (up_subst σ) with (up_subst_n 1 σ) by auto.
      rewrite up_subst_n_additive. rewrite PeanoNat.Nat.add_1_r.
      auto.
    - inversion H; auto.
    - simpl. rewrite H0. auto.
  + f_equal. rewrite IHE with (j := S j).
    - f_equal; f_equal.
      replace (up_subst σ) with (up_subst_n 1 σ) by auto.
      rewrite up_subst_n_additive. rewrite PeanoNat.Nat.add_1_r.
      auto.
    - inversion H; auto.
    - simpl. rewrite H0. auto.
Qed.

Lemma ren_subst_ctx_commute :
  forall E, forall r σ k,
    bijective r -> (forall j, j >= k -> r j = j) ->
    (forall j, j < k -> (σ j) = (future j)) ->
    (forall j, j >= k -> (rename_message (σ j) r) = (σ j)) ->
    subst_ctx (rename_axcut_ctx E r) σ
      = rename_axcut_ctx (subst_ctx E σ) r.
Proof.
  induction E; intros; simpl; auto.
  + assert (
      forall j : nat, j >= (S k) -> up_ren r j = j
    ).
    { intros [|] ?; auto; simpl. rewrite H0; auto; lia. }
    assert (
      forall j : nat, j < S k -> up_subst σ j = future j
    ).
    {
      intros [|] ?; auto; simpl. rewrite H1; simpl; auto; lia.
    }
    assert (
      forall j : nat, j >= S k -> rename_message (up_subst σ j) (up_ren r) = up_subst σ j
    ).
    {
      intros [|] ?; auto; simpl.
      unfold upM.
      rewrite (proj1 (proj2 ren_up_up_ren_commute)); auto.
      + rewrite H2; auto; lia.
      + intros; exfalso; lia.
    }
    assert (
      bijective (up_ren r)
    ) by (apply shift_preserves_bijection; auto).
    erewrite IHE; eauto. erewrite (proj1 ren_subst_commute); eauto.
  + assert (
      forall j : nat, j >= (S k) -> up_ren r j = j
    ).
    { intros [|] ?; auto; simpl. rewrite H0; auto; lia. }
    assert (
      forall j : nat, j < S k -> up_subst σ j = future j
    ).
    {
      intros [|] ?; auto; simpl. rewrite H1; simpl; auto; lia.
    }
    assert (
      forall j : nat, j >= S k -> rename_message (up_subst σ j) (up_ren r) = up_subst σ j
    ).
    {
      intros [|] ?; auto; simpl.
      unfold upM.
      rewrite (proj1 (proj2 ren_up_up_ren_commute)); auto.
      + rewrite H2; auto; lia.
      + intros; exfalso; lia.
    }
    assert (
      bijective (up_ren r)
    ) by (apply shift_preserves_bijection; auto).
    erewrite IHE; eauto. erewrite (proj1 ren_subst_commute); eauto.
Qed.

Lemma up_subst_n_over_reduce_axcut' :
  forall n E M P j σ,
    n = length_axcut_ctx E ->
    well_formed_axcut_ctx 0 E ->
    ~ (occurs_free_message (length_axcut_ctx E) M) ->
    subst_process (reduce_axcut E M P) (up_subst_n j σ) =
    reduce_axcut
      (subst_ctx E (up_subst_n (S j) σ))
      (subst_message M (up_subst_n (length_axcut_ctx E + (S j)) σ))
      (subst_process P (up_subst_n (S j) σ)).
Proof.
  induction n; intros; simpl;
  destruct E; simpl in H; try congruence; simpl.
  + repeat rewrite reduce_axcut_equation_1; simpl.
    repeat rewrite (proj1 substitutions_compose).
    apply subst_extensional.
    intros [|]; simpl.
    - replace (up_subst (up_subst_n j σ)) with (up_subst_n (S j) σ) by auto.
      unfold downM.
      rewrite (proj1 (proj2 up_subst_down_commute)); auto; try lia.
    - rewrite (proj1 (proj2 subst_nfv_down)) with (n := 0).
      * unfold upM. rewrite (proj1 (proj2 down_after_up_id)). auto.
      * apply nfv_lift_n; lia.
      * intros; exfalso; lia.
      * intros; auto.
  + repeat rewrite reduce_axcut_equation_2; simpl.
    repeat rewrite (proj1 substitutions_compose).
    apply subst_extensional.
    intros [|]; simpl.
    - replace (up_subst (up_subst_n j σ)) with (up_subst_n (S j) σ) by auto.
      unfold downM.
      rewrite (proj1 (proj2 up_subst_down_commute)); auto; try lia.
    - rewrite (proj1 (proj2 subst_nfv_down)) with (n := 0).
      * unfold upM. rewrite (proj1 (proj2 down_after_up_id)). auto.
      * apply nfv_lift_n; lia.
      * intros; exfalso; lia.
      * intros; auto.
  + repeat rewrite reduce_axcut_equation_3; simpl.
    f_equal.
    - repeat rewrite up_subst_Sn.
      unfold down.
      replace swap01 with (up_ren_n 0 swap01) by auto. inversion H0; subst.
      repeat rewrite (proj1 up_ren_n_swap_down_down_Sn); auto.
      * rewrite (proj1 up_subst_down_commute); auto. lia.
      * apply nfv_under_substitution_extensional; intros.
        destruct (Compare_dec.lt_dec n0 (S (S j))).
        ** rewrite up_subst_n_lt; auto.
           intro. inversion H3; subst. congruence.
        ** rewrite up_subst_n_ge; try lia. apply nfv_lift_n. lia.
    - replace (up_subst (up_subst_n j σ)) with (up_subst_n (S j) σ) by auto.
      rewrite IHn.
      * f_equal.
        ** rewrite up_subst_Sn.
           apply ren_subst_ctx_commute with (k := S (S j)); try apply swap01_is_bijective.
           ++ intros [|[|]] ?; auto; exfalso; lia.
           ++ intros. rewrite up_subst_n_lt; auto.
           ++ intros. rewrite up_subst_n_ge; try lia.
              rewrite (proj1 (proj2 renaming_idempotent_free_vars)); auto.
              intros. destruct n0 as [|[|]]; auto; exfalso.
              -- assert (
                  ~ occurs_free_message 0 (lift_message (σ (j0 - S (S j))) 0 (S (S j)))
                 ). { apply nfv_lift_n; lia. } congruence.
              -- assert (
                  ~ occurs_free_message 1 (lift_message (σ (j0 - S (S j))) 0 (S (S j)))
                 ). { apply nfv_lift_n; lia. } congruence.
        ** repeat rewrite up_subst_Sn.
           rewrite <- rename_axcut_ctx_preserves_length.
           replace (S (length_axcut_ctx E + S j)) with (length_axcut_ctx E + (S (S j))) by lia.
           rewrite subst_ctx_preserves_length.
           apply (proj1 (proj2 ren_subst_commute)) with (k := length_axcut_ctx E + S (S j)).
           ++ apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
           ++ intros. rewrite up_ren_n_swap_not_nSn; lia.
           ++ intros. rewrite up_subst_n_lt; auto.
           ++ intros. rewrite up_subst_n_ge; try lia.
              rewrite (proj1 (proj2 renaming_idempotent_free_vars)); auto.
              intros. rewrite up_ren_n_swap_not_nSn; auto; intro; subst.
              -- assert (
                  ~ occurs_free_message (length_axcut_ctx E)
                      (lift_message (σ (j0 - (length_axcut_ctx E + S (S j)))) 0 (length_axcut_ctx E + S (S j)))
                 ). { apply nfv_lift_n; lia. } congruence.
              -- assert (
                  ~ occurs_free_message (S (length_axcut_ctx E))
                      (lift_message (σ (j0 - (length_axcut_ctx E + S (S j)))) 0 (length_axcut_ctx E + S (S j)))
                 ). { apply nfv_lift_n; lia. } congruence.
        ** unfold up.
           repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
           rewrite (proj1 up_subst_lift_commute); auto. lia.
      * rewrite <- rename_axcut_ctx_preserves_length; inversion H; auto.
      * replace 0 with (swap01 1) by auto; replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01.
        inversion H0; auto.
      * rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E) with
          (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
          at 1 by (rewrite up_ren_n_swap_Sn; auto).
        apply (proj1 (proj2 nfv_under_renaming)).
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        assumption.
  + repeat rewrite reduce_axcut_equation_4; simpl.
    f_equal.
    - replace (up_subst (up_subst_n j σ)) with (up_subst_n (S j) σ) by auto.
      rewrite IHn.
      * f_equal.
        ** rewrite up_subst_Sn.
           apply ren_subst_ctx_commute with (k := S (S j)); try apply swap01_is_bijective.
           ++ intros [|[|]] ?; auto; exfalso; lia.
           ++ intros. rewrite up_subst_n_lt; auto.
           ++ intros. rewrite up_subst_n_ge; try lia.
              rewrite (proj1 (proj2 renaming_idempotent_free_vars)); auto.
              intros. destruct n0 as [|[|]]; auto; exfalso.
              -- assert (
                  ~ occurs_free_message 0 (lift_message (σ (j0 - S (S j))) 0 (S (S j)))
                 ). { apply nfv_lift_n; lia. } congruence.
              -- assert (
                  ~ occurs_free_message 1 (lift_message (σ (j0 - S (S j))) 0 (S (S j)))
                 ). { apply nfv_lift_n; lia. } congruence.
        ** repeat rewrite up_subst_Sn.
           rewrite <- rename_axcut_ctx_preserves_length.
           replace (S (length_axcut_ctx E + S j)) with (length_axcut_ctx E + (S (S j))) by lia.
           rewrite subst_ctx_preserves_length.
           apply (proj1 (proj2 ren_subst_commute)) with (k := length_axcut_ctx E + S (S j)).
           ++ apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
           ++ intros. rewrite up_ren_n_swap_not_nSn; lia.
           ++ intros. rewrite up_subst_n_lt; auto.
           ++ intros. rewrite up_subst_n_ge; try lia.
              rewrite (proj1 (proj2 renaming_idempotent_free_vars)); auto.
              intros. rewrite up_ren_n_swap_not_nSn; auto; intro; subst.
              -- assert (
                  ~ occurs_free_message (length_axcut_ctx E)
                      (lift_message (σ (j0 - (length_axcut_ctx E + S (S j)))) 0 (length_axcut_ctx E + S (S j)))
                 ). { apply nfv_lift_n; lia. } congruence.
              -- assert (
                  ~ occurs_free_message (S (length_axcut_ctx E))
                      (lift_message (σ (j0 - (length_axcut_ctx E + S (S j)))) 0 (length_axcut_ctx E + S (S j)))
                 ). { apply nfv_lift_n; lia. } congruence.
        ** unfold up.
           repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
           rewrite (proj1 up_subst_lift_commute); auto. lia.
      * rewrite <- rename_axcut_ctx_preserves_length; inversion H; auto.
      * replace 0 with (swap01 1) by auto; replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01.
        inversion H0; auto.
      * rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E) with
          (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
          at 1 by (rewrite up_ren_n_swap_Sn; auto).
        apply (proj1 (proj2 nfv_under_renaming)).
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        assumption.
    - repeat rewrite up_subst_Sn.
      unfold down.
      replace swap01 with (up_ren_n 0 swap01) by auto. inversion H0; subst.
      repeat rewrite (proj1 up_ren_n_swap_down_down_Sn); auto.
      * rewrite (proj1 up_subst_down_commute); auto. lia.
      * apply nfv_under_substitution_extensional; intros.
        destruct (Compare_dec.lt_dec n0 (S (S j))).
        ** rewrite up_subst_n_lt; auto.
           intro. inversion H3; subst. congruence.
        ** rewrite up_subst_n_ge; try lia. apply nfv_lift_n. lia.
Qed.

Lemma up_subst_n_over_reduce_axcut :
  forall E M P j σ,
    well_formed_axcut_ctx 0 E ->
    ~ (occurs_free_message (length_axcut_ctx E) M) ->
    subst_process (reduce_axcut E M P) (up_subst_n j σ) =
    reduce_axcut
      (subst_ctx E (up_subst_n (S j) σ))
      (subst_message M (up_subst_n (length_axcut_ctx E + (S j)) σ))
      (subst_process P (up_subst_n (S j) σ)).
Proof.
  intros; eapply up_subst_n_over_reduce_axcut'; auto.
Qed.

(******************************************************************************)
(* Lemmata for Confluence                                                     *)
(******************************************************************************)
Lemma equiv_red_invariant_under_substitution :
  forall Γ P P' σ, Γ ⊢ P :# -> P ⊵ P' ->
    (subst_process P σ) ⊵ (subst_process P' σ).
Proof.
  intros.
  generalize dependent σ.
  generalize dependent Γ.
  induction H0; intros; simpl;
  try (now econstructor).
  + econstructor. rewrite H. unfold up.
    repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
    replace (up_subst σ) with (up_subst_n 1 σ) by auto.
    rewrite <- (proj1 subst_up_lift_commute).
    reflexivity.
  + econstructor. rewrite H. unfold up.
    repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
    replace (up_subst σ) with (up_subst_n 1 σ) by auto.
    rewrite <- (proj1 subst_up_lift_commute).
    reflexivity.
  + rewrite H. rewrite subst_over_fill_hole with (j := 0); auto.
    rewrite H1. replace σ with (up_subst_n 0 σ) at 4 by auto.
    rewrite up_subst_n_over_reduce_axcut; auto; simpl.
    - assert (
        up_subst_n (length_axcut_ctx E) (up_subst σ)
          = up_subst_n (length_axcut_ctx E + 1) σ
      ).
      { replace (up_subst σ) with (up_subst_n 1 σ) by auto. rewrite up_subst_n_additive. auto. }
      rewrite H3.
      eapply rp_ax_cut_l; eauto.
      replace (up_subst σ) with (up_subst_n 1 σ) by auto.
      apply well_formedness_under_up_subst; auto.
    - inversion H2; subst.
      replace (length_axcut_ctx E) with (length_axcut_ctx E + 0) by lia.
      apply (nfv_well_typed_fill_hole _ _ _ _ H0 H7).
  + rewrite H. rewrite subst_over_fill_hole with (j := 0); auto.
    rewrite H1. replace σ with (up_subst_n 0 σ) at 4 by auto.
    rewrite up_subst_n_over_reduce_axcut; auto; simpl.
    - assert (
        up_subst_n (length_axcut_ctx E) (up_subst σ)
          = up_subst_n (length_axcut_ctx E + 1) σ
      ).
      { replace (up_subst σ) with (up_subst_n 1 σ) by auto. rewrite up_subst_n_additive. auto. }
      rewrite H3.
      eapply rp_ax_cut_r; eauto.
      replace (up_subst σ) with (up_subst_n 1 σ) by auto.
      apply well_formedness_under_up_subst; auto.
    - inversion H2; subst.
      replace (length_axcut_ctx E) with (length_axcut_ctx E + 0) by lia.
      apply (nfv_well_typed_fill_hole _ _ _ _ H0 H8).
  + assert (
      subst_process (subst_process P (prefix s ⋅ id_subst)) σ
        = subst_process (subst_process P (up_subst σ)) (prefix (subst_statement s σ) ⋅ id_subst)
    ).
    {
      repeat rewrite (proj1 substitutions_compose).
      apply subst_extensional.
      intros [|]; auto; simpl.
      rewrite (proj1 (proj2 subst_nfv_down)) with (n := 0).
      + unfold upM. rewrite (proj1 (proj2 down_after_up_id)); auto.
      + apply nfv_lift_n; lia.
      + intros; exfalso; lia.
      + auto.
    }
    rewrite H0. econstructor.
  + apply rp_cong_cut_l. inversion H; subst. eapply IHequiv_reduces; eauto.
  + apply rp_cong_cut_r. inversion H; subst. eapply IHequiv_reduces; eauto.
  + apply rp_cong_seq. inversion H; subst. eapply IHequiv_reduces; eauto.
Qed.

Lemma reduce_axcut_invariant_under_reduced_substituent' :
  forall n Γ E M P P',
    n = length_axcut_ctx E ->
    Γ ⊢ P :# -> P ⊵ P' ->
    reduce_axcut E M P ⊵ reduce_axcut E M P'.
Proof.
  induction n; intros; destruct E; simpl in H; try congruence.
  + repeat rewrite reduce_axcut_equation_1.
    eapply equiv_red_invariant_under_substitution; eauto.
  + repeat rewrite reduce_axcut_equation_2.
    eapply equiv_red_invariant_under_substitution; eauto.
  + repeat rewrite reduce_axcut_equation_3.
    apply rp_cong_cut_r.
    assert (
      exists Γ', Γ' ⊢ up P :#
    ).
    {
      unfold up.
      replace Γ with (nil ++ Γ) in H0 by auto.
      apply (proj1 up_shift_sound) in H0.
      eexists; eassumption.
    }
    destruct H2 as [Γ1 ?].
    assert (
      exists Γ', Γ' ⊢ rename_process (up P) swap01 :#
    ).
    {
      destruct (swap01_preserves_well_typedness _ _ H2).
      eexists; eauto.
    }
    destruct H3 as [Γ2 ?].
    eapply IHn; eauto.
    - rewrite <- rename_axcut_ctx_preserves_length.
      inversion H; auto.
    - replace swap01 with (up_ren_n 0 swap01) by auto.
      eapply equiv_red_invariant_under_swap; eauto.
      eapply equiv_red_invariant_under_up; eauto.
  + repeat rewrite reduce_axcut_equation_4.
    apply rp_cong_cut_l.
    assert (
      exists Γ', Γ' ⊢ up P :#
    ).
    {
      unfold up.
      replace Γ with (nil ++ Γ) in H0 by auto.
      apply (proj1 up_shift_sound) in H0.
      eexists; eassumption.
    }
    destruct H2 as [Γ1 ?].
    assert (
      exists Γ', Γ' ⊢ rename_process (up P) swap01 :#
    ).
    {
      destruct (swap01_preserves_well_typedness _ _ H2).
      eexists; eauto.
    }
    destruct H3 as [Γ2 ?].
    eapply IHn; eauto.
    - rewrite <- rename_axcut_ctx_preserves_length.
      inversion H; auto.
    - replace swap01 with (up_ren_n 0 swap01) by auto.
      eapply equiv_red_invariant_under_swap; eauto.
      eapply equiv_red_invariant_under_up; eauto.
Qed.

Lemma reduce_axcut_invariant_under_reduced_substituent :
  forall Γ E M P P',
    Γ ⊢ P :# -> P ⊵ P' ->
    reduce_axcut E M P ⊵ reduce_axcut E M P'.
Proof. intros. eapply reduce_axcut_invariant_under_reduced_substituent'; eauto. Qed.

Lemma uniqueness_of_evaluation_context :
  forall E E' M M' j Γ,
    well_formed_axcut_ctx j E -> well_formed_axcut_ctx j E' ->
    Γ ⊢ (fill_hole E M) :# ->
    (fill_hole E M) = (fill_hole E' M') ->
    E = E' /\ M = M'.
Proof.
  induction E; intros; destruct E'; simpl in H2; try congruence;
  try (now (inversion H2; subst; auto)).
  + inversion H2; subst. inversion H; inversion H0; subst; split; auto.
    simpl in H1.
    exfalso.
    inversion H1; subst.
    assert (occurs_free_message n0 (future n0)) by econstructor.
    destruct ((proj1 (proj2 free_var_in_ctx)) _ _ H3 _ _ H7).
    destruct ((proj1 (proj2 free_var_in_ctx)) _ _ H3 _ _ H8).
    pose proof (ctx_split_lookup_in_partition _ _ _ _ _ H5 H4). symmetry in H9.
    destruct (decide_ctx_split_partition _ _ _ _ _ H5 H9) as [[? ?] | [? ?]];
    subst; try congruence.
  + inversion H2; subst. inversion H; inversion H0; subst; split; auto.
    simpl in H1.
    exfalso.
    inversion H1; subst.
    assert (occurs_free_message n0 (future n0)) by econstructor.
    destruct ((proj1 (proj2 free_var_in_ctx)) _ _ H3 _ _ H7).
    destruct ((proj1 (proj2 free_var_in_ctx)) _ _ H3 _ _ H8).
    pose proof (ctx_split_lookup_in_partition _ _ _ _ _ H5 H4). symmetry in H9.
    destruct (decide_ctx_split_partition _ _ _ _ _ H5 H9) as [[? ?] | [? ?]];
    subst; try congruence.
  + inversion H2; subst. inversion H. inversion H0; subst.
    simpl in H1; inversion H1; subst.
    eapply IHE in H5; eauto. destruct H5; subst; split; auto.
  + exfalso.
    inversion H2; subst. simpl in H1. inversion H1; subst.
    simpl in H; inversion H; subst.
    simpl in H0; inversion H0; subst.
    pose proof (well_formed_ctx_fv _ _ H10).
    pose proof (well_formed_ctx_fv _ _ H12).
    apply (fv_ctx_fill_hole _ _ M) in H3.
    apply (fv_ctx_fill_hole _ _ M') in H4.
    destruct ((proj1 free_var_in_ctx) _ _ H3 _ H8).
    destruct ((proj1 free_var_in_ctx) _ _ H4 _ H7).
    simpl in H6, H13.
    pose proof (ctx_split_lookup_in_partition _ _ _ _ _ H5 H13). symmetry in H14.
    destruct (decide_ctx_split_partition _ _ _ _ _ H5 H14) as [[? ?] | [? ?]];
    subst; congruence.
  + exfalso.
    inversion H2; subst. simpl in H1. inversion H1; subst.
    simpl in H; inversion H; subst.
    simpl in H0; inversion H0; subst.
    pose proof (well_formed_ctx_fv _ _ H10).
    pose proof (well_formed_ctx_fv _ _ H12).
    apply (fv_ctx_fill_hole _ _ M) in H3.
    apply (fv_ctx_fill_hole _ _ M') in H4.
    destruct ((proj1 free_var_in_ctx) _ _ H3 _ H7).
    destruct ((proj1 free_var_in_ctx) _ _ H4 _ H8).
    simpl in H6, H13.
    pose proof (ctx_split_lookup_in_partition _ _ _ _ _ H5 H6). symmetry in H14.
    destruct (decide_ctx_split_partition _ _ _ _ _ H5 H14) as [[? ?] | [? ?]];
    subst; congruence.
  + inversion H2; subst. inversion H. inversion H0; subst.
    simpl in H1; inversion H1; subst.
    eapply IHE in H4; eauto. destruct H4; subst; split; auto.
Qed.

(******************************************************************************)
(* Confluence for Critical Pairs                                              *)
(******************************************************************************)
Lemma confluence_critical_pairs' :
  forall n m E E' M M',
    n = length_axcut_ctx E  ->
    m = length_axcut_ctx E' ->
    well_formed_axcut_ctx 0 E  ->
    well_formed_axcut_ctx 0 E' ->
    ~ (occurs_free_message (length_axcut_ctx E) M) ->
    ~ (occurs_free_message (length_axcut_ctx E') M') ->
    (reduce_axcut E M (fill_hole E' M')) ≡ (reduce_axcut E' M' (fill_hole E M)).
Proof.
  intros n m. pattern n, m.
  apply lt_wf_double_ind.
  intros.
  destruct n0, m0.
  + destruct E, E'; simpl in *; try congruence;
    repeat rewrite reduce_axcut_equation_1; simpl;
    repeat rewrite reduce_axcut_equation_2; simpl;
    inversion H3; inversion H4; subst; simpl;
    rewrite (proj1 (proj2 subst_nfv_down)) with (n := 0); auto;
    try rewrite (proj1 (proj2 subst_nfv_down)) with (n := 0); auto;
    try apply c_link; try apply c_refl; try (intros; exfalso; lia).
  + destruct E, E'; simpl in *; try congruence.
    - assert (
        (cut (down (rename_process P swap01))
             (reduce_axcut
               (rename_axcut_ctx (upE (nil_l n0)) swap01)
               (rename_message (upM M) swap01)
               (rename_process (fill_hole E' M') swap01)))
        ≡ (reduce_axcut (nil_l n0) M (cut P (fill_hole E' M')))
      ).
      {
        inversion H3; inversion H4; subst.
        eapply c_trans.
        + apply permute_cut_assoc_reduce_axcut; simpl; auto.
          - intro. inversion H7.
          - replace 0 with (swap01 1) by auto; apply nfv_under_renaming.
            apply swap01_is_bijective. unfold upM.
            intro. apply fv_up_Sn2' in H7. congruence. lia.
          - replace 1 with (swap01 0) by auto; apply nfv_under_renaming.
            apply swap01_is_bijective. apply nfv_lift_n. lia.
        + simpl. apply c_refl_inversion_eq. f_equal.
          - rewrite swap_swap_idM.
            unfold upM. rewrite (proj1 (proj2 down_after_up_id)). reflexivity.
          - rewrite swap_swap_id. f_equal. unfold down, up.
            rewrite (proj1 up_after_down_id).
            rewrite swap_swap_id; auto.
            apply nfv_01_swap; auto.
      }
      eapply c_trans. { apply c_comm. apply H7. }
      rewrite reduce_axcut_equation_3. apply c_cong_cut. apply c_refl.
      replace (rename_process (up (link (future n0) M)) swap01)
         with (rename_process (up (fill_hole (nil_l n0) M)) swap01)
           by auto.
      unfold up. rewrite up_ctx_over_fill_hole.
      repeat rewrite rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
      rewrite <- plus_n_O.
      inversion H3; inversion H4; subst.
      eapply H0; eauto.
      * rewrite <- rename_axcut_ctx_preserves_length. inversion H2; auto.
      * replace 0 with (swap01 1) by auto;
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; auto.
      * simpl. replace 0 with (swap01 1) by auto; apply nfv_under_renaming; try apply swap01_is_bijective.
        simpl. intro. apply fv_up_Sn2' in H8. congruence. lia.
      * rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E')
           with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
             at 1 by (rewrite up_ren_n_swap_Sn; auto).
        apply (proj1 (proj2 nfv_under_renaming)).
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        congruence.
    - assert (
        (cut (down (rename_process P swap01))
             (reduce_axcut
               (rename_axcut_ctx (upE (nil_l n0)) swap01)
               (rename_message (upM M) swap01)
               (rename_process (fill_hole E' M') swap01)))
        ≡ (reduce_axcut (nil_l n0) M (cut P (fill_hole E' M')))
      ).
      {
        inversion H3; inversion H4; subst.
        eapply c_trans.
        + apply permute_cut_assoc_reduce_axcut; simpl; auto.
          - intro. inversion H7.
          - replace 0 with (swap01 1) by auto; apply nfv_under_renaming.
            apply swap01_is_bijective. unfold upM.
            intro. apply fv_up_Sn2' in H7. congruence. lia.
          - replace 1 with (swap01 0) by auto; apply nfv_under_renaming.
            apply swap01_is_bijective. apply nfv_lift_n. lia.
        + simpl. apply c_refl_inversion_eq. f_equal.
          - rewrite swap_swap_idM.
            unfold upM. rewrite (proj1 (proj2 down_after_up_id)). reflexivity.
          - rewrite swap_swap_id. f_equal. unfold down, up.
            rewrite (proj1 up_after_down_id).
            rewrite swap_swap_id; auto.
            apply nfv_01_swap; auto.
      }
      assert (
        (reduce_axcut (nil_l n0) M (cut P (fill_hole E' M')))
        ≡ (reduce_axcut (nil_l n0) M (cut (fill_hole E' M') P))
      ).
      { repeat rewrite reduce_axcut_equation_1; simpl. apply c_cut_comm. }
      eapply c_trans. { apply c_comm. apply H8. }
      eapply c_trans. { apply c_comm. apply H7. }
      rewrite reduce_axcut_equation_4. eapply c_trans. apply c_cut_comm.
      apply c_cong_cut; try apply c_refl.
      replace (rename_process (up (link (future n0) M)) swap01)
         with (rename_process (up (fill_hole (nil_l n0) M)) swap01)
           by auto.
      unfold up. rewrite up_ctx_over_fill_hole.
      repeat rewrite rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
      rewrite <- plus_n_O.
      inversion H3; inversion H4; subst.
      eapply H0; eauto.
      * rewrite <- rename_axcut_ctx_preserves_length. inversion H2; auto.
      * replace 0 with (swap01 1) by auto;
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; auto.
      * simpl. replace 0 with (swap01 1) by auto; apply nfv_under_renaming; try apply swap01_is_bijective.
        simpl. intro. apply fv_up_Sn2' in H9. congruence. lia.
      * rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E')
           with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
             at 1 by (rewrite up_ren_n_swap_Sn; auto).
        apply (proj1 (proj2 nfv_under_renaming)).
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        congruence.
    - assert (
        (cut (down (rename_process P swap01))
             (reduce_axcut
               (rename_axcut_ctx (upE (nil_r n0)) swap01)
               (rename_message (upM M) swap01)
               (rename_process (fill_hole E' M') swap01)))
        ≡ (reduce_axcut (nil_r n0) M (cut P (fill_hole E' M')))
      ).
      {
        inversion H3; inversion H4; subst.
        eapply c_trans.
        + apply permute_cut_assoc_reduce_axcut; simpl; auto.
          - intro. inversion H7.
          - replace 0 with (swap01 1) by auto; apply nfv_under_renaming.
            apply swap01_is_bijective. unfold upM.
            intro. apply fv_up_Sn2' in H7. congruence. lia.
          - replace 1 with (swap01 0) by auto; apply nfv_under_renaming.
            apply swap01_is_bijective. apply nfv_lift_n. lia.
        + simpl. apply c_refl_inversion_eq. f_equal.
          - rewrite swap_swap_idM.
            unfold upM. rewrite (proj1 (proj2 down_after_up_id)). reflexivity.
          - rewrite swap_swap_id. f_equal. unfold down, up.
            rewrite (proj1 up_after_down_id).
            rewrite swap_swap_id; auto.
            apply nfv_01_swap; auto.
      }
      eapply c_trans. { apply c_comm. apply H7. }
      rewrite reduce_axcut_equation_3.
      apply c_cong_cut; try apply c_refl.
      replace (rename_process (up (link M (future n0))) swap01)
         with (rename_process (up (fill_hole (nil_r n0) M)) swap01)
           by auto.
      unfold up. rewrite up_ctx_over_fill_hole.
      repeat rewrite rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
      rewrite <- plus_n_O.
      inversion H3; inversion H4; subst.
      eapply H0; eauto.
      * rewrite <- rename_axcut_ctx_preserves_length. inversion H2; auto.
      * replace 0 with (swap01 1) by auto;
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; auto.
      * simpl. replace 0 with (swap01 1) by auto; apply nfv_under_renaming; try apply swap01_is_bijective.
        simpl. intro. apply fv_up_Sn2' in H8. congruence. lia.
      * rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E')
           with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
             at 1 by (rewrite up_ren_n_swap_Sn; auto).
        apply (proj1 (proj2 nfv_under_renaming)).
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        congruence.
    - assert (
        (cut (down (rename_process P swap01))
             (reduce_axcut
               (rename_axcut_ctx (upE (nil_r n0)) swap01)
               (rename_message (upM M) swap01)
               (rename_process (fill_hole E' M') swap01)))
        ≡ (reduce_axcut (nil_r n0) M (cut P (fill_hole E' M')))
      ).
      {
        inversion H3; inversion H4; subst.
        eapply c_trans.
        + apply permute_cut_assoc_reduce_axcut; simpl; auto.
          - intro. inversion H7.
          - replace 0 with (swap01 1) by auto; apply nfv_under_renaming.
            apply swap01_is_bijective. unfold upM.
            intro. apply fv_up_Sn2' in H7. congruence. lia.
          - replace 1 with (swap01 0) by auto; apply nfv_under_renaming.
            apply swap01_is_bijective. apply nfv_lift_n. lia.
        + simpl. apply c_refl_inversion_eq. f_equal.
          - rewrite swap_swap_idM.
            unfold upM. rewrite (proj1 (proj2 down_after_up_id)). reflexivity.
          - rewrite swap_swap_id. f_equal. unfold down, up.
            rewrite (proj1 up_after_down_id).
            rewrite swap_swap_id; auto.
            apply nfv_01_swap; auto.
      }
      assert (
        (reduce_axcut (nil_r n0) M (cut P (fill_hole E' M')))
        ≡ (reduce_axcut (nil_r n0) M (cut (fill_hole E' M') P))
      ).
      { repeat rewrite reduce_axcut_equation_2; simpl. apply c_cut_comm. }
      eapply c_trans. { apply c_comm. apply H8. }
      eapply c_trans. { apply c_comm. apply H7. }
      rewrite reduce_axcut_equation_4. eapply c_trans. apply c_cut_comm.
      apply c_cong_cut; try apply c_refl.
      replace (rename_process (up (link M (future n0))) swap01)
         with (rename_process (up (fill_hole (nil_r n0) M)) swap01)
           by auto.
      unfold up. rewrite up_ctx_over_fill_hole.
      repeat rewrite rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
      rewrite <- plus_n_O.
      inversion H3; inversion H4; subst.
      eapply H0; eauto.
      * rewrite <- rename_axcut_ctx_preserves_length. inversion H2; auto.
      * replace 0 with (swap01 1) by auto;
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; auto.
      * simpl. replace 0 with (swap01 1) by auto; apply nfv_under_renaming; try apply swap01_is_bijective.
        simpl. intro. apply fv_up_Sn2' in H9. congruence. lia.
      * rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E')
           with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
             at 1 by (rewrite up_ren_n_swap_Sn; auto).
        apply (proj1 (proj2 nfv_under_renaming)).
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        congruence.
  + destruct E, E'; simpl in *; try congruence.
    - apply c_comm.
       assert (
        (cut (down (rename_process P swap01))
             (reduce_axcut
               (rename_axcut_ctx (upE (nil_l n1)) swap01)
               (rename_message (upM M') swap01)
               (rename_process (fill_hole E M) swap01)))
        ≡ (reduce_axcut (nil_l n1) M' (cut P (fill_hole E M)))
      ).
      {
        inversion H3; inversion H4; subst.
        eapply c_trans.
        + apply permute_cut_assoc_reduce_axcut; simpl; auto.
          - intro. inversion H7.
          - replace 0 with (swap01 1) by auto; apply nfv_under_renaming.
            apply swap01_is_bijective. unfold upM.
            intro. apply fv_up_Sn2' in H7. congruence. lia.
          - replace 1 with (swap01 0) by auto; apply nfv_under_renaming.
            apply swap01_is_bijective. apply nfv_lift_n. lia.
        + simpl. apply c_refl_inversion_eq. f_equal.
          - rewrite swap_swap_idM.
            unfold upM. rewrite (proj1 (proj2 down_after_up_id)). reflexivity.
          - rewrite swap_swap_id. f_equal. unfold down, up.
            rewrite (proj1 up_after_down_id).
            rewrite swap_swap_id; auto.
            apply nfv_01_swap; auto.
      }
      eapply c_trans. { apply c_comm. apply H7. }
      rewrite reduce_axcut_equation_3. apply c_cong_cut. apply c_refl.
      replace (rename_process (up (link (future n1) M')) swap01)
         with (rename_process (up (fill_hole (nil_l n1) M')) swap01)
           by auto.
      unfold up. rewrite up_ctx_over_fill_hole.
      repeat rewrite rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
      rewrite <- plus_n_O.
      inversion H3; inversion H4; subst.
      apply c_comm.
      eapply H; eauto.
      * rewrite <- rename_axcut_ctx_preserves_length. inversion H2; auto.
      * replace 0 with (swap01 1) by auto;
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; auto.
      * rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E)
           with (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
             at 1 by (rewrite up_ren_n_swap_Sn; auto).
        apply (proj1 (proj2 nfv_under_renaming)).
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        congruence.
      * simpl. replace 0 with (swap01 1) by auto; apply nfv_under_renaming; try apply swap01_is_bijective.
        simpl. intro. apply fv_up_Sn2' in H8. congruence. lia.
    - apply c_comm.
      assert (
        (cut (down (rename_process P swap01))
             (reduce_axcut
               (rename_axcut_ctx (upE (nil_r n1)) swap01)
               (rename_message (upM M') swap01)
               (rename_process (fill_hole E M) swap01)))
        ≡ (reduce_axcut (nil_r n1) M' (cut P (fill_hole E M)))
      ).
      {
        inversion H3; inversion H4; subst.
        eapply c_trans.
        + apply permute_cut_assoc_reduce_axcut; simpl; auto.
          - intro. inversion H7.
          - replace 0 with (swap01 1) by auto; apply nfv_under_renaming.
            apply swap01_is_bijective. unfold upM.
            intro. apply fv_up_Sn2' in H7. congruence. lia.
          - replace 1 with (swap01 0) by auto; apply nfv_under_renaming.
            apply swap01_is_bijective. apply nfv_lift_n. lia.
        + simpl. apply c_refl_inversion_eq. f_equal.
          - rewrite swap_swap_idM.
            unfold upM. rewrite (proj1 (proj2 down_after_up_id)). reflexivity.
          - rewrite swap_swap_id. f_equal. unfold down, up.
            rewrite (proj1 up_after_down_id).
            rewrite swap_swap_id; auto.
            apply nfv_01_swap; auto.
      }
      eapply c_trans. { apply c_comm. apply H7. }
      rewrite reduce_axcut_equation_3.
      apply c_cong_cut; try apply c_refl.
      replace (rename_process (up (link M' (future n1))) swap01)
         with (rename_process (up (fill_hole (nil_r n1) M')) swap01)
           by auto.
      unfold up. rewrite up_ctx_over_fill_hole.
      repeat rewrite rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
      rewrite <- plus_n_O.
      inversion H3; inversion H4; subst.
      apply c_comm. eapply H; eauto.
      * rewrite <- rename_axcut_ctx_preserves_length. inversion H2; auto.
      * replace 0 with (swap01 1) by auto;
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; auto.
      * rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E)
           with (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
             at 1 by (rewrite up_ren_n_swap_Sn; auto).
        apply (proj1 (proj2 nfv_under_renaming)).
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        congruence.
      * simpl. replace 0 with (swap01 1) by auto; apply nfv_under_renaming; try apply swap01_is_bijective.
        simpl. intro. apply fv_up_Sn2' in H8. congruence. lia.
    - apply c_comm.
      assert (
        (cut (down (rename_process P swap01))
             (reduce_axcut
               (rename_axcut_ctx (upE (nil_l n1)) swap01)
               (rename_message (upM M') swap01)
               (rename_process (fill_hole E M) swap01)))
        ≡ (reduce_axcut (nil_l n1) M' (cut P (fill_hole E M)))
      ).
      {
        inversion H3; inversion H4; subst.
        eapply c_trans.
        + apply permute_cut_assoc_reduce_axcut; simpl; auto.
          - intro. inversion H7.
          - replace 0 with (swap01 1) by auto; apply nfv_under_renaming.
            apply swap01_is_bijective. unfold upM.
            intro. apply fv_up_Sn2' in H7. congruence. lia.
          - replace 1 with (swap01 0) by auto; apply nfv_under_renaming.
            apply swap01_is_bijective. apply nfv_lift_n. lia.
        + simpl. apply c_refl_inversion_eq. f_equal.
          - rewrite swap_swap_idM.
            unfold upM. rewrite (proj1 (proj2 down_after_up_id)). reflexivity.
          - rewrite swap_swap_id. f_equal. unfold down, up.
            rewrite (proj1 up_after_down_id).
            rewrite swap_swap_id; auto.
            apply nfv_01_swap; auto.
      }
      assert (
        (reduce_axcut (nil_l n1) M' (cut P (fill_hole E M)))
        ≡ (reduce_axcut (nil_l n1) M' (cut (fill_hole E M) P))
      ).
      { repeat rewrite reduce_axcut_equation_1; simpl. apply c_cut_comm. }
      eapply c_trans. { apply c_comm. apply H8. }
      eapply c_trans. { apply c_comm. apply H7. }
      rewrite reduce_axcut_equation_4. eapply c_trans. apply c_cut_comm.
      apply c_cong_cut; try apply c_refl.
      replace (rename_process (up (link (future n1) M')) swap01)
         with (rename_process (up (fill_hole (nil_l n1) M')) swap01)
           by auto.
      unfold up. rewrite up_ctx_over_fill_hole.
      repeat rewrite rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
      rewrite <- plus_n_O.
      inversion H3; inversion H4; subst.
      apply c_comm. eapply H; eauto.
      * rewrite <- rename_axcut_ctx_preserves_length. inversion H2; auto.
      * replace 0 with (swap01 1) by auto;
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; auto.
      * rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E)
           with (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
             at 1 by (rewrite up_ren_n_swap_Sn; auto).
        apply (proj1 (proj2 nfv_under_renaming)).
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        congruence.
      * simpl. replace 0 with (swap01 1) by auto; apply nfv_under_renaming; try apply swap01_is_bijective.
        simpl. intro. apply fv_up_Sn2' in H9. congruence. lia.
    - apply c_comm.
      assert (
        (cut (down (rename_process P swap01))
             (reduce_axcut
               (rename_axcut_ctx (upE (nil_r n1)) swap01)
               (rename_message (upM M') swap01)
               (rename_process (fill_hole E M) swap01)))
        ≡ (reduce_axcut (nil_r n1) M' (cut P (fill_hole E M)))
      ).
      {
        inversion H3; inversion H4; subst.
        eapply c_trans.
        + apply permute_cut_assoc_reduce_axcut; simpl; auto.
          - intro. inversion H7.
          - replace 0 with (swap01 1) by auto; apply nfv_under_renaming.
            apply swap01_is_bijective. unfold upM.
            intro. apply fv_up_Sn2' in H7. congruence. lia.
          - replace 1 with (swap01 0) by auto; apply nfv_under_renaming.
            apply swap01_is_bijective. apply nfv_lift_n. lia.
        + simpl. apply c_refl_inversion_eq. f_equal.
          - rewrite swap_swap_idM.
            unfold upM. rewrite (proj1 (proj2 down_after_up_id)). reflexivity.
          - rewrite swap_swap_id. f_equal. unfold down, up.
            rewrite (proj1 up_after_down_id).
            rewrite swap_swap_id; auto.
            apply nfv_01_swap; auto.
      }
      assert (
        (reduce_axcut (nil_r n1) M' (cut P (fill_hole E M)))
        ≡ (reduce_axcut (nil_r n1) M' (cut (fill_hole E M) P))
      ).
      { repeat rewrite reduce_axcut_equation_2; simpl. apply c_cut_comm. }
      eapply c_trans. { apply c_comm. apply H8. }
      eapply c_trans. { apply c_comm. apply H7. }
      rewrite reduce_axcut_equation_4. eapply c_trans. apply c_cut_comm.
      apply c_cong_cut; try apply c_refl.
      replace (rename_process (up (link M' (future n1))) swap01)
         with (rename_process (up (fill_hole (nil_r n1) M')) swap01)
           by auto.
      unfold up. rewrite up_ctx_over_fill_hole.
      repeat rewrite rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
      rewrite <- plus_n_O.
      inversion H3; inversion H4; subst.
      apply c_comm. eapply H; eauto.
      * rewrite <- rename_axcut_ctx_preserves_length. inversion H2; auto.
      * replace 0 with (swap01 1) by auto;
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; auto.
      * rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E)
           with (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
             at 1 by (rewrite up_ren_n_swap_Sn; auto).
        apply (proj1 (proj2 nfv_under_renaming)).
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        congruence.
      * simpl. replace 0 with (swap01 1) by auto; apply nfv_under_renaming; try apply swap01_is_bijective.
        simpl. intro. apply fv_up_Sn2' in H9. congruence. lia.
  + destruct E, E'; simpl in *; try congruence.
    - assert (
        (cut (down (rename_process P0 swap01))
             (reduce_axcut
                (rename_axcut_ctx (upE (cons_l P E)) swap01)
                (rename_message (lift_message M (S (length_axcut_ctx E)) 1) (up_ren_n (S (length_axcut_ctx E)) swap01))
                (rename_process (fill_hole E' M') swap01)))
        ≡ (reduce_axcut (cons_l P E) M (cut P0 (fill_hole E' M')))
      ).
      {
        eapply c_trans.
        + apply permute_cut_assoc_reduce_axcut.
          - replace 0 with (swap01 1);
            replace swap01 with (up_ren_n 0 swap01); auto.
            apply well_formedness_preserved_under_swap01.
            unfold upE. apply upE_preserves_well_formedness'; auto.
          - apply nfv_ctx_10_swap.
            apply nfv_lift_nE. lia.
          - rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; rewrite lift_ctx_preserves_length; simpl.
            replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
               with (up_ren_n (S (length_axcut_ctx E)) swap01); auto.
            replace (S (length_axcut_ctx E))
               with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (S (length_axcut_ctx E))))
                 at 1
                 by (rewrite up_ren_n_swap_Sn; auto).
            apply nfv_under_renaming.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            intro. apply fv_up_Sn2' in H7. congruence. lia.
          - rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; rewrite lift_ctx_preserves_length; simpl.
            replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
               with (up_ren_n (S (length_axcut_ctx E)) swap01); auto.
            replace (S (S (length_axcut_ctx E)))
               with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (length_axcut_ctx E)))
                 at 1
                 by (rewrite up_ren_n_swap_n; auto).
            apply nfv_under_renaming.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            apply nfv_lift_n. lia.
        + apply c_refl_inversion_eq; f_equal.
          - rewrite swap_swap_idE.
            unfold downE,upE. rewrite down_after_up_idE.
            reflexivity.
          - simpl. rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; repeat rewrite lift_ctx_preserves_length.
            replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
               with (up_ren_n (S (length_axcut_ctx E)) swap01) by auto.
            rewrite up_ren_swap_swap_idM.
            rewrite (proj1 (proj2 down_after_up_id)).
            reflexivity.
          - rewrite swap_swap_id; f_equal.
            unfold up, down. rewrite (proj1 up_after_down_id).
            rewrite swap_swap_id; auto.
            apply nfv_01_swap. inversion H4; auto.
      }
      eapply c_trans. { apply c_comm. apply H7. }
      rewrite reduce_axcut_equation_3. apply c_cong_cut; try apply c_refl.
      apply c_comm. simpl.
      assert (
        (cut (down (rename_process (rename_process (lift_process P 1 1) (up_ren swap01)) swap01))
            (reduce_axcut
              (rename_axcut_ctx (upE (rename_axcut_ctx E' swap01)) swap01)
              (rename_message
                (lift_message (rename_message M' (up_ren_n (length_axcut_ctx E') swap01))
                              (length_axcut_ctx E') 1)
                (up_ren_n (length_axcut_ctx E') swap01))
              (rename_process (rename_process (lift_process (fill_hole E M) 1 1) (up_ren swap01)) swap01)))
        ≡
        (reduce_axcut (rename_axcut_ctx E' swap01)
                      (rename_message M' (up_ren_n (length_axcut_ctx E') swap01))
                      (cut (rename_process (lift_process P 1 1) (up_ren swap01))
                           (rename_process (lift_process (fill_hole E M) 1 1) (up_ren swap01))))
      ).
      {
        eapply c_trans.
        + apply permute_cut_assoc_reduce_axcut.
          - replace 0 with (swap01 1); replace swap01 with (up_ren_n 0 swap01); auto.
            apply well_formedness_preserved_under_swap01.
            unfold upE. apply upE_preserves_well_formedness'. lia.
            replace 0 with (up_ren_n 0 swap01 1) at 1 by auto.
            apply well_formedness_preserved_under_swap01.
            inversion H4; auto.
          - apply nfv_ctx_10_swap.
            apply nfv_lift_nE. lia.
          - rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; rewrite lift_ctx_preserves_length.
            rewrite <- rename_axcut_ctx_preserves_length.
            replace (length_axcut_ctx E')
               with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
                 at 1 by (rewrite up_ren_n_swap_Sn; auto).
            apply (proj1 (proj2 nfv_under_renaming)).
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            intro. apply fv_up_Sn2' in H8; try lia.
            replace (length_axcut_ctx E')
               with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
                 in H8
                 at 1
                 by (rewrite up_ren_n_swap_Sn; auto).
            apply nfv_under_renaming in H8.
            contradiction.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            assumption.
          - rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; rewrite lift_ctx_preserves_length.
            rewrite <- rename_axcut_ctx_preserves_length.
            replace (S (length_axcut_ctx E'))
               with (up_ren_n (length_axcut_ctx E') swap01 (length_axcut_ctx E'))
                 at 1 by (rewrite up_ren_n_swap_n; auto).
            apply nfv_under_renaming.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            apply nfv_lift_n. lia.
        + apply c_refl_inversion_eq; f_equal.
          - rewrite swap_swap_idE.
            unfold downE,upE. rewrite down_after_up_idE.
            reflexivity.
          - repeat rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; repeat rewrite lift_ctx_preserves_length.
            repeat rewrite <- rename_axcut_ctx_preserves_length.
            rewrite up_ren_swap_swap_idM.
            rewrite (proj1 (proj2 down_after_up_id)). auto.
          - rewrite swap_swap_id; f_equal.
            unfold up, down. rewrite (proj1 up_after_down_id).
            rewrite swap_swap_id; auto.
            apply nfv_01_swap.
            replace 1 with (up_ren swap01 2) by auto.
            apply nfv_under_renaming. apply shift_preserves_bijection; apply swap01_is_bijective.
            simpl. intro. apply fv_up_Sn2' in H8.
            inversion H3; congruence. lia.
      }
      eapply c_trans. { apply c_comm. apply H8. }
      clear H7 H8.
      rewrite reduce_axcut_equation_3.
      apply c_cong_cut; try apply c_refl.
      unfold up. repeat rewrite up_ctx_over_fill_hole.
      repeat rewrite rename_axcut_ctx_over_fill_hole;
      try apply shift_preserves_bijection; try apply swap01_is_bijective.
      rewrite up_ctx_over_fill_hole.
      rewrite rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
      rewrite PeanoNat.Nat.add_1_r.
      rewrite <- plus_n_O.
      assert (
        (up_ren_n (length_axcut_ctx (lift_ctx E 1 1)) (up_ren swap01))
          = (up_ren (up_ren_n (length_axcut_ctx E) swap01))
      ).
      {
        rewrite lift_ctx_preserves_length.
        replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
        rewrite up_ren_n_additive.
        rewrite PeanoNat.Nat.add_1_r.
        reflexivity.
      }
      rewrite H7.
      repeat rewrite lift_ctx_preserves_length.
      repeat rewrite <- rename_axcut_ctx_preserves_length.
      apply c_comm. eapply H.
      * assert (length_axcut_ctx E < S n0) by lia.
        apply H8.
      * repeat rewrite <- rename_axcut_ctx_preserves_length.
        rewrite lift_ctx_preserves_length.
        reflexivity.
      * rewrite <- rename_axcut_ctx_preserves_length.
        unfold upE. rewrite lift_ctx_preserves_length.
        rewrite <- rename_axcut_ctx_preserves_length.
        reflexivity.
      * replace 0 with (swap01 1) by auto.
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; simpl.
        replace 1 with (up_ren swap01 2) by auto.
        replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
        apply well_formedness_preserved_under_swap01; simpl.
        apply upE_preserves_well_formedness'. lia.
        inversion H3; auto.
      * replace 0 with (swap01 1) by auto;
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01.
        unfold upE. apply upE_preserves_well_formedness'. lia.
        replace 0 with (up_ren_n 0 swap01 1) by auto.
        apply well_formedness_preserved_under_swap01.
        inversion H4; auto.
      * repeat rewrite <- rename_axcut_ctx_preserves_length.
        repeat rewrite lift_ctx_preserves_length.
        replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
           with (up_ren_n (S (length_axcut_ctx E)) swap01)
             by auto.
        replace (length_axcut_ctx E)
           with (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
             at 1
             by (rewrite up_ren_n_swap_Sn; auto).
        apply nfv_under_renaming.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        replace (S (length_axcut_ctx E))
           with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (S (length_axcut_ctx E))))
             at 1
             by (rewrite up_ren_n_swap_Sn; auto).
        apply nfv_under_renaming.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        intro. apply fv_up_Sn2' in H8. congruence. lia.
      * unfold upE.
        repeat rewrite <- rename_axcut_ctx_preserves_length.
        repeat rewrite lift_ctx_preserves_length.
        repeat rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E')
           with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
             at 1
             by (rewrite up_ren_n_swap_Sn; auto).
        apply nfv_under_renaming.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        intro. apply fv_up_Sn2' in H8; try lia.
        apply H6.
        replace (length_axcut_ctx E')
           with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
             in H8
             at 1
             by (rewrite up_ren_n_swap_Sn; auto).
        apply nfv_under_renaming in H8; auto.
        contradiction.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
    - assert (
        (cut (down (rename_process P0 swap01))
             (reduce_axcut
                (rename_axcut_ctx (upE (cons_l P E)) swap01)
                (rename_message (lift_message M (S (length_axcut_ctx E)) 1) (up_ren_n (S (length_axcut_ctx E)) swap01))
                (rename_process (fill_hole E' M') swap01)))
        ≡ (reduce_axcut (cons_l P E) M (cut (fill_hole E' M') P0))
      ).
      {
        eapply c_trans.
        + apply permute_cut_assoc_reduce_axcut2.
          - replace 0 with (swap01 1);
            replace swap01 with (up_ren_n 0 swap01); auto.
            apply well_formedness_preserved_under_swap01.
            unfold upE. apply upE_preserves_well_formedness'; auto.
          - apply nfv_ctx_10_swap.
            apply nfv_lift_nE. lia.
          - rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; rewrite lift_ctx_preserves_length; simpl.
            replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
               with (up_ren_n (S (length_axcut_ctx E)) swap01); auto.
            replace (S (length_axcut_ctx E))
               with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (S (length_axcut_ctx E))))
                 at 1
                 by (rewrite up_ren_n_swap_Sn; auto).
            apply nfv_under_renaming.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            intro. apply fv_up_Sn2' in H7. congruence. lia.
          - rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; rewrite lift_ctx_preserves_length; simpl.
            replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
               with (up_ren_n (S (length_axcut_ctx E)) swap01); auto.
            replace (S (S (length_axcut_ctx E)))
               with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (length_axcut_ctx E)))
                 at 1
                 by (rewrite up_ren_n_swap_n; auto).
            apply nfv_under_renaming.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            apply nfv_lift_n. lia.
        + apply c_refl_inversion_eq; f_equal.
          - rewrite swap_swap_idE.
            unfold downE,upE. rewrite down_after_up_idE.
            reflexivity.
          - simpl. rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; repeat rewrite lift_ctx_preserves_length.
            replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
               with (up_ren_n (S (length_axcut_ctx E)) swap01) by auto.
            rewrite up_ren_swap_swap_idM.
            rewrite (proj1 (proj2 down_after_up_id)).
            reflexivity.
          - rewrite swap_swap_id; f_equal.
            unfold up, down. rewrite (proj1 up_after_down_id).
            rewrite swap_swap_id; auto.
            apply nfv_01_swap. inversion H4; auto.
      }
      eapply c_trans. { apply c_comm. apply H7. }
      rewrite reduce_axcut_equation_4.
      eapply c_trans. apply c_cut_comm.
      apply c_cong_cut; try apply c_refl.
      apply c_comm. simpl.
      assert (
        (cut (down (rename_process (rename_process (lift_process P 1 1) (up_ren swap01)) swap01))
            (reduce_axcut
              (rename_axcut_ctx (upE (rename_axcut_ctx E' swap01)) swap01)
              (rename_message
                (lift_message (rename_message M' (up_ren_n (length_axcut_ctx E') swap01))
                              (length_axcut_ctx E') 1)
                (up_ren_n (length_axcut_ctx E') swap01))
              (rename_process (rename_process (lift_process (fill_hole E M) 1 1) (up_ren swap01)) swap01)))
        ≡
        (reduce_axcut (rename_axcut_ctx E' swap01)
                      (rename_message M' (up_ren_n (length_axcut_ctx E') swap01))
                      (cut (rename_process (lift_process P 1 1) (up_ren swap01))
                           (rename_process (lift_process (fill_hole E M) 1 1) (up_ren swap01))))
      ).
      {
        eapply c_trans.
        + apply permute_cut_assoc_reduce_axcut.
          - replace 0 with (swap01 1); replace swap01 with (up_ren_n 0 swap01); auto.
            apply well_formedness_preserved_under_swap01.
            unfold upE. apply upE_preserves_well_formedness'. lia.
            replace 0 with (up_ren_n 0 swap01 1) at 1 by auto.
            apply well_formedness_preserved_under_swap01.
            inversion H4; auto.
          - apply nfv_ctx_10_swap.
            apply nfv_lift_nE. lia.
          - rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; rewrite lift_ctx_preserves_length.
            rewrite <- rename_axcut_ctx_preserves_length.
            replace (length_axcut_ctx E')
               with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
                 at 1 by (rewrite up_ren_n_swap_Sn; auto).
            apply (proj1 (proj2 nfv_under_renaming)).
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            intro. apply fv_up_Sn2' in H8; try lia.
            replace (length_axcut_ctx E')
               with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
                 in H8
                 at 1
                 by (rewrite up_ren_n_swap_Sn; auto).
            apply nfv_under_renaming in H8.
            contradiction.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            assumption.
          - rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; rewrite lift_ctx_preserves_length.
            rewrite <- rename_axcut_ctx_preserves_length.
            replace (S (length_axcut_ctx E'))
               with (up_ren_n (length_axcut_ctx E') swap01 (length_axcut_ctx E'))
                 at 1 by (rewrite up_ren_n_swap_n; auto).
            apply nfv_under_renaming.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            apply nfv_lift_n. lia.
        + apply c_refl_inversion_eq; f_equal.
          - rewrite swap_swap_idE.
            unfold downE,upE. rewrite down_after_up_idE.
            reflexivity.
          - repeat rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; repeat rewrite lift_ctx_preserves_length.
            repeat rewrite <- rename_axcut_ctx_preserves_length.
            rewrite up_ren_swap_swap_idM.
            rewrite (proj1 (proj2 down_after_up_id)). auto.
          - rewrite swap_swap_id; f_equal.
            unfold up, down. rewrite (proj1 up_after_down_id).
            rewrite swap_swap_id; auto.
            apply nfv_01_swap.
            replace 1 with (up_ren swap01 2) by auto.
            apply nfv_under_renaming. apply shift_preserves_bijection; apply swap01_is_bijective.
            simpl. intro. apply fv_up_Sn2' in H8.
            inversion H3; congruence. lia.
      }
      eapply c_trans. { apply c_comm. apply H8. }
      clear H7 H8.
      rewrite reduce_axcut_equation_3.
      apply c_cong_cut; try apply c_refl.
      unfold up. repeat rewrite up_ctx_over_fill_hole.
      repeat rewrite rename_axcut_ctx_over_fill_hole;
      try apply shift_preserves_bijection; try apply swap01_is_bijective.
      rewrite up_ctx_over_fill_hole.
      rewrite rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
      rewrite PeanoNat.Nat.add_1_r.
      rewrite <- plus_n_O.
      assert (
        (up_ren_n (length_axcut_ctx (lift_ctx E 1 1)) (up_ren swap01))
          = (up_ren (up_ren_n (length_axcut_ctx E) swap01))
      ).
      {
        rewrite lift_ctx_preserves_length.
        replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
        rewrite up_ren_n_additive.
        rewrite PeanoNat.Nat.add_1_r.
        reflexivity.
      }
      rewrite H7.
      repeat rewrite lift_ctx_preserves_length.
      repeat rewrite <- rename_axcut_ctx_preserves_length.
      apply c_comm. eapply H.
      * assert (length_axcut_ctx E < S n0) by lia.
        apply H8.
      * repeat rewrite <- rename_axcut_ctx_preserves_length.
        rewrite lift_ctx_preserves_length.
        reflexivity.
      * rewrite <- rename_axcut_ctx_preserves_length.
        unfold upE. rewrite lift_ctx_preserves_length.
        rewrite <- rename_axcut_ctx_preserves_length.
        reflexivity.
      * replace 0 with (swap01 1) by auto.
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; simpl.
        replace 1 with (up_ren swap01 2) by auto.
        replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
        apply well_formedness_preserved_under_swap01; simpl.
        apply upE_preserves_well_formedness'. lia.
        inversion H3; auto.
      * replace 0 with (swap01 1) by auto;
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01.
        unfold upE. apply upE_preserves_well_formedness'. lia.
        replace 0 with (up_ren_n 0 swap01 1) by auto.
        apply well_formedness_preserved_under_swap01.
        inversion H4; auto.
      * repeat rewrite <- rename_axcut_ctx_preserves_length.
        repeat rewrite lift_ctx_preserves_length.
        replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
           with (up_ren_n (S (length_axcut_ctx E)) swap01)
             by auto.
        replace (length_axcut_ctx E)
           with (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
             at 1
             by (rewrite up_ren_n_swap_Sn; auto).
        apply nfv_under_renaming.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        replace (S (length_axcut_ctx E))
           with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (S (length_axcut_ctx E))))
             at 1
             by (rewrite up_ren_n_swap_Sn; auto).
        apply nfv_under_renaming.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        intro. apply fv_up_Sn2' in H8. congruence. lia.
      * unfold upE.
        repeat rewrite <- rename_axcut_ctx_preserves_length.
        repeat rewrite lift_ctx_preserves_length.
        repeat rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E')
           with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
             at 1
             by (rewrite up_ren_n_swap_Sn; auto).
        apply nfv_under_renaming.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        intro. apply fv_up_Sn2' in H8; try lia.
        apply H6.
        replace (length_axcut_ctx E')
           with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
             in H8
             at 1
             by (rewrite up_ren_n_swap_Sn; auto).
        apply nfv_under_renaming in H8; auto.
        contradiction.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
    - assert (
        (cut (down (rename_process P0 swap01))
             (reduce_axcut
                (rename_axcut_ctx (upE (cons_r E P)) swap01)
                (rename_message (lift_message M (S (length_axcut_ctx E)) 1) (up_ren_n (S (length_axcut_ctx E)) swap01))
                (rename_process (fill_hole E' M') swap01)))
        ≡ (reduce_axcut (cons_r E P) M (cut P0 (fill_hole E' M')))
      ).
      {
        eapply c_trans.
        + apply permute_cut_assoc_reduce_axcut.
          - replace 0 with (swap01 1);
            replace swap01 with (up_ren_n 0 swap01); auto.
            apply well_formedness_preserved_under_swap01.
            unfold upE. apply upE_preserves_well_formedness'; auto.
          - apply nfv_ctx_10_swap.
            apply nfv_lift_nE. lia.
          - rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; rewrite lift_ctx_preserves_length; simpl.
            replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
               with (up_ren_n (S (length_axcut_ctx E)) swap01); auto.
            replace (S (length_axcut_ctx E))
               with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (S (length_axcut_ctx E))))
                 at 1
                 by (rewrite up_ren_n_swap_Sn; auto).
            apply nfv_under_renaming.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            intro. apply fv_up_Sn2' in H7. congruence. lia.
          - rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; rewrite lift_ctx_preserves_length; simpl.
            replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
               with (up_ren_n (S (length_axcut_ctx E)) swap01); auto.
            replace (S (S (length_axcut_ctx E)))
               with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (length_axcut_ctx E)))
                 at 1
                 by (rewrite up_ren_n_swap_n; auto).
            apply nfv_under_renaming.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            apply nfv_lift_n. lia.
        + apply c_refl_inversion_eq; f_equal.
          - rewrite swap_swap_idE.
            unfold downE,upE. rewrite down_after_up_idE.
            reflexivity.
          - simpl. rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; repeat rewrite lift_ctx_preserves_length.
            replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
               with (up_ren_n (S (length_axcut_ctx E)) swap01) by auto.
            rewrite up_ren_swap_swap_idM.
            rewrite (proj1 (proj2 down_after_up_id)).
            reflexivity.
          - rewrite swap_swap_id; f_equal.
            unfold up, down. rewrite (proj1 up_after_down_id).
            rewrite swap_swap_id; auto.
            apply nfv_01_swap. inversion H4; auto.
      }
      eapply c_trans. { apply c_comm. apply H7. }
      rewrite reduce_axcut_equation_3.
      apply c_cong_cut; try apply c_refl.
      apply c_comm. simpl.
      assert (
        (cut (down (rename_process (rename_process (lift_process P 1 1) (up_ren swap01)) swap01))
            (reduce_axcut
              (rename_axcut_ctx (upE (rename_axcut_ctx E' swap01)) swap01)
              (rename_message
                (lift_message (rename_message M' (up_ren_n (length_axcut_ctx E') swap01))
                              (length_axcut_ctx E') 1)
                (up_ren_n (length_axcut_ctx E') swap01))
              (rename_process (rename_process (lift_process (fill_hole E M) 1 1) (up_ren swap01)) swap01)))
        ≡
        (reduce_axcut (rename_axcut_ctx E' swap01)
                      (rename_message M' (up_ren_n (length_axcut_ctx E') swap01))
                      (cut (rename_process (lift_process (fill_hole E M) 1 1) (up_ren swap01))
                           (rename_process (lift_process P 1 1) (up_ren swap01))))
      ).
      {
        eapply c_trans.
        + apply permute_cut_assoc_reduce_axcut2.
          - replace 0 with (swap01 1); replace swap01 with (up_ren_n 0 swap01); auto.
            apply well_formedness_preserved_under_swap01.
            unfold upE. apply upE_preserves_well_formedness'. lia.
            replace 0 with (up_ren_n 0 swap01 1) at 1 by auto.
            apply well_formedness_preserved_under_swap01.
            inversion H4; auto.
          - apply nfv_ctx_10_swap.
            apply nfv_lift_nE. lia.
          - rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; rewrite lift_ctx_preserves_length.
            rewrite <- rename_axcut_ctx_preserves_length.
            replace (length_axcut_ctx E')
               with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
                 at 1 by (rewrite up_ren_n_swap_Sn; auto).
            apply (proj1 (proj2 nfv_under_renaming)).
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            intro. apply fv_up_Sn2' in H8; try lia.
            replace (length_axcut_ctx E')
               with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
                 in H8
                 at 1
                 by (rewrite up_ren_n_swap_Sn; auto).
            apply nfv_under_renaming in H8.
            contradiction.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            assumption.
          - rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; rewrite lift_ctx_preserves_length.
            rewrite <- rename_axcut_ctx_preserves_length.
            replace (S (length_axcut_ctx E'))
               with (up_ren_n (length_axcut_ctx E') swap01 (length_axcut_ctx E'))
                 at 1 by (rewrite up_ren_n_swap_n; auto).
            apply nfv_under_renaming.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            apply nfv_lift_n. lia.
        + apply c_refl_inversion_eq; f_equal.
          - rewrite swap_swap_idE.
            unfold downE,upE. rewrite down_after_up_idE.
            reflexivity.
          - repeat rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; repeat rewrite lift_ctx_preserves_length.
            repeat rewrite <- rename_axcut_ctx_preserves_length.
            rewrite up_ren_swap_swap_idM.
            rewrite (proj1 (proj2 down_after_up_id)). auto.
          - rewrite swap_swap_id; f_equal.
            unfold up, down. rewrite (proj1 up_after_down_id).
            rewrite swap_swap_id; auto.
            apply nfv_01_swap.
            replace 1 with (up_ren swap01 2) by auto.
            apply nfv_under_renaming. apply shift_preserves_bijection; apply swap01_is_bijective.
            simpl. intro. apply fv_up_Sn2' in H8.
            inversion H3; congruence. lia.
      }
      eapply c_trans. { apply c_comm. apply H8. }
      clear H7 H8.
      rewrite reduce_axcut_equation_4.
      eapply c_trans. apply c_cut_comm.
      apply c_cong_cut; try apply c_refl.
      unfold up. repeat rewrite up_ctx_over_fill_hole.
      repeat rewrite rename_axcut_ctx_over_fill_hole;
      try apply shift_preserves_bijection; try apply swap01_is_bijective.
      rewrite up_ctx_over_fill_hole.
      rewrite rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
      rewrite PeanoNat.Nat.add_1_r.
      rewrite <- plus_n_O.
      assert (
        (up_ren_n (length_axcut_ctx (lift_ctx E 1 1)) (up_ren swap01))
          = (up_ren (up_ren_n (length_axcut_ctx E) swap01))
      ).
      {
        rewrite lift_ctx_preserves_length.
        replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
        rewrite up_ren_n_additive.
        rewrite PeanoNat.Nat.add_1_r.
        reflexivity.
      }
      rewrite H7.
      repeat rewrite lift_ctx_preserves_length.
      repeat rewrite <- rename_axcut_ctx_preserves_length.
      apply c_comm. eapply H.
      * assert (length_axcut_ctx E < S n0) by lia.
        apply H8.
      * repeat rewrite <- rename_axcut_ctx_preserves_length.
        rewrite lift_ctx_preserves_length.
        reflexivity.
      * rewrite <- rename_axcut_ctx_preserves_length.
        unfold upE. rewrite lift_ctx_preserves_length.
        rewrite <- rename_axcut_ctx_preserves_length.
        reflexivity.
      * replace 0 with (swap01 1) by auto.
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; simpl.
        replace 1 with (up_ren swap01 2) by auto.
        replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
        apply well_formedness_preserved_under_swap01; simpl.
        apply upE_preserves_well_formedness'. lia.
        inversion H3; auto.
      * replace 0 with (swap01 1) by auto;
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01.
        unfold upE. apply upE_preserves_well_formedness'. lia.
        replace 0 with (up_ren_n 0 swap01 1) by auto.
        apply well_formedness_preserved_under_swap01.
        inversion H4; auto.
      * repeat rewrite <- rename_axcut_ctx_preserves_length.
        repeat rewrite lift_ctx_preserves_length.
        replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
           with (up_ren_n (S (length_axcut_ctx E)) swap01)
             by auto.
        replace (length_axcut_ctx E)
           with (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
             at 1
             by (rewrite up_ren_n_swap_Sn; auto).
        apply nfv_under_renaming.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        replace (S (length_axcut_ctx E))
           with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (S (length_axcut_ctx E))))
             at 1
             by (rewrite up_ren_n_swap_Sn; auto).
        apply nfv_under_renaming.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        intro. apply fv_up_Sn2' in H8. congruence. lia.
      * unfold upE.
        repeat rewrite <- rename_axcut_ctx_preserves_length.
        repeat rewrite lift_ctx_preserves_length.
        repeat rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E')
           with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
             at 1
             by (rewrite up_ren_n_swap_Sn; auto).
        apply nfv_under_renaming.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        intro. apply fv_up_Sn2' in H8; try lia.
        apply H6.
        replace (length_axcut_ctx E')
           with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
             in H8
             at 1
             by (rewrite up_ren_n_swap_Sn; auto).
        apply nfv_under_renaming in H8; auto.
        contradiction.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
    - assert (
        (cut (down (rename_process P0 swap01))
             (reduce_axcut
                (rename_axcut_ctx (upE (cons_r E P)) swap01)
                (rename_message (lift_message M (S (length_axcut_ctx E)) 1) (up_ren_n (S (length_axcut_ctx E)) swap01))
                (rename_process (fill_hole E' M') swap01)))
        ≡ (reduce_axcut (cons_r E P) M (cut (fill_hole E' M') P0))
      ).
      {
        eapply c_trans.
        + apply permute_cut_assoc_reduce_axcut2.
          - replace 0 with (swap01 1);
            replace swap01 with (up_ren_n 0 swap01); auto.
            apply well_formedness_preserved_under_swap01.
            unfold upE. apply upE_preserves_well_formedness'; auto.
          - apply nfv_ctx_10_swap.
            apply nfv_lift_nE. lia.
          - rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; rewrite lift_ctx_preserves_length; simpl.
            replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
               with (up_ren_n (S (length_axcut_ctx E)) swap01); auto.
            replace (S (length_axcut_ctx E))
               with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (S (length_axcut_ctx E))))
                 at 1
                 by (rewrite up_ren_n_swap_Sn; auto).
            apply nfv_under_renaming.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            intro. apply fv_up_Sn2' in H7. congruence. lia.
          - rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; rewrite lift_ctx_preserves_length; simpl.
            replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
               with (up_ren_n (S (length_axcut_ctx E)) swap01); auto.
            replace (S (S (length_axcut_ctx E)))
               with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (length_axcut_ctx E)))
                 at 1
                 by (rewrite up_ren_n_swap_n; auto).
            apply nfv_under_renaming.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            apply nfv_lift_n. lia.
        + apply c_refl_inversion_eq; f_equal.
          - rewrite swap_swap_idE.
            unfold downE,upE. rewrite down_after_up_idE.
            reflexivity.
          - simpl. rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; repeat rewrite lift_ctx_preserves_length.
            replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
               with (up_ren_n (S (length_axcut_ctx E)) swap01) by auto.
            rewrite up_ren_swap_swap_idM.
            rewrite (proj1 (proj2 down_after_up_id)).
            reflexivity.
          - rewrite swap_swap_id; f_equal.
            unfold up, down. rewrite (proj1 up_after_down_id).
            rewrite swap_swap_id; auto.
            apply nfv_01_swap. inversion H4; auto.
      }
      eapply c_trans. { apply c_comm. apply H7. }
      rewrite reduce_axcut_equation_4.
      eapply c_trans. apply c_cut_comm.
      apply c_cong_cut; try apply c_refl.
      apply c_comm. simpl.
      assert (
        (cut (down (rename_process (rename_process (lift_process P 1 1) (up_ren swap01)) swap01))
            (reduce_axcut
              (rename_axcut_ctx (upE (rename_axcut_ctx E' swap01)) swap01)
              (rename_message
                (lift_message (rename_message M' (up_ren_n (length_axcut_ctx E') swap01))
                              (length_axcut_ctx E') 1)
                (up_ren_n (length_axcut_ctx E') swap01))
              (rename_process (rename_process (lift_process (fill_hole E M) 1 1) (up_ren swap01)) swap01)))
        ≡
        (reduce_axcut (rename_axcut_ctx E' swap01)
                      (rename_message M' (up_ren_n (length_axcut_ctx E') swap01))
                      (cut (rename_process (lift_process (fill_hole E M) 1 1) (up_ren swap01))
                           (rename_process (lift_process P 1 1) (up_ren swap01))))
      ).
      {
        eapply c_trans.
        + apply permute_cut_assoc_reduce_axcut2.
          - replace 0 with (swap01 1); replace swap01 with (up_ren_n 0 swap01); auto.
            apply well_formedness_preserved_under_swap01.
            unfold upE. apply upE_preserves_well_formedness'. lia.
            replace 0 with (up_ren_n 0 swap01 1) at 1 by auto.
            apply well_formedness_preserved_under_swap01.
            inversion H4; auto.
          - apply nfv_ctx_10_swap.
            apply nfv_lift_nE. lia.
          - rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; rewrite lift_ctx_preserves_length.
            rewrite <- rename_axcut_ctx_preserves_length.
            replace (length_axcut_ctx E')
               with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
                 at 1 by (rewrite up_ren_n_swap_Sn; auto).
            apply (proj1 (proj2 nfv_under_renaming)).
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            intro. apply fv_up_Sn2' in H8; try lia.
            replace (length_axcut_ctx E')
               with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
                 in H8
                 at 1
                 by (rewrite up_ren_n_swap_Sn; auto).
            apply nfv_under_renaming in H8.
            contradiction.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            assumption.
          - rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; rewrite lift_ctx_preserves_length.
            rewrite <- rename_axcut_ctx_preserves_length.
            replace (S (length_axcut_ctx E'))
               with (up_ren_n (length_axcut_ctx E') swap01 (length_axcut_ctx E'))
                 at 1 by (rewrite up_ren_n_swap_n; auto).
            apply nfv_under_renaming.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            apply nfv_lift_n. lia.
        + apply c_refl_inversion_eq; f_equal.
          - rewrite swap_swap_idE.
            unfold downE,upE. rewrite down_after_up_idE.
            reflexivity.
          - repeat rewrite <- rename_axcut_ctx_preserves_length.
            unfold upE; repeat rewrite lift_ctx_preserves_length.
            repeat rewrite <- rename_axcut_ctx_preserves_length.
            rewrite up_ren_swap_swap_idM.
            rewrite (proj1 (proj2 down_after_up_id)). auto.
          - rewrite swap_swap_id; f_equal.
            unfold up, down. rewrite (proj1 up_after_down_id).
            rewrite swap_swap_id; auto.
            apply nfv_01_swap.
            replace 1 with (up_ren swap01 2) by auto.
            apply nfv_under_renaming. apply shift_preserves_bijection; apply swap01_is_bijective.
            simpl. intro. apply fv_up_Sn2' in H8.
            inversion H3; congruence. lia.
      }
      eapply c_trans. { apply c_comm. apply H8. }
      clear H7 H8.
      rewrite reduce_axcut_equation_4.
      eapply c_trans. apply c_cut_comm.
      apply c_cong_cut; try apply c_refl.
      unfold up. repeat rewrite up_ctx_over_fill_hole.
      repeat rewrite rename_axcut_ctx_over_fill_hole;
      try apply shift_preserves_bijection; try apply swap01_is_bijective.
      rewrite up_ctx_over_fill_hole.
      rewrite rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
      rewrite PeanoNat.Nat.add_1_r.
      rewrite <- plus_n_O.
      assert (
        (up_ren_n (length_axcut_ctx (lift_ctx E 1 1)) (up_ren swap01))
          = (up_ren (up_ren_n (length_axcut_ctx E) swap01))
      ).
      {
        rewrite lift_ctx_preserves_length.
        replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
        rewrite up_ren_n_additive.
        rewrite PeanoNat.Nat.add_1_r.
        reflexivity.
      }
      rewrite H7.
      repeat rewrite lift_ctx_preserves_length.
      repeat rewrite <- rename_axcut_ctx_preserves_length.
      apply c_comm. eapply H.
      * assert (length_axcut_ctx E < S n0) by lia.
        apply H8.
      * repeat rewrite <- rename_axcut_ctx_preserves_length.
        rewrite lift_ctx_preserves_length.
        reflexivity.
      * rewrite <- rename_axcut_ctx_preserves_length.
        unfold upE. rewrite lift_ctx_preserves_length.
        rewrite <- rename_axcut_ctx_preserves_length.
        reflexivity.
      * replace 0 with (swap01 1) by auto.
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; simpl.
        replace 1 with (up_ren swap01 2) by auto.
        replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
        apply well_formedness_preserved_under_swap01; simpl.
        apply upE_preserves_well_formedness'. lia.
        inversion H3; auto.
      * replace 0 with (swap01 1) by auto;
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01.
        unfold upE. apply upE_preserves_well_formedness'. lia.
        replace 0 with (up_ren_n 0 swap01 1) by auto.
        apply well_formedness_preserved_under_swap01.
        inversion H4; auto.
      * repeat rewrite <- rename_axcut_ctx_preserves_length.
        repeat rewrite lift_ctx_preserves_length.
        replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
           with (up_ren_n (S (length_axcut_ctx E)) swap01)
             by auto.
        replace (length_axcut_ctx E)
           with (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
             at 1
             by (rewrite up_ren_n_swap_Sn; auto).
        apply nfv_under_renaming.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        replace (S (length_axcut_ctx E))
           with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (S (length_axcut_ctx E))))
             at 1
             by (rewrite up_ren_n_swap_Sn; auto).
        apply nfv_under_renaming.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        intro. apply fv_up_Sn2' in H8. congruence. lia.
      * unfold upE.
        repeat rewrite <- rename_axcut_ctx_preserves_length.
        repeat rewrite lift_ctx_preserves_length.
        repeat rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E')
           with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
             at 1
             by (rewrite up_ren_n_swap_Sn; auto).
        apply nfv_under_renaming.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        intro. apply fv_up_Sn2' in H8; try lia.
        apply H6.
        replace (length_axcut_ctx E')
           with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
             in H8
             at 1
             by (rewrite up_ren_n_swap_Sn; auto).
        apply nfv_under_renaming in H8; auto.
        contradiction.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
Qed.

Lemma confluence_critical_pairs :
  forall E E' M M',
    well_formed_axcut_ctx 0 E  ->
    well_formed_axcut_ctx 0 E' ->
    ~ (occurs_free_message (length_axcut_ctx E) M) ->
    ~ (occurs_free_message (length_axcut_ctx E') M') ->
    (reduce_axcut E M (fill_hole E' M')) ≡ (reduce_axcut E' M' (fill_hole E M)).
Proof.
  intros; eapply confluence_critical_pairs'; eauto.
Qed.
