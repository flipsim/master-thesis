From FD Require Import Syntax.
From FD Require Import Types.
From FD Require Import Typing.
From FD Require Import Contexts.

From Stdlib Require Import ssreflect.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import List.ListNotations.

(* use alternative rename ctx split lemma using strong induction *)
Lemma rename_ctx_split' :
  forall (Γ Γ1 Γ2 Δ : ctx type) (r : renaming),
    bijective r ->
    (exists r_inv, (cancel r_inv r) /\ (cancel r r_inv) /\
    (Γ ≜ Γ1 ∘ Γ2 ->
      (forall n, lookup n Γ = lookup (r n) Δ) ->
        (forall i, i <= (length Δ) ->
          exists Δ1 Δ2, (ListDef.firstn i Δ) ≜ Δ1 ∘ Δ2 /\
          (forall k, k < i ->
            lookup (r_inv k) Γ1 = lookup k Δ1 /\
            lookup (r_inv k) Γ2 = lookup k Δ2
          )))).
Proof.
  intros Γ Γ1 Γ2 Δ r H_bij_r.
  destruct (inverse_of_bijective r H_bij_r) as [r_inv [H_cancel' H_cancel]].
  exists r_inv. split; try assumption. split; try assumption.

  intros H_ctx_split_Γ H_eq_Γ_Δ.
  induction i.
  + intros. exists nil, nil; simpl. split. constructor.
    induction k; intros; inversion H0.
  + intros.
    assert (i <= length Δ). lia.
    apply IHi in H0.
    destruct H0 as [Δ1 [Δ2 [H_ctx_n_Δ H_IH]]].
    specialize H_eq_Γ_Δ with (n := r_inv i).
    rewrite H_cancel in H_eq_Γ_Δ.
    symmetry in H_eq_Γ_Δ.
    pose proof (decide_ctx_split_partition _ _ _
                (r_inv i) (lookup i Δ) H_ctx_split_Γ H_eq_Γ_Δ).
    destruct H0.
    - exists (Δ1 ++ (lookup i Δ :: nil)).
      exists (Δ2 ++ (None :: nil)). split.
      {
        rewrite firstn_Sn_lookup; auto.
        apply ctx_split_distribution; try assumption.
        apply split_cons; destruct (lookup i Δ); try constructor.
      }
      induction k.
      { intros.
        destruct (ctx_split_preserves_length _ Δ1 Δ2 H_ctx_n_Δ) as [H_len_Δ1 H_len_Δ2].
        assert (length (List.firstn i Δ) = i).
        { apply List.firstn_length_le. lia. }
        rewrite H2 in H_len_Δ1, H_len_Δ2.
        destruct i.
        + symmetry in H_len_Δ1, H_len_Δ2.
          apply List.length_zero_iff_nil in H_len_Δ1.
          apply List.length_zero_iff_nil in H_len_Δ2.
          subst.
          destruct H0.
          rewrite H0 H3.
          simpl. split; reflexivity.
        + destruct Δ1, Δ2; try inversion H_len_Δ1; try inversion H_len_Δ2.
          simpl.
          specialize H_IH with 0.
          assert (0 < S i) by lia.
          apply H_IH in H3. destruct H3.
          rewrite H3 H6.
          split; reflexivity.
      }
      {
        intros.
        inversion H1.
        - rewrite H3. destruct H0. rewrite H0 H2.
          assert (i = length Δ1).
          {
            apply ctx_split_preserves_length in H_ctx_n_Δ.
            destruct H_ctx_n_Δ.
            rewrite <- H4.
            rewrite List.firstn_length_le.
            lia.
            reflexivity.
          }
          assert (i = length Δ2).
          {
            apply ctx_split_preserves_length in H_ctx_n_Δ.
            destruct H_ctx_n_Δ.
            rewrite <- H6.
            rewrite List.firstn_length_le.
            lia.
            reflexivity.
          }
          rewrite -> H4 at 2.
          rewrite -> H5 at 3.
          rewrite ctx_lookup_app_length; auto.
          rewrite ctx_lookup_app_length; auto.
        - assert (S k < i) by lia.
          assert (i = length Δ1).
          {
            apply ctx_split_preserves_length in H_ctx_n_Δ.
            destruct H_ctx_n_Δ.
            rewrite <- H5.
            rewrite List.firstn_length_le.
            lia.
            reflexivity.
          }
          rewrite H5 in H4.
          assert (i = length Δ2).
          {
            apply ctx_split_preserves_length in H_ctx_n_Δ.
            destruct H_ctx_n_Δ.
            rewrite <- H7.
            rewrite List.firstn_length_le.
            lia.
            reflexivity.
          }
          assert (S k < length Δ2) by lia.
          rewrite (ctx_lookup_app _ _ (S k) H7).
          rewrite (ctx_lookup_app _ _ (S k) H4).
          auto.
      }
    - (* same things as above but now split right *)
      exists (Δ1 ++ (None :: nil)).
      exists (Δ2 ++ (lookup i Δ  :: nil)). split.
      {
        rewrite firstn_Sn_lookup; auto.
        apply ctx_split_distribution; try assumption.
        apply split_cons; destruct (lookup i Δ); try constructor.
      }
      induction k.
      { intros.
        destruct (ctx_split_preserves_length _ Δ1 Δ2 H_ctx_n_Δ) as [H_len_Δ1 H_len_Δ2].
        assert (length (List.firstn i Δ) = i).
        { apply List.firstn_length_le. lia. }
        rewrite H2 in H_len_Δ1, H_len_Δ2.
        destruct i.
        + symmetry in H_len_Δ1, H_len_Δ2.
          apply List.length_zero_iff_nil in H_len_Δ1.
          apply List.length_zero_iff_nil in H_len_Δ2.
          subst.
          destruct H0.
          rewrite H0 H3.
          simpl. split; reflexivity.
        + destruct Δ1, Δ2; try inversion H_len_Δ1; try inversion H_len_Δ2.
          simpl.
          specialize H_IH with 0.
          assert (0 < S i) by lia.
          apply H_IH in H3. destruct H3.
          rewrite H3 H6.
          split; reflexivity.
      }
      {
        intros.
        inversion H1.
        - rewrite H3. destruct H0. rewrite H0 H2.
          assert (i = length Δ1).
          {
            apply ctx_split_preserves_length in H_ctx_n_Δ.
            destruct H_ctx_n_Δ.
            rewrite <- H4.
            rewrite List.firstn_length_le.
            lia.
            reflexivity.
          }
          assert (i = length Δ2).
          {
            apply ctx_split_preserves_length in H_ctx_n_Δ.
            destruct H_ctx_n_Δ.
            rewrite <- H6.
            rewrite List.firstn_length_le.
            lia.
            reflexivity.
          }
          rewrite -> H4 at 1.
          rewrite -> H5 at 2.
          rewrite ctx_lookup_app_length; auto.
          rewrite ctx_lookup_app_length; auto.
        - assert (S k < i) by lia.
          assert (i = length Δ1).
          {
            apply ctx_split_preserves_length in H_ctx_n_Δ.
            destruct H_ctx_n_Δ.
            rewrite <- H5.
            rewrite List.firstn_length_le.
            lia.
            reflexivity.
          }
          rewrite H5 in H4.
          assert (i = length Δ2).
          {
            apply ctx_split_preserves_length in H_ctx_n_Δ.
            destruct H_ctx_n_Δ.
            rewrite <- H7.
            rewrite List.firstn_length_le.
            lia.
            reflexivity.
          }
          assert (S k < length Δ2) by lia.
          rewrite (ctx_lookup_app _ _ (S k) H7).
          rewrite (ctx_lookup_app _ _ (S k) H4).
          auto.
      }
Qed.

(* for bijective renamings we can compute a new context split adhering to the renaming *)
Lemma rename_ctx_split :
  forall (Γ Γ1 Γ2 Δ : ctx type) (r : renaming),
    bijective r ->
    Γ ≜ Γ1 ∘ Γ2 ->
    (forall n, lookup n Γ = lookup (r n) Δ) ->
    (exists Δ1 Δ2,
      Δ ≜ Δ1 ∘ Δ2 /\
      (forall n, lookup n Γ1 = lookup (r n) Δ1) /\
      (forall n, lookup n Γ2 = lookup (r n) Δ2)).
Proof.
  intros Γ Γ1 Γ2 Δ r H_bij_r Ctx_split_Γ H_eq_Γ_Δ.
  pose proof (rename_ctx_split' Γ Γ1 Γ2 Δ r H_bij_r).
  destruct H as [r_inv [H_cancel' [H_cancel H]]].
  pose proof (H Ctx_split_Γ H_eq_Γ_Δ (length Δ) (le_n (length Δ))).
  destruct H0 as [Δ1 [Δ2 H0]].
  exists Δ1, Δ2.
  rewrite List.firstn_all in H0. destruct H0.
  split; try assumption.
  split.
  + unfold "<" in H1.
    intro n.
    destruct (Compare_dec.le_gt_dec (S (r n)) (length Δ)).
    - apply H1 in l.
      rewrite H_cancel in l. destruct l; auto.
    - assert (length Δ = length Δ1).
      {
        apply ctx_split_preserves_length in H0. destruct H0; auto.
      }
      rewrite (ctx_lookup_gt_len Δ1); try lia.
      specialize H_eq_Γ_Δ with n.
      rewrite (ctx_lookup_gt_len Δ) in H_eq_Γ_Δ; try lia.
      symmetry in H_eq_Γ_Δ.
      destruct (decide_ctx_split_partition _ _ _ _ _ Ctx_split_Γ H_eq_Γ_Δ); destruct H3; auto.
  + unfold "<" in H1.
    intro n.
    destruct (Compare_dec.le_gt_dec (S (r n)) (length Δ)).
    - apply H1 in l.
      rewrite H_cancel in l. destruct l; auto.
    - assert (length Δ = length Δ2).
      {
        apply ctx_split_preserves_length in H0. destruct H0; auto.
      }
      rewrite (ctx_lookup_gt_len Δ2); try lia.
      specialize H_eq_Γ_Δ with n.
      rewrite (ctx_lookup_gt_len Δ) in H_eq_Γ_Δ; try lia.
      symmetry in H_eq_Γ_Δ.
      destruct (decide_ctx_split_partition _ _ _ _ _ Ctx_split_Γ H_eq_Γ_Δ); destruct H3; auto.
Qed.

(* renaming of contexts *)
Lemma context_renaming :
  (forall Γ p, Γ ⊢ p :#
    -> forall (r : renaming), bijective r
    -> forall Γ' (eq : forall n, lookup n Γ = lookup (r n) Γ'), Γ' ⊢ (rename_process p r) :#)
  /\
  (forall Γ M A, Γ ⊢ M :! A
    -> forall (r : renaming), bijective r
    -> forall Γ' (eq : forall n, lookup n Γ = lookup (r n) Γ'), Γ' ⊢ (rename_message M r) :! A)
  /\
  (forall Γ s A, Γ ⊢ s :$  A
    -> forall (r : renaming), bijective r
    -> forall Γ' (eq : forall n, lookup n Γ = lookup (r n) Γ'), Γ' ⊢ (rename_statement s r) :$ A).
Proof.
  apply typing_ind; intros; simpl.
  + pose proof (rename_ctx_split Γ Γ1 Γ2 Γ' r H1 c eq).
    destruct H2 as [Δ1 [Δ2 [Hctx [Heq1 Heq2]]]].
    eapply t_ax.
    - apply Hctx.
    - apply H; try assumption.
    - apply H0; try assumption.
  + assert (bijective (up_ren r)) as Hbij_shiftr by apply (shift_preserves_bijection r H1).
    pose proof (rename_ctx_split Γ Γ1 Γ2 Γ' r H1 c eq).
    destruct H2 as [Δ1 [Δ2 [Hctx [Heq1 Heq2]]]].
    apply t_cut with (Γ1 := Δ1) (Γ2 := Δ2) (A := A).
    - apply Hctx.
    - apply H; auto.
      intros [|].
      * destruct Γ1, Δ1; auto.
      * simpl. destruct Γ1, Δ1; simpl; auto.
    - apply H0; auto.
      intros [|].
      * destruct Γ2, Δ2; auto.
      * simpl; destruct Γ2, Δ2; simpl; auto.
  + assert (bijective (up_ren r)) as Hbij_shiftr by apply (shift_preserves_bijection r H1).
    pose proof (rename_ctx_split Γ Γ1 Γ2 Γ' r H1 c eq).
    destruct H2 as [Δ1 [Δ2 [Hctx [Heq1 Heq2]]]].
    econstructor; try eassumption;
    (* try apply induction hypothesis *)
    try (
      match goal with
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_process ?P r' :#
          |- ?Γ ⊢ rename_process ?P ?r :# ] => apply IH
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_statement ?s r' :$ ?A'
          |- ?Γ ⊢ rename_statement ?s ?r :$ ?A ] => apply IH
      end
    );
    try assumption.
    (* show that up_ren r preserves type mappings in the extended context *)
    try (
      intros [|]; destruct Γ1, Δ1, Γ2, Δ2; simpl; auto
    ).
  + assert (bijective (up_ren r)) as Hbij_shiftr by apply (shift_preserves_bijection r H).
    econstructor; try eassumption;
    (* try apply induction hypothesis *)
    try (
      match goal with
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_process ?P r' :#
          |- ?Γ ⊢ rename_process ?P ?r :# ] => apply IH
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_statement ?s r' :$ ?A
          |- ?Γ ⊢ rename_statement ?s ?r :$ ?A ] => apply IH
      end
    ).
    unfold ctx_eq. intro n.
    rewrite (lookup_ctx_nil empty_ctx eq_refl).
    destruct H.
    specialize eq with (g n).
    rewrite c1 in eq.
    rewrite <- eq.
    unfold ctx_eq in c.
    specialize c with (g n).
    rewrite (lookup_ctx_nil empty_ctx eq_refl) in c.
    assumption.
  + assert (bijective (up_ren r)) as Hbij_shiftr by apply (shift_preserves_bijection r H).
    econstructor; try eassumption;
    (* try apply induction hypothesis *)
    try (
      match goal with
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_process ?P r' :#
          |- ?Γ ⊢ rename_process ?P ?r :# ] => apply IH
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_statement ?s r' :$ ?A
          |- ?Γ ⊢ rename_statement ?s ?r :$ ?A ] => apply IH
      end
    ).
    intros n.
    destruct H.
    specialize eq with (g n).
    rewrite c1 in eq.
    rewrite <- eq.
    unfold ctx_eq in c.
    rewrite (c (g n)).
    destruct (PeanoNat.Nat.eq_dec (g n) i).
    - rewrite <- e.
      rewrite ctx_lookup_after_insert.
      rewrite c1.
      rewrite ctx_lookup_after_insert.
      reflexivity.
    - destruct (PeanoNat.Nat.eq_dec n (r i)).
      * rewrite e.
        rewrite c0.
        repeat rewrite ctx_lookup_after_insert.
        reflexivity.
      * try repeat rewrite ctx_lookup_singleton_neq; auto.
  + assert (bijective (up_ren r)) as Hbij_shiftr by apply (shift_preserves_bijection r H0).
    econstructor; try eassumption;
    (* try apply induction hypothesis *)
    try (
      match goal with
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_process ?P r' :#
          |- ?Γ ⊢ rename_process ?P ?r :# ] => apply IH
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_statement ?s r' :$ ?A
          |- ?Γ ⊢ rename_statement ?s ?r :$ ?A ] => apply IH
      end
    ).
    try assumption. apply eq.
  + assert (bijective (up_ren r)) as Hbij_shiftr by apply (shift_preserves_bijection r H0).
    econstructor; try eassumption;
    (* try apply induction hypothesis *)
    try (
      match goal with
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_process ?P r' :#
          |- ?Γ ⊢ rename_process ?P ?r :# ] => apply IH
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_statement ?s r' :$ ?A
          |- ?Γ ⊢ rename_statement ?s ?r :$ ?A ] => apply IH
      end
    ).
    try assumption.
    intros [|]; destruct Γ, Γ'; simpl; auto.
  + assert (bijective (up_ren r)) as Hbij_shiftr by apply (shift_preserves_bijection r H0).
    econstructor; try eassumption;
    (* try apply induction hypothesis *)
    try (
      match goal with
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_process ?P r' :#
          |- ?Γ ⊢ rename_process ?P ?r :# ] => apply IH
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_statement ?s r' :$ ?A
          |- ?Γ ⊢ rename_statement ?s ?r :$ ?A ] => apply IH
      end
    ).
    try assumption.
    intros [|]; destruct Γ, Γ'; simpl; auto.
  + assert (bijective (up_ren r)) as Hbij_shiftr by apply (shift_preserves_bijection r H1).
    econstructor; try eassumption;
    (* try apply induction hypothesis *)
    try (
      match goal with
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_process ?P r' :#
          |- ?Γ ⊢ rename_process ?P ?r :# ] => apply IH
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_statement ?s r' :$ ?A
          |- ?Γ ⊢ rename_statement ?s ?r :$ ?A ] => apply IH
      end
    );
    try assumption;
    (* show that up_ren r preserves type mappings in the extended context *)
    try (
      intros [|]; destruct Γ, Γ'; simpl; auto
    ).
  + assert (bijective (up_ren r)) as Hbij_shiftr by apply (shift_preserves_bijection r H1).
    pose proof (rename_ctx_split Γ Γ1 Γ2 Γ' r H1 c eq).
    destruct H2 as [Δ1 [Δ2 [Hctx [Heq1 Heq2]]]].
    econstructor; try eassumption;
    (* try apply induction hypothesis *)
    try (
      match goal with
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_process ?P r' :#
          |- ?Γ ⊢ rename_process ?P ?r :# ] => apply IH
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_statement ?s r' :$ ?A'
          |- ?Γ ⊢ rename_statement ?s ?r :$ ?A ] => apply IH
      end
    );
    try assumption;
    (* show that up_ren r preserves type mappings in the extended context *)
    try (
      intros [|]; destruct Γ1, Δ1, Γ2, Δ2; simpl; auto
    ).
  + assert (bijective (up_ren r)) as Hbij_shiftr by apply (shift_preserves_bijection r H0).
    assert (bijective (up_ren (up_ren r))) as Hbij_shiftshiftr by apply (shift_preserves_bijection (up_ren r) Hbij_shiftr).
    econstructor; try eassumption;
    (* try apply induction hypothesis *)
    try (
      match goal with
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_process ?P r' :#
          |- ?Γ ⊢ rename_process ?P ?r :# ] => apply IH
      | [ IH : forall r', _ -> forall Γ', _ -> Γ' ⊢ rename_statement ?s r' :$ ?A
          |- ?Γ ⊢ rename_statement ?s ?r :$ ?A ] => apply IH
      end
    );
    try assumption;
    (* show that up_ren r preserves type mappings in the extended context *)
    intros [|[|]]; destruct Γ, Γ'; simpl; auto.
  + econstructor; intros n; auto.
    destruct H.
    specialize eq with (g n).
    rewrite c1 in eq.
    rewrite <- eq.
    rewrite (lookup_ctx_nil empty_ctx); auto.
    unfold ctx_eq in c.
    specialize c with (g n).
    rewrite (lookup_ctx_nil empty_ctx) in c; auto.
  + econstructor. apply H; auto.
Qed.

(* swapping indicies 0 and 1 preserves typing under swap01 *)
Lemma swap01_preserves_typing :
  forall A B Γ p,
    (A :: (B :: Γ)) ⊢ p :# -> (B :: (A :: Γ)) ⊢ (rename_process p swap01) :#.
Proof.
  intros.
  destruct context_renaming as [Hren [_ _]].
  eapply Hren.
  - apply H.
  - apply swap01_is_bijective.
  - induction n; auto.
    destruct n; auto.
Qed.

Lemma swap01_preserves_well_typedness :
  forall Γ p,
    Γ ⊢ p :# -> exists Γ', Γ' ⊢ (rename_process p swap01) :#.
Proof.
  intros.
  destruct Γ.
  + exists nil.
    eapply (proj1 context_renaming); eauto.
    apply swap01_is_bijective.
    intros; repeat rewrite lookup_ctx_nil; auto.
  + destruct Γ.
    - exists [None; o]. eapply (proj1 context_renaming); eauto.
      apply swap01_is_bijective.
      destruct n as [|[|]]; auto; simpl.
      rewrite lookup_ctx_nil; auto.
    - apply swap01_preserves_typing in H. eexists; eauto.
Qed.

(* upshifting identity remains identity *)
Lemma up_id_is_id :
  forall (r : renaming),
    (forall x, r x = x) -> (forall x, up_ren r x = x).
Proof. intros; destruct x; simpl; try rewrite H; auto. Qed.

(* renaming with identity *)
Lemma rename_id :
  (forall (p : process),
    forall (r : renaming), (forall x, r x = x) -> rename_process p r = p)
  /\
  (forall (m : message),
    forall (r : renaming), (forall x, r x = x) -> rename_message m r = m)
  /\
  (forall (s : statement),
    forall (r : renaming), (forall x, r x = x) -> rename_statement s r = s).
Proof.
  apply syntax_ind; intros; simpl;
  try rewrite H; try rewrite H0;
  try repeat apply up_id_is_id;
  auto.
Qed.

Lemma up_shift_compose :
  forall (f g c : renaming),
    (forall x, Basics.compose f g x = c x) ->
      (forall x, (Basics.compose (up_ren f) (up_ren g)) x = (up_ren c) x).
Proof.
  intros.
  unfold Basics.compose; destruct x; simpl; auto.
  apply f_equal. apply H.
Qed.

(* renamings compose *)
Lemma renamings_compose :
  (forall (p : process), forall (f g c : renaming),
    (forall x, Basics.compose f g x = c x) ->
      rename_process (rename_process p g) f  = rename_process p c)
  /\
  (forall (m : message), forall (f g c : renaming),
    (forall x, Basics.compose f g x = c x) ->
      rename_message (rename_message m g) f  = rename_message m c)
  /\
  (forall (s : statement), forall (f g c : renaming),
    (forall x, Basics.compose f g x = c x) ->
      rename_statement (rename_statement s g) f  = rename_statement s c).
Proof.
  apply syntax_ind; intros; simpl;
  try (try rewrite <- (H f g c); try rewrite <- (H0 f g c); auto);
  try (try rewrite <- (H (up_ren f) (up_ren g) (up_ren c)); try rewrite <- (H0 (up_ren f) (up_ren g) (up_ren c));
       try apply up_shift_compose; auto).
  + unfold Basics.compose in H. rewrite H. reflexivity.
  + try rewrite <- (H (up_ren (up_ren f)) (up_ren (up_ren g)) (up_ren (up_ren c)));
    try rewrite <- (H0 (up_ren (up_ren f)) (up_ren (up_ren g)) (up_ren (up_ren c)));
    try repeat apply up_shift_compose; auto.
Qed.

Corollary swap_swap_id :
  forall P, rename_process (rename_process P swap01) swap01 = P.
Proof.
  intros.
  rewrite ((proj1 renamings_compose) _ _ _ id).
  + intros. destruct x; auto; destruct x; reflexivity.
  + apply (proj1 rename_id); auto.
Qed.

Corollary swap_swap_idM :
  forall M, rename_message (rename_message M swap01) swap01 = M.
Proof.
  intros.
  rewrite ((proj1 (proj2 renamings_compose)) _ _ _ id).
  + intros. destruct x; auto; destruct x; reflexivity.
  + apply (proj1 (proj2 rename_id)); auto.
Qed.

(******************************************************************************)
(* Properties of downshifting and upshifing wrt typing                        *)
(******************************************************************************)
(* Typing variables in modified contexts *)
Lemma type_id_after_downshift :
  forall (Γ Δ : ctx type) A n,
       length Γ < S n
    -> Γ ++ Δ ⊢ future n :! A
    -> Γ ++ None :: Δ ⊢ future (S n) :! A.
Proof.
  intros.
  econstructor.
  inversion H0; subst.
  unfold ctx_eq in H3.
  intro k.
  destruct (Compare_dec.lt_dec k (length Γ)).
  + specialize H3 with k.
    rewrite ctx_lookup_app; auto.
    rewrite ctx_lookup_singleton_neq; try lia.
    rewrite ctx_lookup_singleton_neq in H3; try lia.
    rewrite <- H3.
    rewrite ctx_lookup_app; auto.
  + destruct (PeanoNat.Nat.eq_dec k (length Γ)).
    - subst.
      rewrite ctx_lookup_app_length; auto.
      rewrite ctx_lookup_singleton_neq; try lia.
      reflexivity.
    - destruct k.
      * assert (0 >= length Γ) by lia.
        inversion H1. apply List.length_zero_iff_nil in H4; subst.
        reflexivity.
      * specialize H3 with k.
        destruct (PeanoNat.Nat.eq_dec k n).
        ** subst.
          rewrite ctx_lookup_after_insert.
          rewrite ctx_lookup_after_insert in H3.
          rewrite <- H3.
          repeat try rewrite ctx_lookup_app_minus; try lia.
          replace (S n - length Γ) with (S (n - length Γ)) by lia.
          reflexivity.
        ** rewrite ctx_lookup_singleton_neq; try lia.
           rewrite ctx_lookup_singleton_neq in H3; try lia.
           rewrite <- H3 at 2.
           repeat try rewrite ctx_lookup_app_minus; try lia.
           replace (S k - length Γ) with (S (k - length Γ)) by lia.
           reflexivity.
Qed.

Lemma type_id_before_downshift:
  forall (Γ Δ : ctx type) A n,
       n < length Γ
    -> Γ ++ Δ ⊢ future n :! A
    -> Γ ++ None :: Δ ⊢ future n :! A.
Proof.
  intros.
  econstructor. inversion H0; subst. unfold ctx_eq in H3. intro k.
  destruct (Compare_dec.lt_dec k (length Γ)).
  + rewrite <- (H3 k).
    repeat try rewrite ctx_lookup_app; auto.
  + destruct (PeanoNat.Nat.eq_dec k (length Γ)).
    - subst.
      rewrite ctx_lookup_app_length; auto.
      rewrite ctx_lookup_singleton_neq; try lia.
      reflexivity.
    - destruct k.
      * assert (0 >= length Γ) by lia.
        inversion H1. apply List.length_zero_iff_nil in H4; subst.
        inversion H.
      * destruct (PeanoNat.Nat.eq_dec k n).
        ** subst.
           rewrite ctx_lookup_singleton_neq; try lia.
        ** specialize H3 with k.
           rewrite ctx_lookup_singleton_neq; try lia.
           rewrite ctx_lookup_singleton_neq in H3; try lia.
           rewrite <- H3 at 2.
           repeat try rewrite ctx_lookup_app_minus; try lia.
           replace (S k - length Γ) with (S (k - length Γ)) by lia.
           reflexivity.
Qed.

(* Soundness for downshifting *)
(* The downshift must be 'injective' in the sense that there may not be
   a name clash after downshifting. We ensure so be requiring that
   (length Γ) does not occur free *)
Lemma down_shift_sound :
  (forall p, forall Γ Δ, ~ (length Γ ∈ p) ->
    (Γ ++ (None :: Δ)) ⊢ p :# <-> (Γ ++ Δ) ⊢ (down1_process p (length Γ)) :#)
  /\
  (forall M, forall Γ Δ A, ~ (occurs_free_message (length Γ) M) ->
    (Γ ++ (None :: Δ)) ⊢ M :! A <-> (Γ ++ Δ) ⊢ (down1_message M (length Γ)) :! A)
  /\
  (forall s, forall Γ Δ A, ~ (occurs_free_statement (length Γ) s) ->
    (Γ ++ (None :: Δ)) ⊢ s :$  A <-> (Γ ++ Δ) ⊢ (down1_statement s (length Γ)) :$ A).
Proof.
  apply syntax_ind; intros;
  (* try finishing goals that do not require recomputing context splits *)
  try now (
    split; intros H_well_ty; inversion H_well_ty; subst; simpl;
    econstructor;
    unfold ".:"; simpl; try repeat rewrite app_comm_cons;
    try apply H; try apply H0; auto;
    intro Hfv; apply H0; econstructor; eauto
  ).
  + split; intros H_well_ty; inversion H_well_ty; subst.
    - simpl.
      assert (
        exists Γ1' Γ2' Δ1' Δ2',
          Γ1 = Γ1' ++ (None :: Δ1') /\
          Γ2 = Γ2' ++ (None :: Δ2') /\
          Γ ≜ Γ1' ∘ Γ2'   /\
          Δ ≜ Δ1' ∘ Δ2'   /\
          length Γ = length Γ1' /\
          length Γ = length Γ2'
      ) as H_new_splits.
      {
        pose proof (ctx_split_app_inversion _ _ _ _ H4).
        destruct H2 as [Γ1' [Γ2' [Δ1'' [Δ2'' [? [? [? [? [? ?]]]]]]]]].
        inversion H8; subst.
        exists Γ1', Γ2', Γ3, Γ4. inversion H13; subst.
        repeat try split; auto.
      }
      destruct H_new_splits as [Γ1' [Γ2' [Δ1' [Δ2' [? [? [? [? [? ?]]]]]]]]].
      assert (
        Γ ++ None :: Δ ≜ Γ1' ++ None :: Δ1' ∘ Γ2' ++ None :: Δ2'
      ).
      { eapply ctx_split_distribution; try repeat econstructor; eauto. }
      assert (
        Γ ++ Δ ≜ Γ1' ++ Δ1' ∘ Γ2' ++ Δ2'
      ).
      { eapply ctx_split_distribution; eauto. }
      econstructor; eauto.
      * rewrite H9. eapply H.
        ** intro Hfv. apply H1. constructor. rewrite H9; auto.
        ** rewrite H2 in H6. eassumption.
      * rewrite H10. eapply H0.
        ** intro Hfv. apply H1. apply fv_link_r. rewrite H10; auto.
        ** rewrite H3 in H7. eassumption.
    - simpl.
      assert (
        exists Γ1' Γ2' Δ1' Δ2',
          Γ1 = Γ1' ++ Δ1' /\
          Γ2 = Γ2' ++ Δ2' /\
          Γ ≜ Γ1' ∘ Γ2'   /\
          Δ ≜ Δ1' ∘ Δ2'   /\
          length Γ = length Γ1' /\
          length Γ = length Γ2'
      ) as H_new_splits by apply (ctx_split_app_inversion _ _ _ _ H4).
      destruct H_new_splits as [Γ1' [Γ2' [Δ1' [Δ2' [? [? [? [? [? ?]]]]]]]]].
      assert (
        Γ ++ None :: Δ ≜ Γ1' ++ None :: Δ1' ∘ Γ2' ++ None :: Δ2'
      ).
      { eapply ctx_split_distribution; try repeat econstructor; eauto. }
      assert (
        Γ ++ Δ ≜ Γ1' ++ Δ1' ∘ Γ2' ++ Δ2'
      ) by (eapply ctx_split_distribution; eauto).
      econstructor; eauto.
      * eapply H.
        ** intro Hfv. apply H1. constructor. rewrite H9; auto.
        ** rewrite <- H2. rewrite <- H9. eassumption.
      * eapply H0.
        ** intro Hfv. apply H1. apply fv_link_r. rewrite H10; auto.
        ** rewrite <- H3. rewrite <- H10. eassumption.
  + split; intros H_well_ty; inversion H_well_ty; subst.
    - simpl.
      assert (
        exists Γ1' Γ2' Δ1' Δ2',
          Γ1 = Γ1' ++ (None :: Δ1') /\
          Γ2 = Γ2' ++ (None :: Δ2') /\
          Γ ≜ Γ1' ∘ Γ2'   /\
          Δ ≜ Δ1' ∘ Δ2'   /\
          length Γ = length Γ1' /\
          length Γ = length Γ2'
      ) as H_new_splits.
      {
        pose proof (ctx_split_app_inversion _ _ _ _ H4).
        destruct H2 as [Γ1' [Γ2' [Δ1'' [Δ2'' [? [? [? [? [? ?]]]]]]]]].
        inversion H8; subst.
        exists Γ1', Γ2', Γ3, Γ4. inversion H13; subst.
        repeat try split; auto.
      }
      destruct H_new_splits as [Γ1' [Γ2' [Δ1' [Δ2' [? [? [? [? [? ?]]]]]]]]].
      assert (
        Γ ++ None :: Δ ≜ Γ1' ++ None :: Δ1' ∘ Γ2' ++ None :: Δ2'
      ).
      { eapply ctx_split_distribution; try repeat econstructor; eauto. }
      assert (
        Γ ++ Δ ≜ Γ1' ++ Δ1' ∘ Γ2' ++ Δ2'
      ).
      { eapply ctx_split_distribution; eauto. }
      eapply t_cut with (A := A); eauto; unfold ".:"; simpl.
      * rewrite H9.
        change (S (length Γ1')) with (length (Some A :: Γ1')).
        rewrite List.app_comm_cons.
        eapply H.
        ** intro Hfv. apply H1. constructor. rewrite H9; auto.
        ** rewrite H2 in H6. eassumption.
      * rewrite H10.
        change (S (length Γ1')) with (length (Some A :: Γ1')).
        rewrite List.app_comm_cons.
        eapply H0.
        ** intro Hfv. apply H1. apply fv_cut_r. rewrite H10; auto.
        ** rewrite H3 in H7. eassumption.
    - simpl.
      assert (
        exists Γ1' Γ2' Δ1' Δ2',
          Γ1 = Γ1' ++ Δ1' /\
          Γ2 = Γ2' ++ Δ2' /\
          Γ ≜ Γ1' ∘ Γ2'   /\
          Δ ≜ Δ1' ∘ Δ2'   /\
          length Γ = length Γ1' /\
          length Γ = length Γ2'
      ) as H_new_splits by apply (ctx_split_app_inversion _ _ _ _ H4).
      destruct H_new_splits as [Γ1' [Γ2' [Δ1' [Δ2' [? [? [? [? [? ?]]]]]]]]].
      assert (
        Γ ++ None :: Δ ≜ Γ1' ++ None :: Δ1' ∘ Γ2' ++ None :: Δ2'
      ).
      { eapply ctx_split_distribution; try repeat econstructor; eauto. }
      assert (
        Γ ++ Δ ≜ Γ1' ++ Δ1' ∘ Γ2' ++ Δ2'
      ) by (eapply ctx_split_distribution; eauto).
      eapply t_cut with (A := A); eauto; unfold ".:"; simpl.
      * rewrite List.app_comm_cons.
        apply H.
        ** intro Hfv. apply H1. constructor. rewrite H9; auto.
        ** simpl.
           rewrite H2 in H6.
           rewrite H9 in H6.
           assumption.
      * rewrite List.app_comm_cons.
        apply H0.
        ** intro Hfv. apply H1. apply fv_cut_r. rewrite H10; auto.
        ** simpl.
           rewrite H3 in H7.
           rewrite H10 in H7.
           assumption.
  + split; intros H_well_ty; inversion H_well_ty; subst.
    - simpl.
      assert (
        exists Γ1' Γ2' Δ1' Δ2',
          Γ1 = Γ1' ++ (None :: Δ1') /\
          Γ2 = Γ2' ++ (None :: Δ2') /\
          Γ ≜ Γ1' ∘ Γ2'   /\
          Δ ≜ Δ1' ∘ Δ2'   /\
          length Γ = length Γ1' /\
          length Γ = length Γ2'
      ) as H_new_splits.
      {
        pose proof (ctx_split_app_inversion _ _ _ _ H4).
        destruct H2 as [Γ1' [Γ2' [Δ1'' [Δ2'' [? [? [? [? [? ?]]]]]]]]].
        inversion H8; subst.
        exists Γ1', Γ2', Γ3, Γ4. inversion H13; subst.
        repeat try split; auto.
      }
      destruct H_new_splits as [Γ1' [Γ2' [Δ1' [Δ2' [? [? [? [? [? ?]]]]]]]]].
      assert (
        Γ ++ None :: Δ ≜ Γ1' ++ None :: Δ1' ∘ Γ2' ++ None :: Δ2'
      ).
      { eapply ctx_split_distribution; try repeat econstructor; eauto. }
      assert (
        Γ ++ Δ ≜ Γ1' ++ Δ1' ∘ Γ2' ++ Δ2'
      ).
      { eapply ctx_split_distribution; eauto. }
      eapply t_seq with (A := A); eauto; unfold ".:"; simpl.
      * rewrite H9.
        change (S (length Γ1')) with (length (Some A :: Γ1')).
        rewrite List.app_comm_cons.
        eapply H.
        ** intro Hfv. apply H1. constructor. rewrite H9; auto.
        ** rewrite H2 in H6. eassumption.
      * rewrite H10.
        change (S (length Γ1')) with (length (Some A :: Γ1')).
        eapply H0.
        ** intro Hfv. apply H1. apply fv_seq_r. rewrite H10; auto.
        ** rewrite H3 in H7. eassumption.
    - simpl.
      assert (
        exists Γ1' Γ2' Δ1' Δ2',
          Γ1 = Γ1' ++ Δ1' /\
          Γ2 = Γ2' ++ Δ2' /\
          Γ ≜ Γ1' ∘ Γ2'   /\
          Δ ≜ Δ1' ∘ Δ2'   /\
          length Γ = length Γ1' /\
          length Γ = length Γ2'
      ) as H_new_splits by apply (ctx_split_app_inversion _ _ _ _ H4).
      destruct H_new_splits as [Γ1' [Γ2' [Δ1' [Δ2' [? [? [? [? [? ?]]]]]]]]].
      assert (
        Γ ++ None :: Δ ≜ Γ1' ++ None :: Δ1' ∘ Γ2' ++ None :: Δ2'
      ).
      { eapply ctx_split_distribution; try repeat econstructor; eauto. }
      assert (
        Γ ++ Δ ≜ Γ1' ++ Δ1' ∘ Γ2' ++ Δ2'
      ) by (eapply ctx_split_distribution; eauto).
      eapply t_seq with (A := A); eauto; unfold ".:"; simpl.
      * rewrite List.app_comm_cons.
        apply H.
        ** intro Hfv. apply H1. constructor. rewrite H9; auto.
        ** simpl.
           rewrite H2 in H6.
           rewrite H9 in H6.
           assumption.
      * apply H0.
        ** intro Hfv. apply H1. apply fv_seq_r. rewrite H10; auto.
        ** simpl.
           rewrite H3 in H7.
           rewrite H10 in H7.
           assumption.
  + split; intros H_well_ty; inversion H_well_ty; subst; simpl; econstructor.
    - apply ctx_empty_insert_none; auto.
    - apply (proj1 (ctx_empty_insert_none Γ Δ)). assumption.
  + split; intros H_well_ty.
    - inversion H_well_ty; subst.
      simpl.
      (* decide whether we downshift or not *)
      destruct (Nat.ltb (length Γ) n) eqn:E.
      * apply PeanoNat.Nat.ltb_lt in E.
        destruct n.
        ** inversion E.
        ** simpl. econstructor. intro i.
           destruct (Compare_dec.lt_dec i (length Γ)).
           *** rewrite ctx_lookup_app; try lia.
               rewrite ctx_lookup_singleton_neq; try lia.
               unfold ctx_eq in H2. specialize H2 with i.
               rewrite ctx_lookup_app in H2; try lia.
               rewrite ctx_lookup_singleton_neq in H2; try lia.
               assumption.
           *** unfold ctx_eq in H2.
               specialize H2 with (S i).
               rewrite ctx_lookup_app_minus; try lia.
               rewrite ctx_lookup_app_minus in H2; try lia.
               destruct (PeanoNat.Nat.eq_dec i n).
               **** subst.
                    rewrite ctx_lookup_after_insert.
                    rewrite ctx_lookup_after_insert in H2.
                    rewrite <- H2.
                    assert (S n - length Γ = S (n - length Γ)) by lia.
                    rewrite H0. simpl. reflexivity.
               **** rewrite ctx_lookup_singleton_neq; try lia.
                    rewrite ctx_lookup_singleton_neq in H2; try lia.
                    rewrite <- H2.
                    assert (S i - length Γ = S (i - length Γ)) by lia.
                    rewrite H0.
                    reflexivity.
      * apply PeanoNat.Nat.ltb_ge in E.
        inversion E; subst.
        ** (* length Γ = n -> contradiction from H1 *)
           exfalso.
           unfold ctx_eq in H2.
           specialize H2 with (length Γ).
           rewrite ctx_lookup_after_insert in H2.
           rewrite ctx_lookup_app_length in H2.
           *** apply 1. (* TODO: refactor ctx_lookup_after_length *)
           *** simpl in H2. discriminate.
        ** (* length Γ > n *)
           econstructor. intro i.
           (* 1. i < length Γ *)
           destruct (Compare_dec.lt_dec i (length Γ)).
           *** rewrite ctx_lookup_app; try lia.
               unfold ctx_eq in H2.
               specialize H2 with i.
               rewrite ctx_lookup_app in H2; try lia.
               assumption.
           (* 2. i >= length Γ *)
           *** assert (i <> n) by lia.
               rewrite ctx_lookup_singleton_neq; auto.
               unfold ctx_eq in H2.
               specialize H2 with (S i).
               assert (S i <> n) by lia.
               rewrite ctx_lookup_singleton_neq in H2; auto.
               rewrite <- H2.
               rewrite ctx_lookup_app_minus; try lia.
               rewrite ctx_lookup_app_minus; try lia.
               assert ((S i - length Γ) = (S (i - length Γ))) by lia.
               rewrite H5. simpl. reflexivity.
    - (* use the fact that length Γ does not occur free *)
      assert (n <> length Γ) as H_n.
      {
        destruct (PeanoNat.Nat.eq_dec n (length Γ)); auto.
        subst.
        exfalso.
        apply H. constructor.
      }
      simpl in H_well_ty.
      destruct (Nat.ltb (length Γ) n) eqn:E.
      * apply PeanoNat.Nat.ltb_lt in E. clear H_n.
        destruct n; try now inversion E.
        simpl in H_well_ty.
        apply type_id_after_downshift; auto.
      * apply PeanoNat.Nat.ltb_nlt in E.
        assert (n < length Γ) by lia. clear H_n E.
        apply type_id_before_downshift; auto.
  + split; intros H_well_ty; inversion H_well_ty; subst; simpl.
    - econstructor.
      * unfold ".:"; simpl; try repeat rewrite List.app_comm_cons. apply H; auto.
        intro Hfv; simpl in Hfv. apply H1. econstructor. auto.
      * unfold ".:"; simpl; try repeat rewrite List.app_comm_cons. apply H0; auto.
        intro Hfv; simpl in Hfv. apply H1.
        eapply fv_choice_r. assumption.
    - econstructor.
      * unfold ".:"; simpl; try repeat rewrite app_comm_cons. apply H; auto.
        intro Hfv; simpl in Hfv. apply H1. econstructor. auto.
      * unfold ".:"; simpl; try repeat rewrite app_comm_cons. apply H0; auto.
        intro Hfv; simpl in Hfv. apply H1.
        eapply fv_choice_r. assumption.
  + split; intros H_well_ty; inversion H_well_ty; subst.
    - simpl.
      assert (
        exists Γ1' Γ2' Δ1' Δ2',
          Γ1 = Γ1' ++ (None :: Δ1') /\
          Γ2 = Γ2' ++ (None :: Δ2') /\
          Γ ≜ Γ1' ∘ Γ2'   /\
          Δ ≜ Δ1' ∘ Δ2'   /\
          length Γ = length Γ1' /\
          length Γ = length Γ2'
      ) as H_new_splits.
      {
        pose proof (ctx_split_app_inversion _ _ _ _ H4).
        destruct H2 as [Γ1' [Γ2' [Δ1'' [Δ2'' [? [? [? [? [? ?]]]]]]]]].
        inversion H7; subst.
        exists Γ1', Γ2', Γ3, Γ4. inversion H13; subst.
        repeat try split; auto.
      }
      destruct H_new_splits as [Γ1' [Γ2' [Δ1' [Δ2' [? [? [? [? [? ?]]]]]]]]].
      assert (
        Γ ++ None :: Δ ≜ Γ1' ++ None :: Δ1' ∘ Γ2' ++ None :: Δ2'
      ).
      { eapply ctx_split_distribution; try repeat econstructor; eauto. }
      assert (
        Γ ++ Δ ≜ Γ1' ++ Δ1' ∘ Γ2' ++ Δ2'
      ).
      { eapply ctx_split_distribution; eauto. }
      eapply t_tensor with (A := A0) (B := B); eauto; unfold ".:"; simpl.
      * rewrite H9.
        change (S (length Γ1')) with (length (Some (dual A0) :: Γ1')).
        rewrite app_comm_cons.
        eapply H.
        ** intro Hfv. apply H1. constructor. rewrite H9; auto.
        ** rewrite H2 in H6. eassumption.
      * rewrite H10.
        change (S (length Γ1')) with (length (Some A :: Γ1')).
        rewrite app_comm_cons.
        eapply H0.
        ** intro Hfv. apply H1. apply fv_send_r. rewrite H10; auto.
        ** rewrite H3 in H8. eassumption.
    - simpl.
      assert (
        exists Γ1' Γ2' Δ1' Δ2',
          Γ1 = Γ1' ++ Δ1' /\
          Γ2 = Γ2' ++ Δ2' /\
          Γ ≜ Γ1' ∘ Γ2'   /\
          Δ ≜ Δ1' ∘ Δ2'   /\
          length Γ = length Γ1' /\
          length Γ = length Γ2'
      ) as H_new_splits by apply (ctx_split_app_inversion _ _ _ _ H4).
      destruct H_new_splits as [Γ1' [Γ2' [Δ1' [Δ2' [? [? [? [? [? ?]]]]]]]]].
      assert (
        Γ ++ None :: Δ ≜ Γ1' ++ None :: Δ1' ∘ Γ2' ++ None :: Δ2'
      ).
      { eapply ctx_split_distribution; try repeat econstructor; eauto. }
      assert (
        Γ ++ Δ ≜ Γ1' ++ Δ1' ∘ Γ2' ++ Δ2'
      ) by (eapply ctx_split_distribution; eauto).
      eapply t_tensor with (A := A0) (B := B); eauto; unfold ".:"; simpl.
      * rewrite app_comm_cons.
        apply H.
        ** intro Hfv. apply H1. constructor. rewrite H9; auto.
        ** simpl.
           rewrite H2 in H6.
           rewrite H9 in H6.
           assumption.
      * rewrite app_comm_cons.
        apply H0.
        ** intro Hfv. apply H1. apply fv_send_r. rewrite H10; auto.
        ** simpl.
           rewrite H3 in H8.
           rewrite H10 in H8.
           assumption.
  + split; intros H_well_ty; inversion H_well_ty; subst; simpl.
    - econstructor.
      apply ctx_empty_insert_none; auto.
    - econstructor.
      apply (ctx_empty_insert_none Γ Δ); auto.
Qed.

(* Upshifting is sound when exteding the context with None *)
Lemma up_shift_sound :
  (forall p, forall Γ Δ,
    ((Γ ++ Δ) ⊢ p :# <-> Γ ++ (None :: Δ) ⊢ (lift_process p (length Γ) 1) :#))
  /\
  (forall M, forall Γ Δ A,
    ((Γ ++ Δ) ⊢ M :! A <-> Γ ++ (None :: Δ) ⊢ (lift_message M (length Γ) 1) :! A))
  /\
  (forall s, forall Γ Δ A,
    ((Γ ++ Δ) ⊢ s :$ A <-> Γ ++ (None :: Δ) ⊢ (lift_statement s (length Γ) 1) :$  A)).
Proof.
  (* <- use down_shift_sound and the fact that down after up is id *)
  apply syntax_ind; intros;
  try now (
    split; intros H_well_ty; inversion H_well_ty; subst;
    simpl; econstructor; unfold ".:"; simpl; try repeat rewrite app_comm_cons;
    try apply H; try apply H0; simpl; assumption
  ).
  + split; intros.
    - inversion H1; subst.
      destruct (ctx_split_app_inversion _ _ _ _ H4)
        as [Γ1' [Γ2' [Δ1' [Δ2' [? [? [? [? [? ?]]]]]]]]].
      assert (
        Γ ++ None :: Δ ≜ Γ1' ++ None :: Δ1' ∘ Γ2' ++ None :: Δ2'
      ).
      { eapply ctx_split_distribution; try repeat econstructor; eauto. }
      simpl. econstructor; eauto.
      * rewrite H9; apply H.
        rewrite <- H2; eassumption.
      * rewrite H10; apply H0.
        rewrite <- H3; eassumption.
    - inversion H1; subst.
      assert (
        exists Γ1' Γ2' Δ1' Δ2',
          Γ1 = Γ1' ++ (None :: Δ1') /\
          Γ2 = Γ2' ++ (None :: Δ2') /\
          Γ ≜ Γ1' ∘ Γ2'   /\
          Δ ≜ Δ1' ∘ Δ2'   /\
          length Γ = length Γ1' /\
          length Γ = length Γ2'
      ) as H_new_splits.
      {
        pose proof (ctx_split_app_inversion _ _ _ _ H4).
        destruct H2 as [Γ1' [Γ2' [Δ1'' [Δ2'' [? [? [? [? [? ?]]]]]]]]].
        inversion H8; subst.
        exists Γ1', Γ2', Γ3, Γ4. inversion H13; subst.
        repeat try split; auto.
      }
      destruct H_new_splits as [Γ1' [Γ2' [Δ1' [Δ2' [? [? [? [? [? ?]]]]]]]]].
      assert (
        Γ ++ Δ ≜ Γ1' ++ Δ1' ∘ Γ2' ++ Δ2'
      ).
      { eapply ctx_split_distribution; eauto. }
      econstructor; eauto.
      * apply H. rewrite H2 H9 in H6. eassumption.
      * apply H0. rewrite H3 H10 in H7. eassumption.
  + split; intros.
    - inversion H1; subst.
      destruct (ctx_split_app_inversion _ _ _ _ H4)
        as [Γ1' [Γ2' [Δ1' [Δ2' [? [? [? [? [? ?]]]]]]]]].
      assert (
        Γ ++ None :: Δ ≜ Γ1' ++ None :: Δ1' ∘ Γ2' ++ None :: Δ2'
      ).
      { eapply ctx_split_distribution; try repeat econstructor; eauto. }
      simpl. eapply t_cut with (A := A). eauto.
      * rewrite H9. unfold ".:". simpl. rewrite app_comm_cons.
        change (S (length Γ1')) with (length (Some A :: Γ1')).
        apply H. simpl.
        rewrite <- H2. eassumption.
      * rewrite H10. unfold ".:". simpl. rewrite app_comm_cons.
        change (S (length Γ2')) with (length (Some (dual A) :: Γ2')).
        apply H0. simpl.
        rewrite <- H3; eassumption.
    - inversion H1; subst.
      assert (
        exists Γ1' Γ2' Δ1' Δ2',
          Γ1 = Γ1' ++ (None :: Δ1') /\
          Γ2 = Γ2' ++ (None :: Δ2') /\
          Γ ≜ Γ1' ∘ Γ2'   /\
          Δ ≜ Δ1' ∘ Δ2'   /\
          length Γ = length Γ1' /\
          length Γ = length Γ2'
      ) as H_new_splits.
      {
        pose proof (ctx_split_app_inversion _ _ _ _ H4).
        destruct H2 as [Γ1' [Γ2' [Δ1'' [Δ2'' [? [? [? [? [? ?]]]]]]]]].
        inversion H8; subst.
        exists Γ1', Γ2', Γ3, Γ4. inversion H13; subst.
        repeat try split; auto.
      }
      destruct H_new_splits as [Γ1' [Γ2' [Δ1' [Δ2' [? [? [? [? [? ?]]]]]]]]].
      assert (
        Γ ++ Δ ≜ Γ1' ++ Δ1' ∘ Γ2' ++ Δ2'
      ).
      { eapply ctx_split_distribution; eauto. }
      eapply t_cut with (A := A). eauto.
      * unfold ".:". simpl. rewrite app_comm_cons.
        apply H. simpl.
        rewrite <- H2. rewrite <- H9. eassumption.
      * unfold ".:". simpl. rewrite app_comm_cons.
        apply H0. simpl.
        rewrite <- H3. rewrite <- H10. eassumption.
  + split; intros.
    - inversion H1; subst.
      destruct (ctx_split_app_inversion _ _ _ _ H4)
        as [Γ1' [Γ2' [Δ1' [Δ2' [? [? [? [? [? ?]]]]]]]]].
      assert (
        Γ ++ None :: Δ ≜ Γ1' ++ None :: Δ1' ∘ Γ2' ++ None :: Δ2'
      ).
      { eapply ctx_split_distribution; try repeat econstructor; eauto. }
      simpl. eapply t_seq with (A := A). eauto.
      * rewrite H9. unfold ".:". simpl. rewrite app_comm_cons.
        change (S (length Γ1')) with (length (Some A :: Γ1')).
        apply H. simpl.
        rewrite <- H2. eassumption.
      * rewrite H10. unfold ".:". simpl.
        change (S (length Γ2')) with (length (Some (dual A) :: Γ2')).
        apply H0. simpl.
        rewrite <- H3; eassumption.
    - inversion H1; subst.
      assert (
        exists Γ1' Γ2' Δ1' Δ2',
          Γ1 = Γ1' ++ (None :: Δ1') /\
          Γ2 = Γ2' ++ (None :: Δ2') /\
          Γ ≜ Γ1' ∘ Γ2'   /\
          Δ ≜ Δ1' ∘ Δ2'   /\
          length Γ = length Γ1' /\
          length Γ = length Γ2'
      ) as H_new_splits.
      {
        pose proof (ctx_split_app_inversion _ _ _ _ H4).
        destruct H2 as [Γ1' [Γ2' [Δ1'' [Δ2'' [? [? [? [? [? ?]]]]]]]]].
        inversion H8; subst.
        exists Γ1', Γ2', Γ3, Γ4. inversion H13; subst.
        repeat try split; auto.
      }
      destruct H_new_splits as [Γ1' [Γ2' [Δ1' [Δ2' [? [? [? [? [? ?]]]]]]]]].
      assert (
        Γ ++ Δ ≜ Γ1' ++ Δ1' ∘ Γ2' ++ Δ2'
      ).
      { eapply ctx_split_distribution; eauto. }
      eapply t_seq with (A := A). eauto.
      * unfold ".:". simpl. rewrite app_comm_cons.
        apply H. simpl.
        rewrite <- H2. rewrite <- H9. eassumption.
      * unfold ".:". simpl.
        apply H0. simpl.
        rewrite <- H3. rewrite <- H10. eassumption.
  + split; intros H_well_ty; inversion H_well_ty; subst; simpl; econstructor.
    - apply (proj1 (ctx_empty_insert_none Γ Δ)). assumption.
    - apply ctx_empty_insert_none; auto.
  + split; intros H_well_ty; inversion H_well_ty; subst.
    - simpl. econstructor. intro i. unfold ctx_eq in H1.
      unfold relocate.
      destruct (Nat.leb (length Γ) n) eqn:E; simpl.
      * apply Compare_dec.leb_complete in E.
        destruct (Compare_dec.lt_dec i (length Γ)).
        ** rewrite ctx_lookup_app; auto.
           rewrite ctx_lookup_singleton_neq; try lia.
           specialize H1 with i.
           rewrite ctx_lookup_singleton_neq in H1; try lia.
           rewrite ctx_lookup_app in H1; auto.
        ** destruct (PeanoNat.Nat.eq_dec i (length Γ)).
           *** subst.
               rewrite ctx_lookup_app_minus; try lia.
               rewrite PeanoNat.Nat.sub_diag; simpl.
               rewrite ctx_lookup_singleton_neq; try lia; auto.
           *** destruct i.
               -- assert (1 < 0) by lia. inversion H.
               -- rewrite ctx_lookup_app_minus; try lia.
                  replace (S i - length Γ) with (S (i - length Γ)) by lia.
                  simpl.
                  specialize H1 with i.
                  rewrite ctx_lookup_app_minus in H1; try lia.
                  rewrite H1. reflexivity.
      * apply PeanoNat.Nat.leb_gt in E.
        destruct (Compare_dec.lt_dec i (length Γ)).
        ** specialize H1 with i.
           rewrite ctx_lookup_app; try lia.
           rewrite ctx_lookup_app in H1; try lia.
           auto.
        ** rewrite ctx_lookup_singleton_neq; try lia.
           destruct (PeanoNat.Nat.eq_dec i (length Γ)).
           -- subst. rewrite ctx_lookup_app_minus; try lia.
              rewrite PeanoNat.Nat.sub_diag; reflexivity.
           -- destruct i.
               --- assert (1 < 0) by lia. inversion H.
               --- rewrite ctx_lookup_app_minus; try lia.
                   replace (S i - length Γ) with (S (i - length Γ)) by lia.
                   simpl.
                   specialize H1 with i.
                   rewrite ctx_lookup_app_minus in H1; try lia.
                   rewrite H1. rewrite ctx_lookup_singleton_neq; try lia. auto.
    - simpl. econstructor. intro i. unfold ctx_eq in H1.
      unfold relocate in H1.
      destruct (Nat.leb (length Γ) n) eqn:E; simpl.
      * apply Compare_dec.leb_complete in E.
        destruct (Compare_dec.lt_dec i (length Γ)).
        ** rewrite ctx_lookup_app; auto.
           rewrite ctx_lookup_singleton_neq; try lia.
           specialize H1 with i.
           rewrite ctx_lookup_singleton_neq in H1; try lia.
           rewrite ctx_lookup_app in H1; auto.
        ** destruct (PeanoNat.Nat.eq_dec i n).
           *** subst.
               specialize H1 with (S n).
               rewrite ctx_lookup_after_insert.
               rewrite ctx_lookup_after_insert in H1.
               rewrite <- H1.
               rewrite ctx_lookup_app_minus; try lia.
               rewrite ctx_lookup_app_minus; try lia.
               replace (S n - length Γ) with (S (n - length Γ)) by lia.
               reflexivity.
           *** specialize H1 with (S i).
               rewrite ctx_lookup_singleton_neq; try lia.
               rewrite ctx_lookup_singleton_neq in H1; simpl; try lia.
               rewrite <- H1.
               rewrite ctx_lookup_app_minus; try lia.
               rewrite ctx_lookup_app_minus; try lia.
               replace (S i - length Γ) with (S (i - length Γ)) by lia.
               reflexivity.
      * apply PeanoNat.Nat.leb_gt in E.
        destruct (Compare_dec.lt_dec i (length Γ)).
        ** specialize H1 with i.
           rewrite ctx_lookup_app; try lia.
           rewrite ctx_lookup_app in H1; try lia.
           auto.
        ** rewrite ctx_lookup_singleton_neq; try lia.
           destruct (PeanoNat.Nat.eq_dec i (length Γ)).
           -- subst. rewrite ctx_lookup_app_minus; try lia.
              specialize H1 with (S (length Γ)).
              rewrite PeanoNat.Nat.sub_diag.
              rewrite ctx_lookup_singleton_neq in H1; try lia.
              rewrite <- H1.
              rewrite ctx_lookup_app_minus; try lia.
              replace (S (length Γ) - length Γ) with 1 by lia.
              reflexivity.
           -- destruct i.
               --- assert (1 < 0) by lia. inversion H.
               --- rewrite ctx_lookup_app_minus; try lia.
                   replace (S i - length Γ) with (S (i - length Γ)) by lia.
                   specialize H1 with (S (S i)).
                   rewrite ctx_lookup_app_minus in H1; try lia.
                   rewrite ctx_lookup_singleton_neq in H1; try lia.
                   rewrite <- H1.
                   replace (S (S i) - length Γ) with (S (S (i - length Γ))) by lia.
                   reflexivity.
  + split; intros.
    - inversion H1; subst.
      destruct (ctx_split_app_inversion _ _ _ _ H4)
        as [Γ1' [Γ2' [Δ1' [Δ2' [? [? [? [? [? ?]]]]]]]]].
      assert (
        Γ ++ None :: Δ ≜ Γ1' ++ None :: Δ1' ∘ Γ2' ++ None :: Δ2'
      ).
      { eapply ctx_split_distribution; try repeat econstructor; eauto. }
      simpl. eapply t_tensor with (A := A0). eauto.
      * rewrite H9. unfold ".:". simpl. rewrite app_comm_cons.
        change (S (length Γ1')) with (length (Some (dual A0) :: Γ1')).
        apply H. simpl.
        rewrite <- H2. eassumption.
      * rewrite H10. unfold ".:". simpl. rewrite app_comm_cons.
        change (S (length Γ2')) with (length (Some (dual B) :: Γ2')).
        apply H0. simpl.
        rewrite <- H3; eassumption.
    - inversion H1; subst.
      assert (
        exists Γ1' Γ2' Δ1' Δ2',
          Γ1 = Γ1' ++ (None :: Δ1') /\
          Γ2 = Γ2' ++ (None :: Δ2') /\
          Γ ≜ Γ1' ∘ Γ2'   /\
          Δ ≜ Δ1' ∘ Δ2'   /\
          length Γ = length Γ1' /\
          length Γ = length Γ2'
      ) as H_new_splits.
      {
        pose proof (ctx_split_app_inversion _ _ _ _ H4).
        destruct H2 as [Γ1' [Γ2' [Δ1'' [Δ2'' [? [? [? [? [? ?]]]]]]]]].
        inversion H7; subst.
        exists Γ1', Γ2', Γ3, Γ4. inversion H13; subst.
        repeat try split; auto.
      }
      destruct H_new_splits as [Γ1' [Γ2' [Δ1' [Δ2' [? [? [? [? [? ?]]]]]]]]].
      assert (
        Γ ++ Δ ≜ Γ1' ++ Δ1' ∘ Γ2' ++ Δ2'
      ).
      { eapply ctx_split_distribution; eauto. }
      eapply t_tensor with (A := A0) (B := B). eauto.
      * unfold ".:". simpl. rewrite app_comm_cons.
        apply H. simpl.
        rewrite <- H2. rewrite <- H9. eassumption.
      * unfold ".:". simpl. rewrite app_comm_cons.
        apply H0. simpl.
        rewrite <- H3. rewrite <- H10. eassumption.
  + split; intros H_well_ty; inversion H_well_ty; subst; simpl.
    - econstructor.
      apply (ctx_empty_insert_none Γ Δ); auto.
    - econstructor.
      apply ctx_empty_insert_none; auto.
Qed.

(******************************************************************************)
(* Up and Downshift cancel each other                                         *)
(******************************************************************************)
Lemma down_after_up_id :
  (forall (p : process), forall (k : nat),
    down1_process (lift_process p k 1) k = p)
  /\
  (forall (m : message), forall (k : nat),
    down1_message (lift_message m k 1) k = m)
  /\
  (forall (s : statement), forall (k : nat),
    down1_statement (lift_statement s k 1) k = s).
Proof.
  apply syntax_ind; intros; simpl;
  try rewrite H; try rewrite H0; auto.
  unfold relocate.
  destruct (Nat.leb k n) eqn:E.
  + apply PeanoNat.Nat.leb_le in E. simpl.
    assert (k < S n) by lia.
    apply PeanoNat.Nat.ltb_lt in H. rewrite H. reflexivity.
  + apply PeanoNat.Nat.leb_gt in E. assert (~ (k < n)) by lia.
    apply PeanoNat.Nat.ltb_nlt in H. rewrite H. reflexivity.
Qed.

Corollary down_after_up_process_id :
  forall P, down (up P) = P.
Proof. intros; unfold down, up; apply (proj1 down_after_up_id). Qed.

Lemma up_after_down_id :
  (forall (p : process), forall (k : nat),
    ~ (k ∈ p) -> lift_process (down1_process p k) k 1 = p)
  /\
  (forall (m : message), forall (k : nat),
    ~ (occurs_free_message k m) -> lift_message (down1_message m k) k 1 = m)
  /\
  (forall (s : statement), forall (k : nat),
    ~ (occurs_free_statement k s) -> lift_statement (down1_statement s k) k 1 = s).
Proof.
  apply syntax_ind; intros; simpl; auto;
  try rewrite H; try rewrite H0; auto; try intros Hfv;
  try ( match goal with [ H : ~ _ |- _ ] => apply H; free_var_econstructor; eauto end ).
  assert (k <> n).
  { intro Heq. rewrite Heq in H. apply H. free_var_econstructor. }
  destruct (Nat.ltb k n) eqn:E.
  + apply PeanoNat.Nat.ltb_lt in E.
    simpl. unfold relocate. assert (k <= (Nat.pred n)) by lia.
    apply Compare_dec.leb_correct in H1. rewrite H1.
    simpl. f_equal. lia.
  + simpl. unfold relocate. apply PeanoNat.Nat.leb_gt in E.
    assert (~ (k <= n)) by lia. apply PeanoNat.Nat.leb_nle in H1.
    rewrite H1. reflexivity.
Qed.

Corollary up_after_down_process_id :
  forall P, ~ 0 ∈ P -> up (down P) = P.
Proof. intros; unfold up, down; apply up_after_down_id; auto. Qed.
