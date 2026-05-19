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

From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Relations.Operators_Properties.
From Stdlib Require Import Relation_Definitions.
From Stdlib Require Import Lia.

(* ⊵ trianglerighteq *)
Reserved Notation "P ⊵ Q" (no associativity, at level 61).

Inductive equiv_reduces : process -> process -> Prop :=
  (* make ⊵ reflexive *)
  | rp_refl : forall P, P ⊵ P

  (* duplicate β-redexes up to symmetry of links *)
  | rp_tensor_par_1 : forall P P' Q R,
      P' = rename_process (up P) swap01 ->
      link (prefix (send P Q)) (prefix (receive R)) ⊵ (cut (cut R P')) Q
  | rp_tensor_par_2 : forall P P' Q R,
      P' = rename_process (up P) swap01 ->
      link (prefix (receive R)) (prefix (send P Q)) ⊵ (cut (cut R P')) Q
  | rp_plus_with_l1 : forall P Q R,
      link (prefix (choose_left P)) (prefix (offer_choice Q R)) ⊵ cut P Q
  | rp_plus_with_l2 : forall P Q R,
      link (prefix (offer_choice Q R)) (prefix (choose_left P)) ⊵ cut P Q
  | rp_plus_with_r1 : forall P Q R,
      link (prefix (choose_right P)) (prefix (offer_choice Q R)) ⊵ cut P R
  | rp_plus_with_r2 : forall P Q R,
      link (prefix (offer_choice Q R)) (prefix (choose_right P)) ⊵ cut P R
  | rp_one_bot1 : forall P, link (prefix close) (prefix (wait P)) ⊵ P
  | rp_one_bot2 : forall P, link (prefix (wait P)) (prefix close) ⊵ P

  (* AxCut (duplicated to account for symmetry) *)
  | rp_ax_cut_l : forall P Q (E : axcut_ctx) M R,
      Q = fill_hole E M ->
      well_formed_axcut_ctx 0 E ->
      R = reduce_axcut E M P ->
      equiv_reduces (cut Q P) R
  | rp_ax_cut_r : forall P Q (E : axcut_ctx) M R,
      Q = fill_hole E M ->
      well_formed_axcut_ctx 0 E ->
      R = reduce_axcut E M P ->
      equiv_reduces (cut P Q) R

  (* seq *)
  | rp_seq : forall P s, seq P s ⊵ subst_process P ((prefix s) ⋅ id_subst)

  (* congruences *)
  | rp_cong_cut_l : forall P P' Q, P ⊵ P' -> cut P Q ⊵ cut P' Q
  | rp_cong_cut_r : forall P Q Q', Q ⊵ Q' -> cut P Q ⊵ cut P Q'
  | rp_cong_seq : forall P P' s, P ⊵ P' -> seq P s ⊵ seq P' s
where
  "P ⊵ Q" := (equiv_reduces P Q).

Definition par_reduction := (union _ equiv_reduces structural_congruence).

(* twoheadrightarrow *)
Notation "P '↠' Q" := (par_reduction P Q) (no associativity, at level 61).

(* ⇛* ⊂ ↠* *)
Lemma clos_trans_1n_directed_cong_in_clos_trans_1n_par_reduction :
  forall P Q, (clos_trans_1n _ directed_congruence) P Q -> (clos_trans_1n _ par_reduction) P Q.
Proof.
  intros. induction H.
  + econstructor. right. econstructor. apply c_comm. apply directed_cong_in_struct_cong. auto.
  + eapply Relation_Operators.t1n_trans.
    - right. apply directed_cong_in_struct_cong. eassumption.
    - auto.
Qed.

(* (▷ ∪ ≡) ⊂ ↠* *)
Lemma single_step_struct_cong_in_clos_trans_par_reduction :
  forall P Q, (union _ reduces structural_congruence) P Q -> (clos_trans _ par_reduction) P Q.
Proof.
  intros. destruct H.
  + induction H.
    - econstructor. econstructor. eapply rp_tensor_par_1; eauto; apply c_refl.
    - econstructor. econstructor. eapply rp_plus_with_l1; eauto; apply c_refl.
    - econstructor. econstructor. eapply rp_plus_with_r1; eauto; apply c_refl.
    - econstructor. econstructor. eapply rp_one_bot1.
    - econstructor. econstructor.
      eapply (rp_ax_cut_l _ _ (nil_l 0)).
      * simpl. reflexivity.
      * econstructor.
      * simpl. rewrite reduce_axcut_unfold_eq. simpl. reflexivity.
    - econstructor. econstructor. eapply rp_seq.
    - clear H. induction IHreduces.
      * econstructor. destruct H.
        ** econstructor. apply rp_cong_cut_l; auto.
        ** right. apply c_cong_cut; auto. econstructor.
      * eapply t_trans; eauto.
    - clear H. induction IHreduces.
      * econstructor. destruct H.
        ** econstructor. apply rp_cong_seq; auto.
        ** right. apply c_cong_seq; auto. apply struct_cong_reflS.
      * eapply t_trans; eauto.
    - apply struct_cong_in_trans_directed_cong in H.
      apply struct_cong_in_trans_directed_cong in H1.
      apply clos_trans_1n_directed_cong_in_clos_trans_1n_par_reduction in H.
      apply clos_trans_1n_directed_cong_in_clos_trans_1n_par_reduction in H1.
      apply clos_trans_t1n_iff in H.
      apply clos_trans_t1n_iff in H1.
      eapply t_trans; eauto. eapply t_trans; eauto.
  + apply (proj1 struct_cong_in_trans_directed_cong) in H.
    apply clos_trans_t1n_iff.
    apply clos_trans_1n_directed_cong_in_clos_trans_1n_par_reduction. auto.
Qed.

(* ▶ ⊂ ↠* *)
Lemma multi_step_red_in_clos_trans_par_red :
  forall P Q, P ▶ Q -> (clos_trans _ par_reduction) P Q.
Proof.
  intros. induction H.
  + apply single_step_struct_cong_in_clos_trans_par_reduction in H. auto.
  + eapply Relation_Operators.t_trans; eauto.
Qed.

Ltac directed_cong_to_struct_cong :=
  match goal with
  | [ H : _  ⇛ _ |- _ ] => apply directed_cong_in_struct_cong in H
  | [ H : _ !⇛ _ |- _ ] => apply directed_cong_in_struct_cong in H
  | [ H : _ $⇛ _ |- _ ] => apply directed_cong_in_struct_cong in H
  end.

(* ⊵ ⊂ (⊳ ∪ ≡) *)
Lemma equiv_reduces_in_reduces_or_struct_cong :
  forall P Q, P ⊵ Q -> (union _ reduces structural_congruence) P Q.
Proof.
  intros. induction H;
  try (now (left; econstructor; eauto));
  try (now (left; eapply r_struct; [ apply c_link | econstructor; eauto | apply c_refl ])).
  + right. apply c_refl.
  + econstructor.
    assert ( exists L, (cut Q P) ≡ L /\ L ⊳ R ).
    { eapply equiv_red_axcut_in_reduces_axcut; eauto. }
    destruct H2 as [? [? ?]].
    eapply r_struct; eauto; apply c_refl.
  + econstructor.
    assert ( exists L, (cut Q P) ≡ L /\ L ⊳ R ).
    { eapply equiv_red_axcut_in_reduces_axcut; eauto. }
    destruct H2 as [? [? ?]].
    eapply r_struct.
    - eapply c_trans. eapply c_cut_comm. apply H2.
    - apply H3.
    - apply c_refl.
  + destruct IHequiv_reduces.
    - left. apply r_cong_cut; auto.
    - right. apply c_cong_cut; auto. apply c_refl.
  + destruct IHequiv_reduces.
    - left. eapply r_struct. apply c_cut_comm. apply r_cong_cut. eauto. apply c_cut_comm.
    - right. apply c_cong_cut; auto. apply c_refl.
  + destruct IHequiv_reduces.
    - left. apply r_cong_seq; auto.
    - right. apply c_cong_seq; auto. apply struct_cong_reflS.
Qed.

(* ↠ ⊂ (⊳ ∪ ≡) *)
Lemma par_reduction_in_reduces_or_struct_cong :
  forall P Q, P ↠ Q -> (union _ reduces structural_congruence) P Q.
Proof.
  intros. destruct H.
  - apply equiv_reduces_in_reduces_or_struct_cong; auto.
  - right; auto.
Qed.

(* ↠* ⊂ ▶ *)
Corollary clos_trans_par_red_in_multi_step_red :
  forall P Q, clos_trans process par_reduction P Q -> P ▶ Q.
Proof.
  intros. induction H.
  + apply t_step. apply par_reduction_in_reduces_or_struct_cong. auto.
  + eapply t_trans; eauto.
Qed.

Corollary par_reds_clos_trans_multi_step_red_coincide :
  forall P Q, (clos_trans _ par_reduction) P Q <-> P ▶ Q.
Proof.
  intros; split.
  + apply clos_trans_par_red_in_multi_step_red.
  + apply multi_step_red_in_clos_trans_par_red.
Qed.

(******************************************************************************)
(* Parallel Reductions Preserve Typing                                        *)
(******************************************************************************)
Lemma par_red_preserves_typing :
  forall Γ P Q, Γ ⊢ P :# -> P ↠ Q -> Γ ⊢ Q :#.
Proof.
  intros.
  apply par_reduction_in_reduces_or_struct_cong in H0.
  destruct H0.
  + eapply preservation; eauto.
  + eapply struct_cong_preserves_typing; eauto. apply c_comm; auto.
Qed.

Lemma directed_cong_preserves_typing :
  forall Γ P Q, Γ ⊢ P :# -> P ⇛ Q -> Γ ⊢ Q :#.
Proof.
  intros. apply directed_cong_in_struct_cong in H0.
  apply ((proj1 struct_cong_preserves_typing) _ _ H0) in H; auto.
Qed.

(******************************************************************************)
(* Auxiliary Lemmata for Confluence                                           *)
(******************************************************************************)
Lemma link_directed_cong_equiv_red_commute :
  forall ml mr P Q, (link ml mr) ⇛ P -> (link ml mr) ⊵ Q ->
    exists R, P ⊵ R /\ Q ⇛ R.
Proof.
  intros. inversion H; inversion H0; subst;
  try match goal with
  | [ H1 : (prefix (send _ _))  !⇛ _,
      H2 : (prefix (receive _)) !⇛ _
      |- _ ] =>
    apply directed_cong_inversion_prefix in H1; destruct H1 as [? [? H1']];
    apply directed_cong_inversion_prefix in H2; destruct H2 as [? [? H2']];
    apply directed_cong_inversion_send in H1'; destruct H1' as [? [? [? [? ?]]]];
    apply directed_cong_inversion_receive in H2'; destruct H2' as [? [? ?]];
    subst; eexists; split; 
    [ try eapply rp_tensor_par_1; try eapply rp_tensor_par_2; auto
    | apply dc_cong_cut; auto; apply dc_cong_cut; auto;
      apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective;
      apply directed_cong_invariant_under_upshifting; auto ]
  | [ H1 : (prefix (choose_left _)) !⇛ _,
      H2 : (prefix (offer_choice _ _)) !⇛ _
      |- _ ] =>
    apply directed_cong_inversion_prefix in H1; destruct H1 as [? [? H1']];
    apply directed_cong_inversion_prefix in H2; destruct H2 as [? [? H2']];
    apply directed_cong_inversion_choosel in H1'; destruct H1' as [? [? ?]];
    apply directed_cong_inversion_choice in H2'; destruct H2' as [? [? [? [? ?]]]];
    subst; eexists; split; 
    [ try eapply rp_plus_with_l1; try eapply rp_plus_with_l2; auto
    | apply dc_cong_cut; auto; apply dc_cong_cut; auto;
      apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective;
      apply directed_cong_invariant_under_upshifting; auto ]
  | [ H1 : (prefix (choose_right _)) !⇛ _,
      H2 : (prefix (offer_choice _ _)) !⇛ _
      |- _ ] =>
    apply directed_cong_inversion_prefix in H1; destruct H1 as [? [? H1']];
    apply directed_cong_inversion_prefix in H2; destruct H2 as [? [? H2']];
    apply directed_cong_inversion_chooser in H1'; destruct H1' as [? [? ?]];
    apply directed_cong_inversion_choice in H2'; destruct H2' as [? [? [? [? ?]]]];
    subst; eexists; split; 
    [ try eapply rp_plus_with_r1; try eapply rp_plus_with_r2; auto
    | apply dc_cong_cut; auto; apply dc_cong_cut; auto;
      apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective;
      apply directed_cong_invariant_under_upshifting; auto ]
  | [ H1 : (prefix close) !⇛ _,
      H2 : (prefix (wait _)) !⇛ _
      |- _ ] =>
    apply directed_cong_inversion_prefix in H1; destruct H1 as [? [? H1']];
    apply directed_cong_inversion_prefix in H2; destruct H2 as [? [? H2']];
    apply directed_cong_inversion_close in H1';
    apply directed_cong_inversion_wait in H2'; destruct H2' as [? [? ?]];
    subst; eexists; split; [ try eapply rp_one_bot1; try eapply rp_one_bot2; eauto | auto ]
  end.
  + eexists. split. apply rp_refl. apply dc_cong_link; auto.
  + inversion H; subst.
    - eexists. split. apply rp_refl. econstructor; auto.
    - eexists. split. apply rp_refl. apply dc_link; auto.
Qed.

(* ⊵ is invariant under arbitrary upshift of swap01 ***************************)
(* facts and helpers about substitution *)
Definition swap_subst (σ : substitution) (i j : nat) : substitution :=
  fun x => if (Nat.eqb x i) then σ j else
            if (Nat.eqb x j) then σ i else σ x.

Lemma up_subst_distributes_over_swap_subst :
  forall r σ i j, bijective r ->
    forall x,
      up_subst (fun x => rename_message ((swap_subst σ i j) x) r) x
        = (fun x => rename_message (swap_subst (up_subst σ) (S i) (S j) x) (up_ren r)) x.
Proof.
  intros. destruct x; simpl; auto.
  unfold swap_subst.
  destruct (Nat.eqb x i) eqn:E1.
  + apply PeanoNat.Nat.eqb_eq in E1. assert ((S x) = (S i)) by lia.
    apply PeanoNat.Nat.eqb_eq in H0. rewrite H0. simpl.
    unfold upM.
    rewrite (proj1 (proj2 ren_up_up_ren_commute)); auto.
    intros. exfalso; lia.
  + apply PeanoNat.Nat.eqb_neq in E1. assert ((S x) <> (S i)) by lia.
    apply PeanoNat.Nat.eqb_neq in H0. rewrite H0. simpl.
    destruct (Nat.eqb x j) eqn:E2.
    - unfold upM. rewrite (proj1 (proj2 ren_up_up_ren_commute)); auto. intros; exfalso; lia.
    - unfold upM. rewrite (proj1 (proj2 ren_up_up_ren_commute)); auto. intros; exfalso; lia.
Qed.

Lemma up_subst_distributes_over_swap_subst2 :
  forall r σ i j, bijective r ->
    forall x,
      up_subst (up_subst (fun x => rename_message ((swap_subst σ i j) x) r)) x
        = (fun x => rename_message (swap_subst (up_subst (up_subst σ)) (S (S i)) (S (S j)) x) (up_ren (up_ren r))) x.
Proof.
  intros. destruct x; simpl; auto.
  unfold swap_subst.
  destruct (Nat.eqb (S x) (S (S i))) eqn:E1.
  + simpl. apply PeanoNat.Nat.eqb_eq in E1. inversion E1; subst; simpl.
    unfold upM. rewrite (proj1 (proj2 ren_up_up_ren_commute)).
    - rewrite PeanoNat.Nat.eqb_refl.
      f_equal. rewrite (proj1 (proj2 ren_up_up_ren_commute)); auto.
      intros. exfalso; lia.
    - apply shift_preserves_bijection; auto.
    - intros; exfalso; lia.
  + apply PeanoNat.Nat.eqb_neq in E1. destruct x; simpl; auto.
    assert (x <> i) by lia. apply PeanoNat.Nat.eqb_neq in H0. rewrite H0.
    destruct (Nat.eqb x j) eqn:E2.
    - unfold upM. rewrite (proj1 (proj2 ren_up_up_ren_commute)).
      * f_equal. rewrite (proj1 (proj2 ren_up_up_ren_commute)); auto. intros; exfalso; lia.
      * apply shift_preserves_bijection; auto.
      * intros; exfalso; lia.
    - unfold upM. rewrite (proj1 (proj2 ren_up_up_ren_commute)).
      * f_equal. rewrite (proj1 (proj2 ren_up_up_ren_commute)); auto. intros; exfalso; lia.
      * apply shift_preserves_bijection; auto.
      * intros; exfalso; lia.
Qed.

Lemma subst_extensional :
  (forall P, forall σ1 σ2, (forall x, σ1 x = σ2 x) ->
    subst_process P σ1 = subst_process P σ2) /\
  (forall M, forall σ1 σ2, (forall x, σ1 x = σ2 x) ->
    subst_message M σ1 = subst_message M σ2) /\
  (forall s, forall σ1 σ2, (forall x, σ1 x = σ2 x) ->
    subst_statement s σ1 = subst_statement s σ2).
Proof.
  apply syntax_ind; intros; simpl; auto.
  try (now (try rewrite (H σ1 σ2); auto; try rewrite (H0 σ1 σ2); auto)).
  + rewrite (H _ (up_subst σ2)); try rewrite (H0 _ (up_subst σ2)); auto;
    intros [|]; auto; simpl; rewrite H1; auto.
  + rewrite (H _ (up_subst σ2)); try rewrite (H0 _ σ2); auto;
    intros [|]; auto; simpl; rewrite H1; auto.
  + rewrite (H _ σ2); auto.
  + rewrite (H _ (up_subst σ2)); auto; intros [|]; auto; simpl; rewrite H0; auto.
  + rewrite (H _ (up_subst σ2)); auto; intros [|]; auto; simpl; rewrite H0; auto.
  + rewrite (H _ (up_subst σ2)); try rewrite (H0 _ (up_subst σ2)); auto;
    intros [|]; auto; simpl; rewrite H1; auto.
  + rewrite (H _ (up_subst σ2)); try rewrite (H0 _ (up_subst σ2)); auto;
    intros [|]; auto; simpl; rewrite H1; auto.
  + rewrite (H _ (up_subst (up_subst σ2))); auto; intros [|[|]]; auto;
    simpl; rewrite H0; auto.
  + rewrite (H _ σ2); auto.
Qed.

Lemma up_ren_n_swap_n :
  forall n, up_ren_n n swap01 n = S n.
Proof.
  induction n; auto. simpl. rewrite IHn; auto.
Qed.

Lemma up_ren_n_swap_Sn :
  forall n, up_ren_n n swap01 (S n) = n.
Proof.
  induction n; auto. simpl. rewrite IHn; auto.
Qed.

Lemma up_ren_n_swap_not_nSn :
  forall n j, n <> j -> S n <> j -> up_ren_n n swap01 j = j.
Proof.
  induction n; intros; simpl.
  + destruct j; try (exfalso; lia); destruct j; try (exfalso; lia).
    auto.
  + destruct j; auto; simpl.
    assert (n <> j) by lia.
    assert (S n <> j) by lia.
    rewrite IHn; auto.
Qed.

Lemma up_ren_swap_over_subst :
  (
    forall P, forall σ j,
      rename_process (subst_process P σ) (up_ren_n j swap01) =
      subst_process (rename_process P (up_ren_n (S j) swap01))
                    (fun x => rename_message (swap_subst σ (S j) (S (S j)) x) (up_ren_n j swap01))
  ) /\
  (
    forall M, forall σ j,
      rename_message (subst_message M σ) (up_ren_n j swap01) =
      subst_message (rename_message M (up_ren_n (S j) swap01))
                    (fun x => rename_message (swap_subst σ (S j) (S (S j)) x) (up_ren_n j swap01))
  ) /\
  (
    forall s, forall σ j,
      rename_statement (subst_statement s σ) (up_ren_n j swap01) =
      subst_statement (rename_statement s (up_ren_n (S j) swap01))
                    (fun x => rename_message (swap_subst σ (S j) (S (S j)) x) (up_ren_n j swap01))
  ).
Proof.
  apply syntax_ind; intros; simpl;
  try (now (try rewrite H; try rewrite H0; auto)).
  + replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
    rewrite H. rewrite H0. f_equal.
    - apply (proj1 subst_extensional). intro x.
      rewrite up_subst_distributes_over_swap_subst; auto.
      apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
    - apply (proj1 subst_extensional). intro x.
      rewrite up_subst_distributes_over_swap_subst; auto.
      apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
  + replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
    rewrite H0. f_equal. rewrite H. apply (proj1 subst_extensional). intro x.
    rewrite up_subst_distributes_over_swap_subst; auto.
    apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
  + replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
    f_equal.
    destruct (PeanoNat.Nat.eq_dec (S j) n).
    - subst. rewrite up_ren_n_swap_n.
      unfold swap_subst. assert (S (S j) <> S j) by lia.
      apply PeanoNat.Nat.eqb_neq in H; rewrite H.
      rewrite PeanoNat.Nat.eqb_refl. auto.
    - destruct (PeanoNat.Nat.eq_dec (S (S j)) n).
      * subst. rewrite up_ren_n_swap_Sn. unfold swap_subst.
        rewrite PeanoNat.Nat.eqb_refl. auto.
      * rewrite up_ren_n_swap_not_nSn; auto.
        unfold swap_subst. assert (n <> S j) by lia. assert (n <> S (S j)) by lia.
        apply PeanoNat.Nat.eqb_neq in H, H0.
        rewrite H. rewrite H0. auto.
  + replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
    rewrite H. f_equal. apply (proj1 subst_extensional). intro x.
    rewrite up_subst_distributes_over_swap_subst; auto.
    apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
  + replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
    rewrite H. f_equal. apply (proj1 subst_extensional). intro x.
    rewrite up_subst_distributes_over_swap_subst; auto.
    apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
  + replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
    rewrite H. rewrite H0. f_equal.
    - apply (proj1 subst_extensional). intro x.
      rewrite up_subst_distributes_over_swap_subst; auto.
      apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
    - apply (proj1 subst_extensional). intro x.
      rewrite up_subst_distributes_over_swap_subst; auto.
      apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
  + replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
    rewrite H. rewrite H0. f_equal.
    - apply (proj1 subst_extensional). intro x.
      rewrite up_subst_distributes_over_swap_subst; auto.
      apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
    - apply (proj1 subst_extensional). intro x.
      rewrite up_subst_distributes_over_swap_subst; auto.
      apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
  + f_equal.
    replace (up_ren (up_ren (up_ren_n j swap01))) with (up_ren_n (S (S j)) swap01) by auto.
    rewrite H. apply subst_extensional. intro x.
    rewrite up_subst_distributes_over_swap_subst2; auto.
    apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
Qed.

Lemma up_ren_swap_over_reduce_axcut' :
  forall n E M P j,
    n = length_axcut_ctx E ->
    well_formed_axcut_ctx 0 E ->
    ~ (occurs_free_message n M) ->
    rename_process (reduce_axcut E M P) (up_ren_n j swap01) =
    reduce_axcut
      (rename_axcut_ctx E (up_ren_n (S j) swap01))
      (rename_message M (up_ren_n (length_axcut_ctx E + (S j)) swap01))
      (rename_process P (up_ren_n (S j) swap01)).
Proof.
  intro n.
  induction n; intros; simpl;
  destruct E; simpl in H; try congruence; simpl.
  + repeat rewrite reduce_axcut_equation_1.
    replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
    rewrite (proj1 up_ren_swap_over_subst).
    apply subst_extensional. intros x.
    destruct (PeanoNat.Nat.eq_dec (S j) x).
    - subst. simpl. unfold swap_subst. rewrite PeanoNat.Nat.eqb_refl.
      simpl. rewrite up_ren_n_swap_Sn. auto.
    - unfold swap_subst. assert (x <> S j) by lia.
      apply PeanoNat.Nat.eqb_neq in H2; rewrite H2.
      destruct (Nat.eqb x (S (S j))) eqn:E.
      * simpl. rewrite up_ren_n_swap_n.
        apply PeanoNat.Nat.eqb_eq in E; subst. simpl. auto.
      * simpl. destruct x; simpl.
        ** unfold downM. rewrite (proj1 (proj2 down_ren_up_ren_commute)); auto.
           -- apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
           -- intros; exfalso; lia.
        ** rewrite up_ren_n_swap_not_nSn; auto. apply PeanoNat.Nat.eqb_neq in E; lia.
  + repeat rewrite reduce_axcut_equation_2.
    replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
    rewrite (proj1 up_ren_swap_over_subst).
    apply subst_extensional. intros x.
    destruct (PeanoNat.Nat.eq_dec (S j) x).
    - subst. simpl. unfold swap_subst. rewrite PeanoNat.Nat.eqb_refl.
      simpl. rewrite up_ren_n_swap_Sn. auto.
    - unfold swap_subst. assert (x <> S j) by lia.
      apply PeanoNat.Nat.eqb_neq in H2; rewrite H2.
      destruct (Nat.eqb x (S (S j))) eqn:E.
      * simpl. rewrite up_ren_n_swap_n.
        apply PeanoNat.Nat.eqb_eq in E; subst. simpl. auto.
      * simpl. destruct x; simpl.
        ** unfold downM. rewrite (proj1 (proj2 down_ren_up_ren_commute)); auto.
           -- apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
           -- intros; exfalso; lia.
        ** rewrite up_ren_n_swap_not_nSn; auto. apply PeanoNat.Nat.eqb_neq in E; lia.
  + rewrite reduce_axcut_equation_3; simpl.
    rewrite reduce_axcut_equation_3; simpl.
    f_equal.
    - assert (
        rename_process (rename_process P0 (up_ren (up_ren (up_ren_n j swap01)))) swap01 =
        rename_process (rename_process P0 swap01) (up_ren (up_ren (up_ren_n j swap01)))
      ).
      {
        erewrite (proj1 renamings_compose); auto.
        erewrite (proj1 renamings_compose); auto.
        intros [|[|]]; auto.
      }
      rewrite H2.
      unfold down. rewrite (proj1 down_ren_up_ren_commute); auto.
      * apply shift_preserves_bijection. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
      * intros; exfalso; lia.
      * apply nfv_01_swap. inversion H0; auto.
    - inversion H; subst.
      assert (
        length_axcut_ctx E = length_axcut_ctx (rename_axcut_ctx E swap01)
      ). { rewrite rename_axcut_ctx_preserves_length with (r := swap01); auto. }
      assert (
        well_formed_axcut_ctx 0 (rename_axcut_ctx E swap01)
      ).
      {
        inversion H0; subst.
        replace 0 with (swap01 1) by auto.
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; auto.
      }
      assert (
        ~ (occurs_free_message (length_axcut_ctx E)
           (rename_message M (up_ren_n (length_axcut_ctx E) swap01)))
      ).
      {
        replace (length_axcut_ctx E) with
                ((up_ren_n (length_axcut_ctx E) swap01) (S (length_axcut_ctx E)))
          at 1
          by apply up_ren_n_swap_Sn.
        apply (proj1 (proj2 nfv_under_renaming)); auto.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
      }
      replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
      rewrite (IHn _ _ _ _ H2 H3 H4). f_equal.
      * erewrite rename_axcut_ctx_compose; auto.
        erewrite rename_axcut_ctx_compose; auto.
        intros [|[|]]; auto.
      * rewrite <- rename_axcut_ctx_preserves_length with (r := up_ren (up_ren_n (S j) swap01)).
        replace (up_ren (up_ren_n (length_axcut_ctx E + S j) swap01)) with
                (up_ren_n (S (length_axcut_ctx E + S j)) swap01) by auto.
        replace (S (length_axcut_ctx E + S j)) with
                (length_axcut_ctx E + S (S j)) by lia.
        rewrite <- rename_axcut_ctx_preserves_length with (r := swap01).
        erewrite (proj1 (proj2 renamings_compose)); auto.
        erewrite (proj1 (proj2 renamings_compose)); auto.
        intro x.
        {
          destruct (PeanoNat.Nat.eq_dec (length_axcut_ctx E) x); subst.
          + unfold Basics.compose. rewrite up_ren_n_swap_n.
            assert (
              (up_ren_n (length_axcut_ctx E + S (S j)) swap01 (length_axcut_ctx E)) =
              length_axcut_ctx E
            ). { rewrite up_ren_n_swap_not_nSn; lia. }
            rewrite H5. rewrite up_ren_n_swap_n.
            rewrite up_ren_n_swap_not_nSn; lia.
          + destruct (PeanoNat.Nat.eq_dec (S (length_axcut_ctx E)) x); subst.
            - unfold Basics.compose. rewrite up_ren_n_swap_Sn.
              rewrite (up_ren_n_swap_not_nSn (length_axcut_ctx E + S (S j))); try lia.
              rewrite up_ren_n_swap_Sn. rewrite up_ren_n_swap_not_nSn; lia.
            - unfold Basics.compose.
              rewrite (up_ren_n_swap_not_nSn (length_axcut_ctx E) x); try lia.
              destruct (PeanoNat.Nat.eq_dec (length_axcut_ctx E + S (S j)) x).
              * subst. rewrite up_ren_n_swap_n.
                rewrite up_ren_n_swap_not_nSn; lia.
              * destruct (PeanoNat.Nat.eq_dec (S (length_axcut_ctx E + S (S j))) x).
                ** subst. rewrite up_ren_n_swap_Sn.
                   rewrite up_ren_n_swap_not_nSn; lia.
                ** rewrite (up_ren_n_swap_not_nSn (length_axcut_ctx E + S (S j))); try lia.
                   rewrite up_ren_n_swap_not_nSn; lia.
        }
      * unfold up. rewrite <- (proj1 ren_up_up_ren_commute).
        ** remember (lift_process P 0 1); simpl.
           erewrite (proj1 renamings_compose); auto.
           erewrite (proj1 renamings_compose); auto.
           intros [|[|]]; auto.
        ** apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        ** intros; exfalso; lia.
  + rewrite reduce_axcut_equation_4; simpl.
    rewrite reduce_axcut_equation_4; simpl.
    f_equal.
    - inversion H; subst.
      assert (
        length_axcut_ctx E = length_axcut_ctx (rename_axcut_ctx E swap01)
      ). { rewrite rename_axcut_ctx_preserves_length with (r := swap01); auto. }
      assert (
        well_formed_axcut_ctx 0 (rename_axcut_ctx E swap01)
      ).
      {
        inversion H0; subst.
        replace 0 with (swap01 1) by auto.
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; auto.
      }
      assert (
        ~ (occurs_free_message (length_axcut_ctx E)
           (rename_message M (up_ren_n (length_axcut_ctx E) swap01)))
      ).
      {
        replace (length_axcut_ctx E) with
                ((up_ren_n (length_axcut_ctx E) swap01) (S (length_axcut_ctx E)))
          at 1
          by apply up_ren_n_swap_Sn.
        apply (proj1 (proj2 nfv_under_renaming)); auto.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
      }
      replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
      rewrite (IHn _ _ _ _ H2 H3 H4). f_equal.
      * erewrite rename_axcut_ctx_compose; auto.
        erewrite rename_axcut_ctx_compose; auto.
        intros [|[|]]; auto.
      * rewrite <- rename_axcut_ctx_preserves_length with (r := up_ren (up_ren_n (S j) swap01)).
        replace (up_ren (up_ren_n (length_axcut_ctx E + S j) swap01)) with
                (up_ren_n (S (length_axcut_ctx E + S j)) swap01) by auto.
        replace (S (length_axcut_ctx E + S j)) with
                (length_axcut_ctx E + S (S j)) by lia.
        rewrite <- rename_axcut_ctx_preserves_length with (r := swap01).
        erewrite (proj1 (proj2 renamings_compose)); auto.
        erewrite (proj1 (proj2 renamings_compose)); auto.
        intro x.
        {
          destruct (PeanoNat.Nat.eq_dec (length_axcut_ctx E) x); subst.
          + unfold Basics.compose. rewrite up_ren_n_swap_n.
            assert (
              (up_ren_n (length_axcut_ctx E + S (S j)) swap01 (length_axcut_ctx E)) =
              length_axcut_ctx E
            ). { rewrite up_ren_n_swap_not_nSn; lia. }
            rewrite H5. rewrite up_ren_n_swap_n.
            rewrite up_ren_n_swap_not_nSn; lia.
          + destruct (PeanoNat.Nat.eq_dec (S (length_axcut_ctx E)) x); subst.
            - unfold Basics.compose. rewrite up_ren_n_swap_Sn.
              rewrite (up_ren_n_swap_not_nSn (length_axcut_ctx E + S (S j))); try lia.
              rewrite up_ren_n_swap_Sn. rewrite up_ren_n_swap_not_nSn; lia.
            - unfold Basics.compose.
              rewrite (up_ren_n_swap_not_nSn (length_axcut_ctx E) x); try lia.
              destruct (PeanoNat.Nat.eq_dec (length_axcut_ctx E + S (S j)) x).
              * subst. rewrite up_ren_n_swap_n.
                rewrite up_ren_n_swap_not_nSn; lia.
              * destruct (PeanoNat.Nat.eq_dec (S (length_axcut_ctx E + S (S j))) x).
                ** subst. rewrite up_ren_n_swap_Sn.
                   rewrite up_ren_n_swap_not_nSn; lia.
                ** rewrite (up_ren_n_swap_not_nSn (length_axcut_ctx E + S (S j))); try lia.
                   rewrite up_ren_n_swap_not_nSn; lia.
        }
      * unfold up. rewrite <- (proj1 ren_up_up_ren_commute).
        ** remember (lift_process P 0 1); simpl.
           erewrite (proj1 renamings_compose); auto.
           erewrite (proj1 renamings_compose); auto.
           intros [|[|]]; auto.
        ** apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        ** intros; exfalso; lia.
    - assert (
        rename_process (rename_process P0 (up_ren (up_ren (up_ren_n j swap01)))) swap01 =
        rename_process (rename_process P0 swap01) (up_ren (up_ren (up_ren_n j swap01)))
      ).
      {
        erewrite (proj1 renamings_compose); auto.
        erewrite (proj1 renamings_compose); auto.
        intros [|[|]]; auto.
      }
      rewrite H2.
      unfold down. rewrite (proj1 down_ren_up_ren_commute); auto.
      * apply shift_preserves_bijection. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
      * intros; exfalso; lia.
      * apply nfv_01_swap. inversion H0; auto.
Qed.

Lemma up_ren_swap_over_reduce_axcut :
  forall E M P j,
    well_formed_axcut_ctx 0 E ->
    ~ (occurs_free_message (length_axcut_ctx E) M) ->
    rename_process (reduce_axcut E M P) (up_ren_n j swap01) =
    reduce_axcut
      (rename_axcut_ctx E (up_ren_n (S j) swap01))
      (rename_message M (up_ren_n (length_axcut_ctx E + (S j)) swap01))
      (rename_process P (up_ren_n (S j) swap01)).
Proof.
  intros. eapply up_ren_swap_over_reduce_axcut'; eauto.
Qed.

Lemma equiv_red_invariant_under_swap :
  forall Γ P P', Γ ⊢ P :# -> P ⊵ P' -> forall j,
    rename_process P (up_ren_n j swap01) ⊵ rename_process P' (up_ren_n j swap01).
Proof.
  intros.
  generalize dependent Γ.
  generalize dependent j.
  induction H0; intros; try (now (simpl; econstructor)).
  + simpl. econstructor. rewrite H.
    unfold up. rewrite <- (proj1 ren_up_up_ren_commute).
    - replace (up_ren (up_ren (up_ren_n j swap01))) with (up_ren_n (S (S j)) swap01) by auto.
      rewrite ((proj1 renamings_compose) _
        swap01
        (up_ren_n (S (S j)) swap01)
        (Basics.compose (up_ren_n (S (S j)) swap01) swap01)).
      {
        rewrite ((proj1 renamings_compose) _
        (up_ren_n (S (S j)) swap01)
        swap01
        (Basics.compose (up_ren_n (S (S j)) swap01) swap01)); auto.
      }
      intros [|[|]]; auto.
    - replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
      apply up_ren_n_preserves_bijection. apply swap01_is_bijective.
    - intros; exfalso; lia.
  + simpl. econstructor. rewrite H.
    unfold up. rewrite <- (proj1 ren_up_up_ren_commute).
    - replace (up_ren (up_ren (up_ren_n j swap01))) with (up_ren_n (S (S j)) swap01) by auto.
      rewrite ((proj1 renamings_compose) _
        swap01
        (up_ren_n (S (S j)) swap01)
        (Basics.compose (up_ren_n (S (S j)) swap01) swap01)).
      {
        rewrite ((proj1 renamings_compose) _
        (up_ren_n (S (S j)) swap01)
        swap01
        (Basics.compose (up_ren_n (S (S j)) swap01) swap01)); auto.
      }
      intros [|[|]]; auto.
    - replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
      apply up_ren_n_preserves_bijection. apply swap01_is_bijective.
    - intros; exfalso; lia.
  + simpl.
    rewrite H.
    rewrite rename_axcut_ctx_over_fill_hole.
    - replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
      rewrite H1. econstructor; eauto.
      * replace 0 with (up_ren_n (S j) swap01 0) by auto.
        apply well_formedness_preserved_under_swap01; auto.
      * rewrite up_ren_n_additive.
        apply up_ren_swap_over_reduce_axcut; auto.
        inversion H2; subst.
        replace (length_axcut_ctx E) with (length_axcut_ctx E + 0) by lia.
        eapply nfv_well_typed_fill_hole; eauto.
    - replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
      apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
  + simpl.
    rewrite H.
    rewrite rename_axcut_ctx_over_fill_hole.
    - replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
      rewrite H1. eapply rp_ax_cut_r; eauto.
      * replace 0 with (up_ren_n (S j) swap01 0) by auto.
        apply well_formedness_preserved_under_swap01; auto.
      * rewrite up_ren_n_additive.
        apply up_ren_swap_over_reduce_axcut; auto.
        inversion H2; subst.
        replace (length_axcut_ctx E) with (length_axcut_ctx E + 0) by lia.
        eapply nfv_well_typed_fill_hole; eauto.
    - replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
      apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
  + simpl.
    rewrite (proj1 up_ren_swap_over_subst). simpl.
    rewrite ((proj1 subst_extensional) _ _
             ((prefix (rename_statement s (up_ren_n j swap01))) ⋅ id_subst)).
    - econstructor.
    - intros. destruct x; auto. simpl.
      unfold swap_subst.
      destruct (Nat.eqb (S x) (S j)) eqn:E1; simpl.
      * apply PeanoNat.Nat.eqb_eq in E1; inversion E1; subst.
        rewrite up_ren_n_swap_Sn. auto.
      * destruct (Nat.eqb x (S j)) eqn:E2; simpl.
        ** apply PeanoNat.Nat.eqb_eq in E2; subst.
            rewrite up_ren_n_swap_n; auto.
        ** apply PeanoNat.Nat.eqb_neq in E1, E2.
           assert (x <> j) by lia.
           rewrite up_ren_n_swap_not_nSn; auto.
  + simpl. apply rp_cong_cut_l.
    replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
    inversion H; subst.
    eapply IHequiv_reduces; eauto.
  + simpl. apply rp_cong_cut_r.
    replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
    inversion H; subst.
    eapply IHequiv_reduces; eauto.
  + simpl. apply rp_cong_seq.
    replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
    inversion H; subst.
    eapply IHequiv_reduces; eauto.
Qed.

(* ⊵ is invariant under lifting ***********************************************)
Definition lift_subst_at_n (σ : substitution) (n : nat) : substitution :=
  fun x => if (Nat.eqb x (S n)) then (future n) else
            if (Nat.ltb (S n) x) then (lift_message (σ (Nat.pred x)) n 1)
             else (lift_message (σ x) n 1).

Lemma up_subst_over_lift_subst :
  forall σ n x,
    up_subst (lift_subst_at_n σ n) x = lift_subst_at_n (up_subst σ) (S n) x.
Proof.
  intros.
  destruct x; auto; simpl.
  unfold lift_subst_at_n.
  destruct (Nat.eqb x (S n)) eqn:E1.
  + apply PeanoNat.Nat.eqb_eq in E1. assert (S x = S (S n)) by lia.
    apply PeanoNat.Nat.eqb_eq in H; rewrite H.
    simpl. reflexivity.
  + destruct (Nat.ltb (S n) x) eqn:E2.
    - apply PeanoNat.Nat.ltb_lt in E2.
      assert (S (S n) < (S x)) by lia. apply PeanoNat.Nat.ltb_lt in H; rewrite H.
      assert (S x <> S (S n)) by lia. apply PeanoNat.Nat.eqb_neq in H0; rewrite H0.
      apply PeanoNat.Nat.ltb_lt in H; apply PeanoNat.Nat.eqb_neq in H0.
      destruct x; try (exfalso; lia). simpl.
      unfold upM. rewrite (proj1 (proj2 lift_k_lift_Sj_lt_commute)); auto. lia.
    - apply PeanoNat.Nat.eqb_neq in E1. assert (S x <> S (S n)) by lia.
      apply PeanoNat.Nat.eqb_neq in H; rewrite H.
      apply PeanoNat.Nat.ltb_nlt in E2. assert (~ (S (S n)) < S x) by lia.
      apply PeanoNat.Nat.ltb_nlt in H0; rewrite H0; simpl.
      unfold upM. rewrite (proj1 (proj2 lift_k_lift_Sj_lt_commute)); auto. lia.
Qed.

Lemma up_subst_over_lift_subst2 :
  forall σ n x,
    up_subst (up_subst (lift_subst_at_n σ n)) x
      = lift_subst_at_n (up_subst (up_subst σ)) (S (S n)) x.
Proof.
  destruct x; auto; simpl. destruct x; auto; simpl.
  unfold lift_subst_at_n.
    destruct (Nat.eqb x (S n)) eqn:E1.
  + apply PeanoNat.Nat.eqb_eq in E1. assert (S (S x) = S (S (S n))) by lia.
    apply PeanoNat.Nat.eqb_eq in H; rewrite H.
    simpl. reflexivity.
  + destruct (Nat.ltb (S n) x) eqn:E2.
    - apply PeanoNat.Nat.ltb_lt in E2.
      assert (S (S (S n)) < (S (S x))) by lia. apply PeanoNat.Nat.ltb_lt in H; rewrite H.
      assert (S (S x) <> S (S (S n))) by lia. apply PeanoNat.Nat.eqb_neq in H0; rewrite H0.
      apply PeanoNat.Nat.ltb_lt in H; apply PeanoNat.Nat.eqb_neq in H0.
      destruct x; try (exfalso; lia). simpl.
      unfold upM. rewrite (proj1 (proj2 lift_k_lift_Sj_lt_commute)); auto; try lia.
      rewrite (proj1 (proj2 lift_k_lift_Sj_lt_commute)); auto; try lia.
    - apply PeanoNat.Nat.eqb_neq in E1. assert (S (S x) <> S (S (S n))) by lia.
      apply PeanoNat.Nat.eqb_neq in H; rewrite H.
      apply PeanoNat.Nat.ltb_nlt in E2. assert (~ (S (S (S n))) < S (S x)) by lia.
      apply PeanoNat.Nat.ltb_nlt in H0; rewrite H0; simpl.
      unfold upM. rewrite (proj1 (proj2 lift_k_lift_Sj_lt_commute)); auto; try lia.
      rewrite (proj1 (proj2 lift_k_lift_Sj_lt_commute)); auto; try lia.
Qed.

Lemma lift_over_subst :
  (
    forall P, forall σ j,
      lift_process (subst_process P σ) j 1 =
      subst_process (lift_process P (S j) 1) (lift_subst_at_n σ j)
  ) /\
  (
    forall M, forall σ j,
      lift_message (subst_message M σ) j 1 =
      subst_message (lift_message M (S j) 1) (lift_subst_at_n σ j)
  ) /\
  (
    forall s, forall σ j,
      lift_statement (subst_statement s σ) j 1 =
      subst_statement (lift_statement s (S j) 1) (lift_subst_at_n σ j)
  ).
Proof.
  apply syntax_ind; intros; simpl;
  try (now (try rewrite H; try rewrite H0; auto));
  try repeat rewrite ((proj1 subst_extensional) _
              (up_subst (lift_subst_at_n σ j))
              (lift_subst_at_n (up_subst σ) (S j))
              (up_subst_over_lift_subst _ _));
  try rewrite H; try rewrite H0; auto.
  + unfold lift_subst_at_n, relocate.
    destruct (Nat.leb (S j) n) eqn:E1; simpl.
    - destruct (Nat.eqb n j) eqn:E2.
      * exfalso.
        apply PeanoNat.Nat.leb_le in E1.
        apply PeanoNat.Nat.eqb_eq in E2.
        lia.
      * apply PeanoNat.Nat.leb_le in E1.
        apply PeanoNat.Nat.eqb_neq in E2.
        assert (S j < S n) by lia. apply PeanoNat.Nat.ltb_lt in H; rewrite H.
        reflexivity.
    - destruct (Nat.eqb n (S j)) eqn:E2.
      * exfalso.
        apply PeanoNat.Nat.leb_nle in E1.
        apply PeanoNat.Nat.eqb_eq in E2.
        lia.
      * apply PeanoNat.Nat.leb_nle in E1.
        apply PeanoNat.Nat.eqb_neq in E2.
        assert (~ (S j) < n) by lia. apply PeanoNat.Nat.ltb_nlt in H; rewrite H.
        reflexivity.
  + f_equal. apply subst_extensional. intro.
    rewrite up_subst_over_lift_subst2; auto.
Qed.

Lemma lift_ctx_at_k_rename_ctx_id_after_k_commute :
  forall E k r,
    bijective r -> (forall j, k <= j -> r j = j) ->
      lift_ctx (rename_axcut_ctx E r) k 1
        = rename_axcut_ctx (lift_ctx E k 1) r.
Proof.
  intro E. induction E; intros; simpl.
  + f_equal.
    unfold relocate.
    destruct (Nat.leb k n) eqn:E.
    - apply PeanoNat.Nat.leb_le in E. rewrite (H0 _ E).
      apply PeanoNat.Nat.leb_le in E. rewrite E. simpl.
      apply PeanoNat.Nat.leb_le in E.
      rewrite H0; lia.
    - apply PeanoNat.Nat.leb_nle in E.
      assert ( ~ k <= (r n) ).
      {
        intro Hle. destruct H.
        replace n with (g (r n)) in E by (rewrite c; auto).
        rewrite <- (H0 _ Hle) in E.
        rewrite c in E. congruence.
      }
      apply PeanoNat.Nat.leb_nle in H1; rewrite H1; auto.
  + f_equal.
    unfold relocate.
    destruct (Nat.leb k n) eqn:E.
    - apply PeanoNat.Nat.leb_le in E. rewrite (H0 _ E).
      apply PeanoNat.Nat.leb_le in E. rewrite E. simpl.
      apply PeanoNat.Nat.leb_le in E.
      rewrite H0; lia.
    - apply PeanoNat.Nat.leb_nle in E.
      assert ( ~ k <= (r n) ).
      {
        intro Hle. destruct H.
        replace n with (g (r n)) in E by (rewrite c; auto).
        rewrite <- (H0 _ Hle) in E.
        rewrite c in E. congruence.
      }
      apply PeanoNat.Nat.leb_nle in H1; rewrite H1; auto.
  + f_equal.
    - rewrite (proj1 lift_at_k_rename_id_after_k_commute); auto.
      apply shift_preserves_bijection; auto.
      intros. destruct j; auto. assert (k <= j) by lia.
      simpl. rewrite (H0 _ H2). reflexivity.
    - rewrite IHE; auto.
      apply shift_preserves_bijection; auto.
      intros. destruct j; auto. assert (k <= j) by lia.
      simpl. rewrite (H0 _ H2). reflexivity.
  + f_equal.
    - rewrite IHE; auto.
      apply shift_preserves_bijection; auto.
      intros. destruct j; auto. assert (k <= j) by lia.
      simpl. rewrite (H0 _ H2). reflexivity.
    - rewrite (proj1 lift_at_k_rename_id_after_k_commute); auto.
      apply shift_preserves_bijection; auto.
      intros. destruct j; auto. assert (k <= j) by lia.
      simpl. rewrite (H0 _ H2). reflexivity.
Qed.

Lemma lift_after_down_lt_commute_nfv :
  (forall P,
    forall k1 k2, k2 <= k1 ->
      ~ (k2 ∈ P) ->
      lift_process (down1_process P k2) k1 1
        = down1_process (lift_process P (S k1) 1) k2) /\
  (forall M,
    forall k1 k2, k2 <= k1 ->
      ~ (occurs_free_message k2 M) ->
      lift_message (down1_message M k2) k1 1
        = down1_message (lift_message M (S k1) 1) k2) /\
  (forall s,
    forall k1 k2, k2 <= k1 ->
      ~ (occurs_free_statement k2 s) ->
      lift_statement (down1_statement s k2) k1 1
        = down1_statement (lift_statement s (S k1) 1) k2).
Proof.
  apply syntax_ind; intros; simpl; auto.
    try (now (rewrite (H (S k1) (S k2)); try lia; try free_var_econstructor; eauto));
    try (now (rewrite (H (S k1) (S k2)); try lia; rewrite (H0 (S k1) (S k2)); try lia; auto)).
  + rewrite H; auto; try rewrite H0; auto; intro Hfv; apply H2; free_var_econstructor; eauto.
  + rewrite (H (S k1) (S k2)); try lia; try rewrite (H0 (S k1) (S k2)); try lia; auto;
    intro Hfv; apply H2; free_var_econstructor; eauto.
  + rewrite (H (S k1) (S k2)); auto; try rewrite (H0 k1 k2); try lia; auto;
    intro Hfv; apply H2; free_var_econstructor; eauto.
  + unfold relocate.
    destruct (Nat.leb (S k1) n) eqn:E.
    - simpl. apply PeanoNat.Nat.leb_le in E.
      assert (k2 < n) by lia. apply PeanoNat.Nat.ltb_lt in H1.
      assert (k2 < S n) by lia. apply PeanoNat.Nat.ltb_lt in H2.
      rewrite H1, H2. destruct n; try (exfalso; lia). simpl.
      unfold relocate. assert (k1 <= n) by lia.
      apply PeanoNat.Nat.leb_le in H3. rewrite H3; reflexivity.
    - apply PeanoNat.Nat.leb_nle in E.
      assert (n <= k1) by lia.
      destruct (Nat.ltb k2 n) eqn:E1.
      * simpl. unfold relocate. destruct (PeanoNat.Nat.eq_dec k2 n). { subst; exfalso; apply H0; econstructor. }
        assert (~ (k1 <= (Nat.pred n))) by lia.
        apply PeanoNat.Nat.leb_nle in H2. rewrite H2. reflexivity.
      * simpl. unfold relocate.
        apply PeanoNat.Nat.ltb_nlt in E1.
        destruct (PeanoNat.Nat.eq_dec n k1).
        ++ destruct (PeanoNat.Nat.eq_dec k2 n). { subst; exfalso; apply H0; econstructor. }
           exfalso. lia.
        ++ assert (~ (k1 <= n)) by lia. apply PeanoNat.Nat.leb_nle in H2. rewrite H2. reflexivity.
  + rewrite H; auto; try lia; intro Hfv; apply H1; free_var_econstructor; eauto.
  + rewrite H; auto; try lia; intro Hfv; apply H1; free_var_econstructor; eauto.
  + rewrite H; auto; try lia; intro Hfv; apply H1; free_var_econstructor; eauto.
  + rewrite (H (S k1) (S k2)); try lia; try rewrite (H0 (S k1) (S k2)); try lia; auto;
    intro Hfv; apply H2; free_var_econstructor; eauto.
  + rewrite (H (S k1) (S k2)); try lia; try rewrite (H0 (S k1) (S k2)); try lia; auto;
    intro Hfv; apply H2; free_var_econstructor; eauto.
  + rewrite (H (S (S k1)) (S (S k2))); try lia; try rewrite (H0 (S k1) (S k2)); try lia; auto;
    intro Hfv; apply H1; free_var_econstructor; eauto.
  + rewrite H; auto; try lia; intro Hfv; apply H1; free_var_econstructor; eauto.
Qed.

Lemma lift_over_reduce_axcut' :
  forall n E M P j,
    n = length_axcut_ctx E ->
    well_formed_axcut_ctx 0 E ->
    ~ (occurs_free_message (length_axcut_ctx E) M) ->
    lift_process (reduce_axcut E M P) j 1 =
    reduce_axcut
      (lift_ctx E (S j) 1)
      (lift_message M (length_axcut_ctx E + S j) 1)
      (lift_process P (S j) 1).
Proof.
  intro n.
  induction n; intros;
  destruct E; simpl in H; try congruence; simpl.
  + rewrite reduce_axcut_equation_1.
    unfold relocate. destruct (Nat.leb (S j) n) eqn:E; simpl.
    - rewrite reduce_axcut_equation_1.
      rewrite (proj1 lift_over_subst). erewrite (proj1 subst_extensional); eauto.
      apply PeanoNat.Nat.leb_le in E.
      intros.
      unfold lift_subst_at_n. destruct (Nat.eqb x (S j)) eqn:E1.
      * apply PeanoNat.Nat.eqb_eq in E1; subst; auto.
      * apply PeanoNat.Nat.eqb_neq in E1.
        destruct (Nat.ltb (S j) x) eqn:E2.
        ** apply PeanoNat.Nat.ltb_lt in E2. destruct x; try (exfalso; lia).
           simpl. destruct x; try (exfalso; lia). simpl.
           unfold relocate. assert (j <= x) by lia. apply PeanoNat.Nat.leb_le in H2.
           rewrite H2; auto.
        ** apply PeanoNat.Nat.ltb_nlt in E2. destruct x; simpl.
          *** unfold downM.
              rewrite (proj1 (proj2 lift_after_down_lt_commute_nfv)); auto.
              lia.
          *** unfold relocate. assert (~ (j <= x)) by lia. apply PeanoNat.Nat.leb_nle in H2.
              rewrite H2. auto.
    - rewrite reduce_axcut_equation_1.
      rewrite (proj1 lift_over_subst). erewrite (proj1 subst_extensional); eauto.
      apply PeanoNat.Nat.leb_nle in E.
      intros.
      unfold lift_subst_at_n. destruct (Nat.eqb x (S j)) eqn:E1.
      * apply PeanoNat.Nat.eqb_eq in E1; subst; auto.
      * apply PeanoNat.Nat.eqb_neq in E1.
        destruct (Nat.ltb (S j) x) eqn:E2.
        ** apply PeanoNat.Nat.ltb_lt in E2. destruct x; try (exfalso; lia).
           simpl. destruct x; try (exfalso; lia). simpl.
           unfold relocate. assert (j <= x) by lia. apply PeanoNat.Nat.leb_le in H2.
           rewrite H2; auto.
        ** apply PeanoNat.Nat.ltb_nlt in E2. destruct x; simpl.
          *** unfold downM.
              rewrite (proj1 (proj2 lift_after_down_lt_commute_nfv)); auto.
              lia.
          *** unfold relocate. assert (~ (j <= x)) by lia. apply PeanoNat.Nat.leb_nle in H2.
              rewrite H2. auto.
  + rewrite reduce_axcut_equation_2.
    unfold relocate. destruct (Nat.leb (S j) n) eqn:E; simpl.
    - rewrite reduce_axcut_equation_2.
      rewrite (proj1 lift_over_subst). erewrite (proj1 subst_extensional); eauto.
      apply PeanoNat.Nat.leb_le in E.
      intros.
      unfold lift_subst_at_n. destruct (Nat.eqb x (S j)) eqn:E1.
      * apply PeanoNat.Nat.eqb_eq in E1; subst; auto.
      * apply PeanoNat.Nat.eqb_neq in E1.
        destruct (Nat.ltb (S j) x) eqn:E2.
        ** apply PeanoNat.Nat.ltb_lt in E2. destruct x; try (exfalso; lia).
           simpl. destruct x; try (exfalso; lia). simpl.
           unfold relocate. assert (j <= x) by lia. apply PeanoNat.Nat.leb_le in H2.
           rewrite H2; auto.
        ** apply PeanoNat.Nat.ltb_nlt in E2. destruct x; simpl.
          *** unfold downM.
              rewrite (proj1 (proj2 lift_after_down_lt_commute_nfv)); auto.
              lia.
          *** unfold relocate. assert (~ (j <= x)) by lia. apply PeanoNat.Nat.leb_nle in H2.
              rewrite H2. auto.
    - rewrite reduce_axcut_equation_2.
      rewrite (proj1 lift_over_subst). erewrite (proj1 subst_extensional); eauto.
      apply PeanoNat.Nat.leb_nle in E.
      intros.
      unfold lift_subst_at_n. destruct (Nat.eqb x (S j)) eqn:E1.
      * apply PeanoNat.Nat.eqb_eq in E1; subst; auto.
      * apply PeanoNat.Nat.eqb_neq in E1.
        destruct (Nat.ltb (S j) x) eqn:E2.
        ** apply PeanoNat.Nat.ltb_lt in E2. destruct x; try (exfalso; lia).
           simpl. destruct x; try (exfalso; lia). simpl.
           unfold relocate. assert (j <= x) by lia. apply PeanoNat.Nat.leb_le in H2.
           rewrite H2; auto.
        ** apply PeanoNat.Nat.ltb_nlt in E2. destruct x; simpl.
          *** unfold downM.
              rewrite (proj1 (proj2 lift_after_down_lt_commute_nfv)); auto.
              lia.
          *** unfold relocate. assert (~ (j <= x)) by lia. apply PeanoNat.Nat.leb_nle in H2.
              rewrite H2. auto.
  + rewrite reduce_axcut_equation_3; simpl.
    rewrite reduce_axcut_equation_3; simpl.
    f_equal.
    - unfold down. rewrite (proj1 lift_after_down_lt_commute); try lia.
      f_equal. rewrite (proj1 lift_at_k_rename_id_after_k_commute); auto.
      apply swap01_is_bijective. intros [|[|]] ?; try (exfalso; lia); auto.
    - inversion H; subst.
      assert (
        length_axcut_ctx E = length_axcut_ctx (rename_axcut_ctx E swap01)
      ). { rewrite rename_axcut_ctx_preserves_length with (r := swap01); auto. }
      assert (
        well_formed_axcut_ctx 0 (rename_axcut_ctx E swap01)
      ).
      {
        inversion H0; subst.
        replace 0 with (swap01 1) by auto.
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; auto.
      }
      assert (
        ~ (occurs_free_message (length_axcut_ctx E)
           (rename_message M (up_ren_n (length_axcut_ctx E) swap01)))
      ).
      {
        replace (length_axcut_ctx E) with
                ((up_ren_n (length_axcut_ctx E) swap01) (S (length_axcut_ctx E)))
          at 1
          by apply up_ren_n_swap_Sn.
        apply (proj1 (proj2 nfv_under_renaming)); auto.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
      }
      rewrite H2.
      rewrite H2 in H4.
      rewrite (IHn _ _ _  _  H2 H3 H4). f_equal.
      * rewrite lift_ctx_at_k_rename_ctx_id_after_k_commute; auto.
        apply swap01_is_bijective. intros [|[|]] ?; try (exfalso; lia); auto.
      * rewrite <- rename_axcut_ctx_preserves_length with (r := swap01).
        rewrite lift_ctx_preserves_length.
        replace (S (length_axcut_ctx E + S j))
           with (length_axcut_ctx E + S (S j))
             by lia.
        rewrite (proj1 (proj2 lift_at_k_rename_id_after_k_commute)); auto.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        intros. apply up_ren_n_swap_not_nSn; lia.
      * unfold up.
        rewrite (proj1 lift_at_k_rename_id_after_k_commute).
        ** f_equal. rewrite (proj1 lift_k_lift_Sj_lt_commute); auto. lia.
        ** apply swap01_is_bijective.
        ** intros [|[|]] ?; try (exfalso; lia); auto.
  + rewrite reduce_axcut_equation_4; simpl.
    rewrite reduce_axcut_equation_4; simpl.
    f_equal.
    - inversion H; subst.
      assert (
        length_axcut_ctx E = length_axcut_ctx (rename_axcut_ctx E swap01)
      ). { rewrite rename_axcut_ctx_preserves_length with (r := swap01); auto. }
      assert (
        well_formed_axcut_ctx 0 (rename_axcut_ctx E swap01)
      ).
      {
        inversion H0; subst.
        replace 0 with (swap01 1) by auto.
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; auto.
      }
      assert (
        ~ (occurs_free_message (length_axcut_ctx E)
           (rename_message M (up_ren_n (length_axcut_ctx E) swap01)))
      ).
      {
        replace (length_axcut_ctx E) with
                ((up_ren_n (length_axcut_ctx E) swap01) (S (length_axcut_ctx E)))
          at 1
          by apply up_ren_n_swap_Sn.
        apply (proj1 (proj2 nfv_under_renaming)); auto.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
      }
      rewrite H2.
      rewrite H2 in H4.
      rewrite (IHn _ _ _  _  H2 H3 H4). f_equal.
      * rewrite lift_ctx_at_k_rename_ctx_id_after_k_commute; auto.
        apply swap01_is_bijective. intros [|[|]] ?; try (exfalso; lia); auto.
      * rewrite <- rename_axcut_ctx_preserves_length with (r := swap01).
        rewrite lift_ctx_preserves_length.
        replace (S (length_axcut_ctx E + S j))
           with (length_axcut_ctx E + S (S j))
             by lia.
        rewrite (proj1 (proj2 lift_at_k_rename_id_after_k_commute)); auto.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        intros. apply up_ren_n_swap_not_nSn; lia.
      * unfold up.
        rewrite (proj1 lift_at_k_rename_id_after_k_commute).
        ** f_equal. rewrite (proj1 lift_k_lift_Sj_lt_commute); auto. lia.
        ** apply swap01_is_bijective.
        ** intros [|[|]] ?; try (exfalso; lia); auto.
    - unfold down. rewrite (proj1 lift_after_down_lt_commute); try lia.
      f_equal. rewrite (proj1 lift_at_k_rename_id_after_k_commute); auto.
      apply swap01_is_bijective. intros [|[|]] ?; try (exfalso; lia); auto.
Qed.

Lemma lift_over_reduce_axcut :
  forall E M P j,
    well_formed_axcut_ctx 0 E ->
    ~ (occurs_free_message (length_axcut_ctx E) M) ->
    lift_process (reduce_axcut E M P) j 1 =
    reduce_axcut
      (lift_ctx E (S j) 1)
      (lift_message M (length_axcut_ctx E + S j) 1)
      (lift_process P (S j) 1).
Proof.
  intros. eapply lift_over_reduce_axcut'; eauto.
Qed.

Lemma equiv_red_invariant_under_up :
  forall Γ P P', Γ ⊢ P :# -> P ⊵ P' ->
    forall j, lift_process P j 1 ⊵ lift_process P' j 1.
Proof.
  intros.
  generalize dependent Γ.
  generalize dependent j.
  induction H0; intros; simpl; try (now econstructor).
  + econstructor. subst.
    unfold up. rewrite (proj1 lift_at_k_rename_id_after_k_commute).
    - rewrite (proj1 lift_k_lift_Sj_lt_commute); auto. lia.
    - apply swap01_is_bijective.
    - intros [|[|]] ?; auto; try (exfalso; lia).
  + econstructor. subst.
    unfold up. rewrite (proj1 lift_at_k_rename_id_after_k_commute).
    - rewrite (proj1 lift_k_lift_Sj_lt_commute); auto. lia.
    - apply swap01_is_bijective.
    - intros [|[|]] ?; auto; try (exfalso; lia).
  + rewrite H, H1.
    rewrite up_ctx_over_fill_hole.
    assert (
      lift_process (reduce_axcut E M P) j 1 =
      reduce_axcut
        (lift_ctx E (S j) 1)
        (lift_message M (length_axcut_ctx E + S j) 1)
        (lift_process P (S j) 1)
    ).
    {
      apply lift_over_reduce_axcut; auto.
      inversion H2; subst.
      replace (length_axcut_ctx E) with (length_axcut_ctx E + 0) by lia.
      eapply nfv_well_typed_fill_hole; eauto.
    }
    rewrite H3. econstructor; eauto.
    apply upE_preserves_well_formedness2; auto. lia.
  + rewrite H, H1.
    rewrite up_ctx_over_fill_hole.
    assert (
      lift_process (reduce_axcut E M P) j 1 =
      reduce_axcut
        (lift_ctx E (S j) 1)
        (lift_message M (length_axcut_ctx E + S j) 1)
        (lift_process P (S j) 1)
    ).
    {
      apply lift_over_reduce_axcut; auto.
      inversion H2; subst.
      replace (length_axcut_ctx E) with (length_axcut_ctx E + 0) by lia.
      eapply nfv_well_typed_fill_hole; eauto.
    }
    rewrite H3. eapply rp_ax_cut_r; eauto.
    apply upE_preserves_well_formedness2; auto. lia.
  + rewrite (proj1 lift_over_subst).
    erewrite (proj1 subst_extensional).
    - econstructor.
    - intros [|]; auto; simpl.
      unfold lift_subst_at_n.
      destruct (Nat.eqb (S n) (S j)) eqn:E1.
      * apply PeanoNat.Nat.eqb_eq in E1; inversion E1; auto.
      * destruct (PeanoNat.Nat.ltb (S j) (S n)) eqn:E2.
        ** simpl. apply PeanoNat.Nat.ltb_lt in E2. destruct n; try (exfalso; lia).
           simpl. unfold relocate. assert (j <= n) by lia. apply PeanoNat.Nat.leb_le in H0.
           rewrite H0. auto.
        ** simpl. unfold relocate.
           apply PeanoNat.Nat.ltb_nlt in E2. apply PeanoNat.Nat.eqb_neq in E1.
           assert (~ (j <= n)) by lia. apply PeanoNat.Nat.leb_nle in H0.
           rewrite H0. auto.
  + apply rp_cong_cut_l. inversion H; subst.
    eapply IHequiv_reduces; eauto.
  + apply rp_cong_cut_r. inversion H; subst.
    eapply IHequiv_reduces; eauto.
  + apply rp_cong_seq. inversion H; subst.
    eapply IHequiv_reduces; eauto.
Qed.
