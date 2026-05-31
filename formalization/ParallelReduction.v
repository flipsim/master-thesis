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
Lemma equiv_red_preserves_typing :
  forall Γ P Q, Γ ⊢ P :# -> P ⊵ Q -> Γ ⊢ Q :#.
Proof.
  intros.
  apply equiv_reduces_in_reduces_or_struct_cong in H0.
  destruct H0.
  + eapply preservation; eauto.
  + eapply struct_cong_preserves_typing; eauto. apply c_comm; auto.
Qed.

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

Lemma up_subst_into_swap_subst :
  forall n k σ x,
    up_subst (swap_subst σ n k) x =
      swap_subst (up_subst σ) (S n) (S k) x.
Proof.
  intros. destruct x; auto; simpl.
  unfold swap_subst.
  destruct (PeanoNat.Nat.eq_dec x n); subst.
  + repeat rewrite PeanoNat.Nat.eqb_refl. reflexivity.
  + assert (S x <> S n) by lia. apply PeanoNat.Nat.eqb_neq in n0, H.
    rewrite n0, H.
    destruct (PeanoNat.Nat.eq_dec x k); subst.
    - repeat rewrite PeanoNat.Nat.eqb_refl. reflexivity.
    - assert (S x <> S k) by lia. apply PeanoNat.Nat.eqb_neq in H0, n1.
      rewrite n1, H0. reflexivity.
Qed.

Lemma up_subst_into_swap_subst2 :
  forall n k σ x,
    up_subst (up_subst (swap_subst σ n k)) x =
      swap_subst (up_subst (up_subst σ)) (S (S n)) (S (S k)) x.
Proof.
  intros. destruct x as [|[|]]; auto; simpl.
  unfold swap_subst.
  destruct (PeanoNat.Nat.eq_dec n0 n); subst.
  + repeat rewrite PeanoNat.Nat.eqb_refl. reflexivity.
  + assert (n0 <> n) by lia.
    assert (S (S n0) <> (S (S n))) by lia.
    apply PeanoNat.Nat.eqb_neq in n1, H0.
    rewrite n1, H0.
    destruct (PeanoNat.Nat.eq_dec n0 k); subst.
    - repeat rewrite PeanoNat.Nat.eqb_refl. reflexivity.
    - assert (S (S n0) <> S (S k)) by lia.
      apply PeanoNat.Nat.eqb_neq in H1, n2.
      rewrite n2, H1. reflexivity.
Qed.

Lemma up_ren_swap_subst_cancel :
  (forall P n σ,
    subst_process (rename_process P (up_ren_n n swap01)) (swap_subst σ n (S n))
      = subst_process P σ) /\
  (forall M n σ,
    subst_message (rename_message M (up_ren_n n swap01)) (swap_subst σ n (S n))
      = subst_message M σ) /\
  (forall s n σ,
    subst_statement (rename_statement s (up_ren_n n swap01)) (swap_subst σ n (S n))
      = subst_statement s σ).
Proof.
  apply syntax_ind; intros; simpl;
  replace (up_ren (up_ren_n n swap01)) with (up_ren_n (S n) swap01) by auto;
  replace (up_ren (up_ren_n (S n) swap01)) with (up_ren_n (S (S n)) swap01) by auto;
  repeat rewrite ((proj1 subst_extensional) _ _ _ (up_subst_into_swap_subst n (S n) σ));
  try rewrite H; try rewrite H0; auto.
  + destruct (PeanoNat.Nat.eq_dec n0 n); subst.
    - rewrite up_ren_n_swap_n. unfold swap_subst.
      assert (S n <> n) by lia. apply PeanoNat.Nat.eqb_neq in H. rewrite H.
      rewrite PeanoNat.Nat.eqb_refl. reflexivity.
    - destruct (PeanoNat.Nat.eq_dec (S n0) n); subst.
      * rewrite up_ren_n_swap_Sn. unfold swap_subst. rewrite PeanoNat.Nat.eqb_refl.
        reflexivity.
      * rewrite up_ren_n_swap_not_nSn; try lia. unfold swap_subst.
        apply not_eq_sym in n1, n2. apply PeanoNat.Nat.eqb_neq in n1, n2.
        rewrite n1, n2. reflexivity.
  + rewrite ((proj1 subst_extensional) _ _ _ (up_subst_into_swap_subst2 n (S n) σ)).
    rewrite H; auto.
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

Lemma down_ctx_at_k_rename_ctx_id_after_k_commute :
  forall E k r,
    bijective r -> (forall j, k <= j -> r j = j) ->
      down1_ctx (rename_axcut_ctx E r) k
        = rename_axcut_ctx (down1_ctx E k) r.
Proof.
  intro E. induction E; intros; simpl.
  + destruct (Nat.ltb k n) eqn:E; simpl.
    - apply PeanoNat.Nat.ltb_lt in E.
      assert (Nat.ltb k n = true) by (apply PeanoNat.Nat.ltb_lt in E; auto).
      destruct n; try (exfalso; lia). simpl.
      assert (k <= (S n)) by lia. rewrite (H0 (S n)); auto. simpl.
      rewrite H1. rewrite H0; auto. lia.
    - destruct (Nat.ltb k (r n)) eqn:E1; auto.
      apply PeanoNat.Nat.leb_nle in E. assert (n <= k) by lia.
      apply PeanoNat.Nat.leb_le in E1.
      destruct (Compare_dec.le_gt_dec k n).
      ++ exfalso.
         rewrite (H0 n) in E1; auto.
      ++ exfalso.
         destruct H.
         assert (r n = n).
         {
          assert (k <= r n) by lia.
          specialize H0 with (r n). apply H0 in H.
          assert (g0 (r (r n)) = g0 (r n)) by (rewrite H; auto).
          repeat rewrite c in H2. auto.
         }
         rewrite H in E1. congruence.
  + destruct (Nat.ltb k n) eqn:E; simpl.
    - apply PeanoNat.Nat.ltb_lt in E.
      assert (Nat.ltb k n = true) by (apply PeanoNat.Nat.ltb_lt in E; auto).
      destruct n; try (exfalso; lia). simpl.
      assert (k <= (S n)) by lia. rewrite (H0 (S n)); auto. simpl.
      rewrite H1. rewrite H0; auto. lia.
    - destruct (Nat.ltb k (r n)) eqn:E1; auto.
      apply PeanoNat.Nat.leb_nle in E. assert (n <= k) by lia.
      apply PeanoNat.Nat.leb_le in E1.
      destruct (Compare_dec.le_gt_dec k n).
      ++ exfalso.
         rewrite (H0 n) in E1; auto.
      ++ exfalso.
         destruct H.
         assert (r n = n).
         {
          assert (k <= r n) by lia.
          specialize H0 with (r n). apply H0 in H.
          assert (g0 (r (r n)) = g0 (r n)) by (rewrite H; auto).
          repeat rewrite c in H2. auto.
         }
         rewrite H in E1. congruence.
  + f_equal.
    - rewrite (proj1 down_at_k_rename_id_after_k_commute); auto.
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
    - rewrite (proj1 down_at_k_rename_id_after_k_commute); auto.
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

(* ⊵ is invariant under downshifting ******************************************)
Definition down_subst_at_n (σ : substitution) (n : nat) : substitution :=
  fun x => if Nat.ltb x n then σ x else σ (S x).

Lemma down_after_down_gt_commute_nfv :
  (forall P,
    forall k1 k2, k1 < (S k2) ->
      ~ k2 ∈ P ->
      down1_process (lift_process P k1 1) (S k2)
        = lift_process (down1_process P k2) k1 1) /\
  (forall M,
    forall k1 k2, k1 < (S k2) ->
      ~ (occurs_free_message k2 M) ->
      down1_message (lift_message M k1 1) (S k2)
        = lift_message (down1_message M k2) k1 1) /\
  (forall s,
    forall k1 k2, k1 < (S k2) ->
      ~ (occurs_free_statement k2 s) ->
      down1_statement (lift_statement s k1 1) (S k2)
        = lift_statement (down1_statement s k2) k1 1).
Proof.
  apply syntax_ind; intros; simpl; auto;
    try (now (rewrite H; try rewrite H0; auto; try lia; intro; try apply H2; try apply H1; free_var_econstructor; eauto));
    try (now (rewrite (H (S k1) (S k2)); try lia; auto));
    try (now (rewrite (H (S k1) (S k2)); try lia; rewrite (H0 (S k1) (S k2)); try lia; auto;
              intro; apply H2; free_var_econstructor; eauto)).
  + unfold relocate.
    assert (k2 <> n). { destruct (PeanoNat.Nat.eq_dec k2 n); auto; subst. exfalso; apply H0; econstructor. }
    destruct (Nat.leb k1 n) eqn:E1; simpl.
    - apply PeanoNat.Nat.leb_le in E1.
      destruct (Nat.ltb k2 n) eqn:E2.
      * apply PeanoNat.Nat.ltb_lt in E2.
        assert (S k2 < S n) by lia. apply PeanoNat.Nat.ltb_lt in H2. rewrite H2.
        destruct n; try (exfalso; lia). simpl. unfold relocate.
        assert (k1 <= n) by lia. apply PeanoNat.Nat.leb_le in H3; rewrite H3; auto.
      * apply PeanoNat.Nat.ltb_nlt in E2.
        assert (~ (S k2) < (S n)) by lia. apply PeanoNat.Nat.ltb_nlt in H2; rewrite H2.
        simpl. unfold relocate. assert (k1 <= n) by lia.
        apply PeanoNat.Nat.leb_le in H3; rewrite H3; auto.
    - apply PeanoNat.Nat.leb_nle in E1.
      destruct (Nat.ltb (S k2) n) eqn:E2.
      * apply PeanoNat.Nat.ltb_lt in E2.
        assert (k2 < n) by lia. apply PeanoNat.Nat.ltb_lt in H2. rewrite H2.
        simpl. unfold relocate.
        assert (~ (k1 <= (Nat.pred n))) by lia.
        apply PeanoNat.Nat.leb_nle in H3; rewrite H3. auto.
      * apply PeanoNat.Nat.ltb_nlt in E2.
        assert (~ k2 < n) by lia. apply PeanoNat.Nat.ltb_nlt in H2; rewrite H2.
        simpl. unfold relocate. assert (~ k1 <= n) by lia.
        apply PeanoNat.Nat.leb_nle in H3; rewrite H3; auto.
  + f_equal. rewrite H; auto. intro. apply H1. econstructor. auto.
  + f_equal. rewrite H; auto. intro; apply H1; econstructor; auto.
Qed.

Lemma subst_extensional_only_free_vars :
  (forall P, forall σ1 σ2, (forall x, x ∈ P -> σ1 x = σ2 x) ->
    subst_process P σ1 = subst_process P σ2) /\
  (forall M, forall σ1 σ2, (forall x, occurs_free_message x M -> σ1 x = σ2 x) ->
    subst_message M σ1 = subst_message M σ2) /\
  (forall s, forall σ1 σ2, (forall x, occurs_free_statement x s -> σ1 x = σ2 x) ->
    subst_statement s σ1 = subst_statement s σ2).
Proof.
  apply syntax_ind; intros; simpl; auto.
  + rewrite (H _ σ2); try rewrite (H0 _ σ2); auto; intros; apply H1; free_var_econstructor; eauto.
  + rewrite (H _ (up_subst σ2)); try rewrite (H0 _ (up_subst σ2)); auto; intros;
    destruct x; auto; simpl; rewrite H1; auto; free_var_econstructor; eauto.
  + rewrite (H _ (up_subst σ2)); try rewrite (H0 _ σ2); auto; intros.
    - rewrite H1; auto; free_var_econstructor; eauto.
    - destruct x; auto; simpl; rewrite H1; auto; free_var_econstructor; eauto.
  + rewrite H; auto. econstructor.
  + rewrite (H _ σ2); auto. intros; rewrite H0; auto; free_var_econstructor; eauto.
  + rewrite (H _ (up_subst σ2)); auto; intros. destruct x; auto; simpl; rewrite H0; auto; free_var_econstructor; eauto.
  + rewrite (H _ (up_subst σ2)); auto; intros. destruct x; auto; simpl; rewrite H0; auto; free_var_econstructor; eauto.
  + rewrite (H _ (up_subst σ2)); try rewrite (H0 _ (up_subst σ2)); auto; intros;
    destruct x; auto; simpl; rewrite H1; auto; free_var_econstructor; eauto.
  + rewrite (H _ (up_subst σ2)); try rewrite (H0 _ (up_subst σ2)); auto; intros;
    destruct x; auto; simpl; rewrite H1; auto; free_var_econstructor; eauto.
  + rewrite (H _ (up_subst (up_subst σ2))); auto; intros.
    destruct x as [|[|]]; auto; simpl; rewrite H0; auto; free_var_econstructor; eauto.
  + rewrite (H _ σ2); auto; intros; rewrite H0; auto; free_var_econstructor; eauto.
Qed.

Lemma down_over_subst :
    (
    forall P, forall σ j,
      ~ (S j) ∈ P ->
      (forall n, n ∈ P -> ~ (occurs_free_message j (σ n))) ->
      down1_process (subst_process P σ) j =
      subst_process (down1_process P (S j))
                    (fun x => down1_message (down_subst_at_n σ (S j) x) j)
  ) /\
  (
    forall M, forall σ j,
      ~ (occurs_free_message (S j) M) ->
      (forall n, (occurs_free_message n M) -> ~ (occurs_free_message j (σ n))) ->
      down1_message (subst_message M σ) j =
      subst_message (down1_message M (S j))
                    (fun x => down1_message (down_subst_at_n σ (S j) x) j)
  ) /\
  (
    forall s, forall σ j,
      ~ (occurs_free_statement (S j) s) ->
      (forall n, (occurs_free_statement n s) -> ~ (occurs_free_message j (σ n))) ->
      down1_statement (subst_statement s σ) j =
      subst_statement (down1_statement s (S j))
                    (fun x => down1_message (down_subst_at_n σ (S j) x) j)
  ).
Proof.
  apply syntax_ind; intros; simpl.
  + rewrite H. rewrite H0. auto.
    all: try (intros; apply H2; free_var_econstructor; eauto).
    all: intro Hfv; apply H1; free_var_econstructor; eauto.
  + rewrite H; try rewrite H0;
    try (intro Hfv; apply H1; free_var_econstructor; eauto).
    - f_equal.
      {
        apply subst_extensional_only_free_vars.
        intros.
        destruct x as [|]; auto; simpl.
        unfold down_subst_at_n.
        destruct (Nat.ltb (S x) (S (S j))) eqn:E.
        - apply PeanoNat.Nat.ltb_lt in E. assert (x < S j) by lia.
          apply PeanoNat.Nat.ltb_lt in H4; rewrite H4. simpl.
          unfold upM.
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto; try lia.
          apply H2. apply fv_cut_l.
          destruct ((proj1 free_vars_decidable) p (S x)); auto.
          apply ((proj1 nfv_down_lt) _ _ _ E) in H5. congruence.
        - apply PeanoNat.Nat.ltb_nlt in E. assert (~ x < S j) by lia.
          apply PeanoNat.Nat.ltb_nlt in H4; rewrite H4; simpl.
          unfold upM.
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto. lia.
          apply H2. apply fv_cut_l.
          destruct ((proj1 free_vars_decidable) p (S (S x))); auto.
          assert (S (S x) > (S (S j))) by lia.
          eapply (proj1 n_fv_down_Sn') with (k := (S (S j))); eauto. lia.
          intro Hfv. apply H1; free_var_econstructor; eauto.
      }
      {
        apply subst_extensional_only_free_vars.
        intros.
        destruct x as [|]; auto; simpl.
        unfold down_subst_at_n.
        destruct (Nat.ltb (S x) (S (S j))) eqn:E.
        - apply PeanoNat.Nat.ltb_lt in E. assert (x < S j) by lia.
          apply PeanoNat.Nat.ltb_lt in H4; rewrite H4. simpl.
          unfold upM.
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto; try lia.
          apply H2. apply fv_cut_r.
          destruct ((proj1 free_vars_decidable) p0 (S x)); auto.
          apply ((proj1 nfv_down_lt) _ _ _ E) in H5. congruence.
        - apply PeanoNat.Nat.ltb_nlt in E. assert (~ x < S j) by lia.
          apply PeanoNat.Nat.ltb_nlt in H4; rewrite H4; simpl.
          unfold upM.
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto. lia.
          apply H2. apply fv_cut_r.
          destruct ((proj1 free_vars_decidable) p0 (S (S x))); auto.
          assert (S (S x) > (S (S j))) by lia.
          eapply (proj1 n_fv_down_Sn') with (k := (S (S j))); eauto. lia.
          intro Hfv. apply H1; free_var_econstructor; eauto.
      }
    - intros [|] ?; simpl.
      * intro. inversion H4.
      * intro. apply (H2 n).
        ** free_var_econstructor; eauto.
        ** unfold upM in H4. apply fv_up_Sn2' in H4; auto. lia.
    - intros [|] ?; simpl.
      * intro. inversion H4.
      * intro. apply (H2 n).
        ** free_var_econstructor; eauto.
        ** unfold upM in H4. apply fv_up_Sn2' in H4; auto. lia.
  + rewrite H. rewrite H0. auto.
    all: try (intros; apply H2; free_var_econstructor; eauto).
    all: try (intro Hfv; apply H1; free_var_econstructor; eauto).
    - f_equal.
      apply subst_extensional_only_free_vars.
        intros.
        destruct x as [|]; auto; simpl.
        unfold down_subst_at_n.
        destruct (Nat.ltb (S x) (S (S j))) eqn:E.
        * apply PeanoNat.Nat.ltb_lt in E. assert (x < S j) by lia.
          apply PeanoNat.Nat.ltb_lt in H4; rewrite H4. simpl.
          unfold upM.
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto; try lia.
          apply H2. apply fv_seq_l.
          destruct ((proj1 free_vars_decidable) p (S x)); auto.
          apply ((proj1 nfv_down_lt) _ _ _ E) in H5. congruence.
        * apply PeanoNat.Nat.ltb_nlt in E. assert (~ x < S j) by lia.
          apply PeanoNat.Nat.ltb_nlt in H4; rewrite H4; simpl.
          unfold upM.
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto. lia.
          apply H2. apply fv_seq_l.
          destruct ((proj1 free_vars_decidable) p (S (S x))); auto.
          assert (S (S x) > (S (S j))) by lia.
          eapply (proj1 n_fv_down_Sn') with (k := (S (S j))); eauto. lia.
          intro Hfv. apply H1; free_var_econstructor; eauto.
    - intros [|] ?; simpl.
      * intro. inversion H4.
      * intro. apply (H2 n).
        ** free_var_econstructor; eauto.
        ** unfold upM in H4. apply fv_up_Sn2' in H4; auto. lia.
  + auto.
  + destruct (Nat.ltb (S j) n) eqn:E; simpl.
    - apply PeanoNat.Nat.ltb_lt in E. destruct n; try (exfalso; lia); simpl.
      unfold down_subst_at_n.
      assert (~ (n < (S j))) by lia. apply PeanoNat.Nat.ltb_nlt in H1; rewrite H1.
      reflexivity.
    - apply PeanoNat.Nat.ltb_nlt in E.
      assert (S j <> n). { destruct (PeanoNat.Nat.eq_dec (S j) n); auto; subst. exfalso; apply H; econstructor. }
      unfold down_subst_at_n.
      assert (n < (S j)) by lia. apply PeanoNat.Nat.ltb_lt in H2; rewrite H2.
      reflexivity.
  + rewrite H. auto.
    intro; apply H0; free_var_econstructor; eauto.
    intros. apply H1; free_var_econstructor; eauto.
  + rewrite H;
    try (intro; apply H0; free_var_econstructor; eauto).
    - f_equal.
      apply subst_extensional_only_free_vars.
      intros.
      destruct x as [|]; auto; simpl.
      unfold down_subst_at_n.
      destruct (Nat.ltb (S x) (S (S j))) eqn:E.
      * apply PeanoNat.Nat.ltb_lt in E. assert (x < S j) by lia.
        apply PeanoNat.Nat.ltb_lt in H3; rewrite H3. simpl.
        unfold upM.
        rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto; try lia.
        apply H1. econstructor.
        destruct ((proj1 free_vars_decidable) p (S x)); auto.
        apply ((proj1 nfv_down_lt) _ _ _ E) in H4. congruence.
      * apply PeanoNat.Nat.ltb_nlt in E. assert (~ x < S j) by lia.
        apply PeanoNat.Nat.ltb_nlt in H3; rewrite H3; simpl.
        unfold upM.
        rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto. lia.
        apply H1. econstructor.
        destruct ((proj1 free_vars_decidable) p (S (S x))); auto.
        assert (S (S x) > (S (S j))) by lia.
        eapply (proj1 n_fv_down_Sn') with (k := (S (S j))); eauto. lia.
        intro Hfv. apply H0; free_var_econstructor; eauto.
    - intros [|] ?; simpl.
      * intro. inversion H3.
      * intro. apply (H1 n).
        ** free_var_econstructor; eauto.
        ** unfold upM in H3. apply fv_up_Sn2' in H3; auto. lia.
  + rewrite H;
    try (intro; apply H0; free_var_econstructor; eauto).
    - f_equal.
      apply subst_extensional_only_free_vars.
      intros.
      destruct x as [|]; auto; simpl.
      unfold down_subst_at_n.
      destruct (Nat.ltb (S x) (S (S j))) eqn:E.
      * apply PeanoNat.Nat.ltb_lt in E. assert (x < S j) by lia.
        apply PeanoNat.Nat.ltb_lt in H3; rewrite H3. simpl.
        unfold upM.
        rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto; try lia.
        apply H1. econstructor.
        destruct ((proj1 free_vars_decidable) p (S x)); auto.
        apply ((proj1 nfv_down_lt) _ _ _ E) in H4. congruence.
      * apply PeanoNat.Nat.ltb_nlt in E. assert (~ x < S j) by lia.
        apply PeanoNat.Nat.ltb_nlt in H3; rewrite H3; simpl.
        unfold upM.
        rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto. lia.
        apply H1. econstructor.
        destruct ((proj1 free_vars_decidable) p (S (S x))); auto.
        assert (S (S x) > (S (S j))) by lia.
        eapply (proj1 n_fv_down_Sn') with (k := (S (S j))); eauto. lia.
        intro Hfv. apply H0; free_var_econstructor; eauto.
    - intros [|] ?; simpl.
      * intro. inversion H3.
      * intro. apply (H1 n).
        ** free_var_econstructor; eauto.
        ** unfold upM in H3. apply fv_up_Sn2' in H3; auto. lia.
  + rewrite H; try rewrite H0;
    try (intro Hfv; apply H1; free_var_econstructor; eauto).
    - f_equal.
      {
        apply subst_extensional_only_free_vars.
        intros.
        destruct x as [|]; auto; simpl.
        unfold down_subst_at_n.
        destruct (Nat.ltb (S x) (S (S j))) eqn:E.
        - apply PeanoNat.Nat.ltb_lt in E. assert (x < S j) by lia.
          apply PeanoNat.Nat.ltb_lt in H4; rewrite H4. simpl.
          unfold upM.
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto; try lia.
          apply H2. apply fv_choice_l.
          destruct ((proj1 free_vars_decidable) p (S x)); auto.
          apply ((proj1 nfv_down_lt) _ _ _ E) in H5. congruence.
        - apply PeanoNat.Nat.ltb_nlt in E. assert (~ x < S j) by lia.
          apply PeanoNat.Nat.ltb_nlt in H4; rewrite H4; simpl.
          unfold upM.
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto. lia.
          apply H2. apply fv_choice_l.
          destruct ((proj1 free_vars_decidable) p (S (S x))); auto.
          assert (S (S x) > (S (S j))) by lia.
          eapply (proj1 n_fv_down_Sn') with (k := (S (S j))); eauto. lia.
          intro Hfv. apply H1; free_var_econstructor; eauto.
      }
      {
        apply subst_extensional_only_free_vars.
        intros.
        destruct x as [|]; auto; simpl.
        unfold down_subst_at_n.
        destruct (Nat.ltb (S x) (S (S j))) eqn:E.
        - apply PeanoNat.Nat.ltb_lt in E. assert (x < S j) by lia.
          apply PeanoNat.Nat.ltb_lt in H4; rewrite H4. simpl.
          unfold upM.
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto; try lia.
          apply H2. apply fv_choice_r.
          destruct ((proj1 free_vars_decidable) p0 (S x)); auto.
          apply ((proj1 nfv_down_lt) _ _ _ E) in H5. congruence.
        - apply PeanoNat.Nat.ltb_nlt in E. assert (~ x < S j) by lia.
          apply PeanoNat.Nat.ltb_nlt in H4; rewrite H4; simpl.
          unfold upM.
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto. lia.
          apply H2. apply fv_choice_r.
          destruct ((proj1 free_vars_decidable) p0 (S (S x))); auto.
          assert (S (S x) > (S (S j))) by lia.
          eapply (proj1 n_fv_down_Sn') with (k := (S (S j))); eauto. lia.
          intro Hfv. apply H1; free_var_econstructor; eauto.
      }
    - intros [|] ?; simpl.
      * intro. inversion H4.
      * intro. apply (H2 n).
        ** free_var_econstructor; eauto.
        ** unfold upM in H4. apply fv_up_Sn2' in H4; auto. lia.
    - intros [|] ?; simpl.
      * intro. inversion H4.
      * intro. apply (H2 n).
        ** free_var_econstructor; eauto.
        ** unfold upM in H4. apply fv_up_Sn2' in H4; auto. lia.
  + rewrite H; try rewrite H0;
    try (intro Hfv; apply H1; free_var_econstructor; eauto).
    - f_equal.
      {
        apply subst_extensional_only_free_vars.
        intros.
        destruct x as [|]; auto; simpl.
        unfold down_subst_at_n.
        destruct (Nat.ltb (S x) (S (S j))) eqn:E.
        - apply PeanoNat.Nat.ltb_lt in E. assert (x < S j) by lia.
          apply PeanoNat.Nat.ltb_lt in H4; rewrite H4. simpl.
          unfold upM.
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto; try lia.
          apply H2. apply fv_send_l.
          destruct ((proj1 free_vars_decidable) p (S x)); auto.
          apply ((proj1 nfv_down_lt) _ _ _ E) in H5. congruence.
        - apply PeanoNat.Nat.ltb_nlt in E. assert (~ x < S j) by lia.
          apply PeanoNat.Nat.ltb_nlt in H4; rewrite H4; simpl.
          unfold upM.
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto. lia.
          apply H2. apply fv_send_l.
          destruct ((proj1 free_vars_decidable) p (S (S x))); auto.
          assert (S (S x) > (S (S j))) by lia.
          eapply (proj1 n_fv_down_Sn') with (k := (S (S j))); eauto. lia.
          intro Hfv. apply H1; free_var_econstructor; eauto.
      }
      {
        apply subst_extensional_only_free_vars.
        intros.
        destruct x as [|]; auto; simpl.
        unfold down_subst_at_n.
        destruct (Nat.ltb (S x) (S (S j))) eqn:E.
        - apply PeanoNat.Nat.ltb_lt in E. assert (x < S j) by lia.
          apply PeanoNat.Nat.ltb_lt in H4; rewrite H4. simpl.
          unfold upM.
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto; try lia.
          apply H2. apply fv_send_r.
          destruct ((proj1 free_vars_decidable) p0 (S x)); auto.
          apply ((proj1 nfv_down_lt) _ _ _ E) in H5. congruence.
        - apply PeanoNat.Nat.ltb_nlt in E. assert (~ x < S j) by lia.
          apply PeanoNat.Nat.ltb_nlt in H4; rewrite H4; simpl.
          unfold upM.
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto. lia.
          apply H2. apply fv_send_r.
          destruct ((proj1 free_vars_decidable) p0 (S (S x))); auto.
          assert (S (S x) > (S (S j))) by lia.
          eapply (proj1 n_fv_down_Sn') with (k := (S (S j))); eauto. lia.
          intro Hfv. apply H1; free_var_econstructor; eauto.
      }
    - intros [|] ?; simpl.
      * intro. inversion H4.
      * intro. apply (H2 n).
        ** free_var_econstructor; eauto.
        ** unfold upM in H4. apply fv_up_Sn2' in H4; auto. lia.
    - intros [|] ?; simpl.
      * intro. inversion H4.
      * intro. apply (H2 n).
        ** free_var_econstructor; eauto.
        ** unfold upM in H4. apply fv_up_Sn2' in H4; auto. lia.
  + rewrite H.
    - f_equal.
      {
        apply subst_extensional_only_free_vars.
        intros.
        destruct x as [|[|]]; auto; simpl.
        unfold down_subst_at_n.
        destruct (Nat.ltb (S (S n)) (S (S (S j)))) eqn:E.
        - apply PeanoNat.Nat.ltb_lt in E. assert (n < S j) by lia.
          apply PeanoNat.Nat.ltb_lt in H3; rewrite H3. simpl.
          unfold upM.
          assert ( ~ occurs_free_message j (σ n) ).
          {
            apply H1. econstructor; auto.
            destruct ((proj1 free_vars_decidable) p (S (S n ))); auto.
            apply ((proj1 nfv_down_lt) _ _ _ E) in H4. congruence.
          }
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto; try lia.
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto; try lia.
          intro. apply (proj1 (proj2 fv_up_Sn2')) with (k := 0) in H5; eauto. lia.
        - apply PeanoNat.Nat.ltb_nlt in E. assert (~ n < S j) by lia.
          apply PeanoNat.Nat.ltb_nlt in H3; rewrite H3; simpl.
          unfold upM.
          assert ( ~ occurs_free_message j (σ (S n)) ).
          {
            apply H1. econstructor.
            destruct ((proj1 free_vars_decidable) p (S (S (S n)))); auto.
            assert (S (S (S n)) > (S (S (S j)))) by lia.
            eapply (proj1 n_fv_down_Sn') with (k := (S (S (S j)))); eauto. lia.
            intro Hfv. apply H0; free_var_econstructor; eauto.
          }
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto; try lia.
          rewrite (proj1 (proj2 down_after_down_gt_commute_nfv)); auto; try lia.
          intro. apply (proj1 (proj2 fv_up_Sn2')) with (k := 0) in H5; eauto. lia.
      }
    - intro; apply H0; free_var_econstructor; eauto.
    - intros [|[|]] ?; simpl.
      * intro. inversion H3.
      * intro. inversion H3.
      * intro. apply (H1 n).
        ** free_var_econstructor; eauto.
        ** unfold upM in H3.
           apply fv_up_Sn2' in H3; auto; try lia.
           apply fv_up_Sn2' in H3; auto; try lia.
  + auto.
  + f_equal. rewrite H; auto.
    intro; apply H0; free_var_econstructor; eauto.
    intros. apply H1; free_var_econstructor; eauto.
Qed.

Lemma down_k_down_Sj_lt_commute2 :
  (forall P,
    forall k j, k < S j ->
      down1_process (down1_process P k) j
        = down1_process (down1_process P (S j)) k) /\
  (forall M,
    forall k j, k < S j ->
      down1_message (down1_message M k) j
        = down1_message (down1_message M (S j)) k) /\
  (forall s,
    forall k j, k < S j ->
      down1_statement (down1_statement s k) j
        = down1_statement (down1_statement s (S j)) k).
Proof.
  apply syntax_ind; intros; simpl; auto;
  try (now (rewrite H; try rewrite H0; auto; intro; try apply H2; try apply H1; free_var_econstructor; eauto));
  try (now (rewrite (H (S k) (S j)); try rewrite (H0 (S k) (S j)); try lia; auto;
            intro; try apply H2; try apply H1; free_var_econstructor; eauto)).
  + rewrite (H (S k) (S j)); try rewrite H0; try lia; auto; intro; apply H2; free_var_econstructor; eauto.
  + destruct (Nat.ltb (S j) n) eqn:E.
    - apply PeanoNat.Nat.ltb_lt in E. assert (k < n) by lia.
      apply PeanoNat.Nat.ltb_lt in H0. rewrite H0. destruct n; try (exfalso; lia).
      simpl. assert (j < n) by lia. apply PeanoNat.Nat.ltb_lt in H1. rewrite H1.
      assert (k < n) by lia. apply PeanoNat.Nat.ltb_lt in H2. rewrite H2. auto.
    - apply PeanoNat.Nat.ltb_nlt in E. simpl.
      destruct (Nat.ltb k n) eqn:E1.
      * apply PeanoNat.Nat.ltb_lt in E1; destruct n; try (exfalso; lia).
        simpl. assert (~ (j < n)) by lia. apply PeanoNat.Nat.ltb_nlt in H0.
        rewrite H0; auto.
      * apply PeanoNat.Nat.ltb_nlt in E1. simpl.
        assert (~ (j < n)) by lia. apply PeanoNat.Nat.ltb_nlt in H0. rewrite H0; auto.
  + f_equal. rewrite H; auto.
  + rewrite (H (S (S k)) (S (S j))); try lia. auto; intro; apply H1; free_var_econstructor; eauto.
  + rewrite H; auto.
Qed.

Lemma down_over_reduce_axcut' :
  forall n E M P j,
    n = length_axcut_ctx E ->
    well_formed_axcut_ctx 0 E ->
    ~ (S j) ∈ P ->
    ~ (occurs_free_ctx (S j) E) ->
    ~ (occurs_free_message (length_axcut_ctx E + (S j)) M) ->
    ~ (occurs_free_message (length_axcut_ctx E) M) ->
    down1_process (reduce_axcut E M P) j =
    reduce_axcut
      (down1_ctx E (S j))
      (down1_message M (length_axcut_ctx E + S j))
      (down1_process P (S j)).
Proof.
  intro n.
  induction n; intros;
  destruct E; simpl in H; try congruence; simpl.
  + rewrite reduce_axcut_equation_1.
    unfold relocate. destruct (Nat.leb (S j) n) eqn:E; simpl.
    - rewrite reduce_axcut_equation_1.
      unfold downM.
      rewrite (proj1 down_over_subst); auto.
      * erewrite (proj1 subst_extensional_only_free_vars); eauto.
        intros. destruct x; auto; simpl.
        ** unfold down_subst_at_n; simpl in *.
           rewrite (proj1 (proj2 down_k_down_Sj_lt_commute2)); auto. lia.
        ** unfold down_subst_at_n.
           destruct (Nat.ltb (S x) (S j)) eqn:E1.
           {
            simpl. apply PeanoNat.Nat.ltb_lt in E1.
            assert (~ j < x) by lia. apply PeanoNat.Nat.ltb_nlt in H6; rewrite H6.
            reflexivity.
           }
           {
            simpl. apply PeanoNat.Nat.ltb_nlt in E1.
            assert (j < S x) by lia. apply PeanoNat.Nat.ltb_lt in H6; rewrite H6.
            reflexivity.
           }
      * intros. destruct n0.
        ** simpl in *. intro.
           apply n_fv_down_Sn' in H6; auto. lia.
        ** simpl. unfold id_subst; simpl. intro.
           inversion H6; subst. congruence.
    - rewrite reduce_axcut_equation_1.
      unfold downM.
      rewrite (proj1 down_over_subst); auto.
      * erewrite (proj1 subst_extensional_only_free_vars); eauto.
        intros. destruct x; auto; simpl.
        ** unfold down_subst_at_n; simpl.
           rewrite (proj1 (proj2 down_k_down_Sj_lt_commute2)); auto. lia.
        ** unfold down_subst_at_n.
           destruct (Nat.ltb (S x) (S j)) eqn:E1.
           {
            simpl. apply PeanoNat.Nat.ltb_lt in E1.
            assert (~ j < x) by lia. apply PeanoNat.Nat.ltb_nlt in H6; rewrite H6.
            reflexivity.
           }
           {
            simpl. apply PeanoNat.Nat.ltb_nlt in E1.
            assert (j < S x) by lia. apply PeanoNat.Nat.ltb_lt in H6; rewrite H6.
            reflexivity.
           }
      * intros. destruct n0.
        ** simpl in *. intro.
           apply n_fv_down_Sn' in H6; auto. lia.
        ** simpl. unfold id_subst; simpl. intro.
           inversion H6; subst. congruence.
  + rewrite reduce_axcut_equation_2.
    unfold relocate. destruct (Nat.leb (S j) n) eqn:E; simpl.
    - rewrite reduce_axcut_equation_2.
      unfold downM.
      rewrite (proj1 down_over_subst); auto.
      * erewrite (proj1 subst_extensional_only_free_vars); eauto.
        intros. destruct x; auto; simpl.
        ** unfold down_subst_at_n; simpl in *.
           rewrite (proj1 (proj2 down_k_down_Sj_lt_commute2)); auto. lia.
        ** unfold down_subst_at_n.
           destruct (Nat.ltb (S x) (S j)) eqn:E1.
           {
            simpl. apply PeanoNat.Nat.ltb_lt in E1.
            assert (~ j < x) by lia. apply PeanoNat.Nat.ltb_nlt in H6; rewrite H6.
            reflexivity.
           }
           {
            simpl. apply PeanoNat.Nat.ltb_nlt in E1.
            assert (j < S x) by lia. apply PeanoNat.Nat.ltb_lt in H6; rewrite H6.
            reflexivity.
           }
      * intros. destruct n0.
        ** simpl in *. intro.
           apply n_fv_down_Sn' in H6; auto. lia.
        ** simpl. unfold id_subst; simpl. intro.
           inversion H6; subst. congruence.
    - rewrite reduce_axcut_equation_2.
      unfold downM.
      rewrite (proj1 down_over_subst); auto.
      * erewrite (proj1 subst_extensional_only_free_vars); eauto.
        intros. destruct x; auto; simpl.
        ** unfold down_subst_at_n; simpl.
           rewrite (proj1 (proj2 down_k_down_Sj_lt_commute2)); auto. lia.
        ** unfold down_subst_at_n.
           destruct (Nat.ltb (S x) (S j)) eqn:E1.
           {
            simpl. apply PeanoNat.Nat.ltb_lt in E1.
            assert (~ j < x) by lia. apply PeanoNat.Nat.ltb_nlt in H6; rewrite H6.
            reflexivity.
           }
           {
            simpl. apply PeanoNat.Nat.ltb_nlt in E1.
            assert (j < S x) by lia. apply PeanoNat.Nat.ltb_lt in H6; rewrite H6.
            reflexivity.
           }
      * intros. destruct n0.
        ** simpl in *. intro.
           apply n_fv_down_Sn' in H6; auto. lia.
        ** simpl. unfold id_subst; simpl. intro.
           inversion H6; subst. congruence.
  + rewrite reduce_axcut_equation_3; simpl.
    rewrite reduce_axcut_equation_3; simpl.
    f_equal.
    - rewrite <- (proj1 down_at_k_rename_id_after_k_commute).
      * unfold down.
        rewrite (proj1 down_k_down_Sj_lt_commute2); auto.
        lia.
      * apply swap01_is_bijective.
      * intros [|[|]] ?; auto; exfalso; lia.
    - rewrite IHn; auto.
      * f_equal.
        ** rewrite down_at_k_rename_id_after_k_commute_ctx; auto.
           apply swap01_is_bijective.
           intros [|[|]] ?; auto; exfalso; lia.
        ** rewrite down_ctx_preserves_length.
           rewrite <- rename_axcut_ctx_preserves_length.
           replace (length_axcut_ctx E + S (S j))
              with (S (length_axcut_ctx E + S j))
                by lia.
           rewrite (proj1 (proj2 down_at_k_rename_id_after_k_commute)); auto.
           apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
           intros.
           rewrite up_ren_n_swap_not_nSn; lia.
        ** rewrite (proj1 down_at_k_rename_id_after_k_commute).
           -- f_equal. unfold up.
              rewrite (proj1 down_after_down_gt_commute_nfv); auto. lia.
           -- apply swap01_is_bijective.
           -- intros [|[|]] ?; auto; exfalso; lia.
      * rewrite <- rename_axcut_ctx_preserves_length.
        inversion H; auto.
      * replace 0 with (swap01 1) by auto;
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01.
        inversion H0; auto.
      * replace (S (S j)) with (swap01 (S (S j))) by auto.
        apply nfv_under_renaming; try apply swap01_is_bijective.
        unfold up. intro.
        apply fv_up_Sn2 in H5; try lia. congruence.
      * replace (S (S j)) with (swap01 (S (S j))) by auto.
        apply nfv_ctx_under_renaming; try apply swap01_is_bijective.
        intro. apply H2. apply fv_ctx_cons_l2. auto.
      * simpl in H3.
        rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E + S (S j)) with
                (S (length_axcut_ctx E + S j)) by lia.
        replace (S (length_axcut_ctx E + S j)) with
          ((up_ren_n (length_axcut_ctx E) swap01) (S (length_axcut_ctx E + S j))).
        apply nfv_under_renaming; auto.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        rewrite up_ren_n_swap_not_nSn; lia.
      * simpl in H4.
        rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E) with
          ((up_ren_n (length_axcut_ctx E) swap01) (S (length_axcut_ctx E)))
          at 1.
        apply nfv_under_renaming; auto.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        rewrite up_ren_n_swap_Sn; reflexivity.
  + rewrite reduce_axcut_equation_4; simpl.
    rewrite reduce_axcut_equation_4; simpl.
    f_equal.
    - rewrite IHn; auto.
      * f_equal.
        ** rewrite down_at_k_rename_id_after_k_commute_ctx; auto.
           apply swap01_is_bijective.
           intros [|[|]] ?; auto; exfalso; lia.
        ** rewrite down_ctx_preserves_length.
           rewrite <- rename_axcut_ctx_preserves_length.
           replace (length_axcut_ctx E + S (S j))
              with (S (length_axcut_ctx E + S j))
                by lia.
           rewrite (proj1 (proj2 down_at_k_rename_id_after_k_commute)); auto.
           apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
           intros.
           rewrite up_ren_n_swap_not_nSn; lia.
        ** rewrite (proj1 down_at_k_rename_id_after_k_commute).
           -- f_equal. unfold up.
              rewrite (proj1 down_after_down_gt_commute_nfv); auto. lia.
           -- apply swap01_is_bijective.
           -- intros [|[|]] ?; auto; exfalso; lia.
      * rewrite <- rename_axcut_ctx_preserves_length.
        inversion H; auto.
      * replace 0 with (swap01 1) by auto;
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01.
        inversion H0; auto.
      * replace (S (S j)) with (swap01 (S (S j))) by auto.
        apply nfv_under_renaming; try apply swap01_is_bijective.
        unfold up. intro.
        apply fv_up_Sn2 in H5; try lia. congruence.
      * replace (S (S j)) with (swap01 (S (S j))) by auto.
        apply nfv_ctx_under_renaming; try apply swap01_is_bijective.
        intro. apply H2. apply fv_ctx_cons_r2. auto.
      * simpl in H3.
        rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E + S (S j)) with
                (S (length_axcut_ctx E + S j)) by lia.
        replace (S (length_axcut_ctx E + S j)) with
          ((up_ren_n (length_axcut_ctx E) swap01) (S (length_axcut_ctx E + S j))).
        apply nfv_under_renaming; auto.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        rewrite up_ren_n_swap_not_nSn; lia.
      * simpl in H4.
        rewrite <- rename_axcut_ctx_preserves_length.
        replace (length_axcut_ctx E) with
          ((up_ren_n (length_axcut_ctx E) swap01) (S (length_axcut_ctx E)))
          at 1.
        apply nfv_under_renaming; auto.
        apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
        rewrite up_ren_n_swap_Sn; reflexivity.
    - rewrite <- (proj1 down_at_k_rename_id_after_k_commute).
      * unfold down.
        rewrite (proj1 down_k_down_Sj_lt_commute2); auto.
        lia.
      * apply swap01_is_bijective.
      * intros [|[|]] ?; auto; exfalso; lia.
Qed.

Lemma down_over_reduce_axcut :
  forall E M P j,
    well_formed_axcut_ctx 0 E ->
    ~ (S j) ∈ P ->
    ~ (occurs_free_ctx (S j) E) ->
    ~ (occurs_free_message (length_axcut_ctx E + (S j)) M) ->
    ~ (occurs_free_message (length_axcut_ctx E) M) ->
    down1_process (reduce_axcut E M P) j =
    reduce_axcut
      (down1_ctx E (S j))
      (down1_message M (length_axcut_ctx E + S j))
      (down1_process P (S j)).
Proof.
  intros. eapply down_over_reduce_axcut'; eauto.
Qed.

Lemma equiv_red_invariant_under_down :
  forall Γ P P', Γ ⊢ P :# -> P ⊵ P' ->
    forall j, ~ j ∈ P -> down1_process P j ⊵ down1_process P' j.
Proof.
  intros.
  generalize dependent Γ.
  generalize dependent j.
  induction H0; intros; simpl; try (now econstructor).
  + econstructor. subst.
    rewrite (proj1 down_at_k_rename_id_after_k_commute).
    - f_equal. unfold up.
      rewrite (proj1 down_after_down_gt_commute); auto.
      lia.
    - apply swap01_is_bijective.
    - intros [|[|]] ?; auto; exfalso; lia.
  + econstructor. subst.
    rewrite (proj1 down_at_k_rename_id_after_k_commute).
    - f_equal. unfold up.
      rewrite (proj1 down_after_down_gt_commute); auto.
      lia.
    - apply swap01_is_bijective.
    - intros [|[|]] ?; auto; exfalso; lia.
  + rewrite H, H1.
    rewrite down_ctx_over_fill_hole.
    assert (
          ~ (S j) ∈ (fill_hole E M)
        ). { intro; apply H2; subst; free_var_econstructor; eauto. }
    destruct (nfv_fill_hole _ _ _ H4).
    assert (
      down1_process (reduce_axcut E M P) j =
      reduce_axcut
        (down1_ctx E (S j))
        (down1_message M (length_axcut_ctx E + S j))
        (down1_process P (S j))
    ).
    {
      apply down_over_reduce_axcut; auto.
      + intro; apply H2; free_var_econstructor; eauto.
      + rewrite H in H3; inversion H3; subst.
        replace (length_axcut_ctx E) with (length_axcut_ctx E + 0) by lia.
        apply (nfv_well_typed_fill_hole _ _ _ _ H0 H11).
    }
    rewrite H7. econstructor; eauto.
    apply downE_preserves_well_formedness_nfv2; auto. lia.
  + rewrite H, H1.
    rewrite down_ctx_over_fill_hole.
    assert (
          ~ (S j) ∈ (fill_hole E M)
        ). { intro; apply H2; subst; free_var_econstructor; eauto. }
    destruct (nfv_fill_hole _ _ _ H4).
    assert (
      down1_process (reduce_axcut E M P) j =
      reduce_axcut
        (down1_ctx E (S j))
        (down1_message M (length_axcut_ctx E + S j))
        (down1_process P (S j))
    ).
    {
      apply down_over_reduce_axcut; auto.
      + intro; apply H2; free_var_econstructor; eauto.
      + rewrite H in H3; inversion H3; subst.
        replace (length_axcut_ctx E) with (length_axcut_ctx E + 0) by lia.
        apply (nfv_well_typed_fill_hole _ _ _ _ H0 H12).
    }
    rewrite H7. eapply rp_ax_cut_r; eauto.
    apply downE_preserves_well_formedness_nfv2; auto. lia.
  + rewrite (proj1 down_over_subst).
    - erewrite (proj1 subst_extensional).
      * econstructor.
      * intros [|]; auto. simpl.
        unfold down_subst_at_n.
        destruct (Nat.ltb (S n) (S j)) eqn: E.
        ** simpl.
           apply PeanoNat.Nat.ltb_lt in E.
           assert (~ (j < n)) by lia. apply PeanoNat.Nat.ltb_nlt in H0.
           rewrite H0. reflexivity.
        ** simpl. apply PeanoNat.Nat.ltb_nlt in E.
           assert (j < (S n)) by lia. apply PeanoNat.Nat.ltb_lt in H0; rewrite H0.
           reflexivity.
    - intro Hfv. apply H1. free_var_econstructor; eauto.
    - intros. intro. destruct n; simpl in H2.
      * inversion H2; subst. apply H1; free_var_econstructor; eauto.
      * inversion H2; subst. apply H1; free_var_econstructor; eauto.
  + apply rp_cong_cut_l. inversion H; subst.
    eapply IHequiv_reduces; eauto.
    intro Hfv; apply H1; free_var_econstructor; eauto.
  + apply rp_cong_cut_r. inversion H; subst.
    eapply IHequiv_reduces; eauto.
    intro Hfv; apply H1; free_var_econstructor; eauto.
  + apply rp_cong_seq. inversion H; subst.
    eapply IHequiv_reduces; eauto.
    intro Hfv; apply H1; free_var_econstructor; eauto.
Qed.

(******************************************************************************)
(* Permuting a cut association into reduce_axcut                              *)
(******************************************************************************)
Corollary c_refl_inversion_eq :
  forall P Q, P = Q -> P ≡ Q.
Proof. intros; subst; apply c_refl. Qed.

Lemma subst_nfv_down :
  (forall P σ n,
    ~ n ∈ P ->
    (forall j, j < n -> σ j = future j) ->
    (forall j, j >= n -> σ (S j) = future j) ->
    subst_process P σ = down1_process P n) /\
  (forall M σ n,
    ~ (occurs_free_message n M) ->
    (forall j, j < n -> σ j = future j) ->
    (forall j, j >= n -> σ (S j) = future j) ->
    subst_message M σ = down1_message M n) /\
  (forall s σ n,
    ~ (occurs_free_statement n s) ->
    (forall j, j < n -> σ j = future j) ->
    (forall j, j >= n -> σ (S j) = future j) ->
    subst_statement s σ = down1_statement s n).
Proof.
  apply syntax_ind; intros; simpl;
  try assert (forall j : nat, j < S n -> up_subst σ j = future j)
    by (intros; destruct j; auto; simpl; try rewrite H1; try rewrite H2; try lia; simpl; unfold relocate; auto);
  try assert (forall j : nat, j >= S n -> up_subst σ (S j) = future j)
    by (intros; destruct j; try (exfalso; lia); simpl;try rewrite H3; try rewrite H2; try lia; reflexivity);
  try (try erewrite H; eauto; try erewrite H0; eauto; intro Hfv; try apply H1; try apply H0; free_var_econstructor; eauto).
  + destruct (Nat.ltb n0 n) eqn:E.
    - apply PeanoNat.Nat.ltb_lt in E. destruct n; try (exfalso; lia).
      rewrite H1; auto; lia.
    - apply PeanoNat.Nat.ltb_nlt in E.
      assert (n0 <> n). { destruct (PeanoNat.Nat.eq_dec n0 n); auto. exfalso; apply H. subst. econstructor. }
      assert (n < n0 ) by lia. rewrite H0; auto.
  + rewrite H with (n := S (S n)); eauto.
    intro Hfv; try apply H1; try apply H0; free_var_econstructor; eauto.
    - intros. destruct j as [|[|]]; auto; simpl. rewrite H1; try lia. reflexivity.
    - intros. destruct j as [|[|]]; try (exfalso; lia); simpl. rewrite H2; try lia. reflexivity.
Qed.

Lemma permute_cut_assoc_reduce_axcut' :
  forall n P E M Q,
    n = length_axcut_ctx E ->
    well_formed_axcut_ctx 0 E ->
    ~ (occurs_free_ctx 1 E) ->
    ~ occurs_free_message (length_axcut_ctx E) M ->
    ~ occurs_free_message (S (length_axcut_ctx E)) M ->
    (cut P (reduce_axcut E M Q)) ≡
    (reduce_axcut
      (downE (rename_axcut_ctx E swap01))
      (down1_message (rename_message M (up_ren_n (length_axcut_ctx E) swap01)) (length_axcut_ctx E))
      (cut (rename_process (up P) swap01) (rename_process Q swap01))
    ).
Proof.
  intros n.
  induction n; intros; destruct E; simpl in H; try congruence.
  + inversion H; subst; simpl.
    rewrite reduce_axcut_equation_1.
    unfold downE. simpl.
    rewrite reduce_axcut_equation_1. simpl in *.
    rewrite (proj1 (proj2 renaming_idempotent_free_vars)).
    - assert (
        forall x,
          up_subst (downM (downM M) ⋅ id_subst) x =
            swap_subst (downM M ⋅ id_subst) 0 1 x
      ).
      {
        intros [|[|]]; simpl; try reflexivity.
        unfold upM, downM.
        rewrite (proj1 (proj2 up_after_down_id)).
        + reflexivity.
        + intros Hfv. apply H3.
          eapply (proj1 (proj2 n_fv_down_Sn')); eauto.
      }
      rewrite ((proj1 subst_extensional) _ _ _ H4).
      rewrite ((proj1 subst_extensional) _ _ _ H4).
      replace swap01 with (up_ren_n 0 swap01) by auto.
      repeat rewrite (proj1 up_ren_swap_subst_cancel).
      apply c_refl_inversion_eq; f_equal.
      rewrite (proj1 subst_nfv_down) with (n := 0).
      * unfold up. rewrite (proj1 down_after_up_id); auto.
      * apply nfv_lift_n; lia.
      * intros; exfalso; lia.
      * intros; simpl. reflexivity.
    - intros [|[|]] ?; try congruence. reflexivity.
  + inversion H; subst; simpl.
    rewrite reduce_axcut_equation_2.
    unfold downE. simpl.
    rewrite reduce_axcut_equation_2. simpl in *.
    rewrite (proj1 (proj2 renaming_idempotent_free_vars)).
    - assert (
        forall x,
          up_subst (downM (downM M) ⋅  id_subst) x =
            swap_subst (downM M ⋅ id_subst) 0 1 x
      ).
      {
        intros [|[|]]; simpl; try reflexivity.
        unfold upM, downM.
        rewrite (proj1 (proj2 up_after_down_id)).
        + reflexivity.
        + intros Hfv. apply H3.
          eapply (proj1 (proj2 n_fv_down_Sn')); eauto.
      }
      rewrite ((proj1 subst_extensional) _ _ _ H4).
      rewrite ((proj1 subst_extensional) _ _ _ H4).
      replace swap01 with (up_ren_n 0 swap01) by auto.
      repeat rewrite (proj1 up_ren_swap_subst_cancel).
      apply c_refl_inversion_eq; f_equal.
      rewrite (proj1 subst_nfv_down) with (n := 0).
      * unfold up. rewrite (proj1 down_after_up_id); auto.
      * apply nfv_lift_n; lia.
      * intros; exfalso; lia.
      * intros; simpl. reflexivity.
    - intros [|[|]] ?; try congruence. reflexivity.
  + rewrite reduce_axcut_equation_3.
    unfold downE; simpl.
    rewrite reduce_axcut_equation_3.
    inversion H0; subst.
    eapply c_trans. apply c_cut_comm.
    eapply c_trans. apply c_cut_assoc; eauto.
    {
      assert (~ 2 ∈ P0). { intro Hfv. apply H1. apply fv_ctx_cons_l1. auto. }
      intro Hfv.
      unfold down in Hfv. apply n_fv_down_Sn in Hfv; try lia.
      replace 2 with (swap01 2) in Hfv by auto.
      apply fv_under_renaming in Hfv.
      congruence.
      apply swap01_is_bijective.
    }
    apply c_cong_cut.
    - apply c_refl_inversion_eq. f_equal. f_equal.
      assert (~ 2 ∈ P0).
      { intro Hfv. apply H1. apply fv_ctx_cons_l1. assumption. }
      assert (
        rename_process P0 (up_ren swap01) = P0
      ).
      {
        rewrite (proj1 renaming_idempotent_free_vars); auto.
        intros [|[|[|]]] ?; auto; try congruence.
      }
      rewrite H5.
      replace swap01 with (up_ren_n 0 swap01) by auto; unfold down.
      rewrite (proj1 up_ren_n_swap_down_down_Sn); auto.
    - eapply c_trans. apply c_cut_comm.
      eapply c_trans.
      * replace swap01 with (up_ren_n 0 swap01) at 5 by auto.
        rewrite up_ren_swap_over_reduce_axcut.
        ** apply IHn.
           -- repeat rewrite <- rename_axcut_ctx_preserves_length.
              inversion H; auto.
           -- replace 0 with
                ((up_ren_n 1 swap01) (swap01 1)) by auto.
              apply well_formedness_preserved_under_swap01.
              replace swap01 with (up_ren_n 0 swap01) by auto.
              apply well_formedness_preserved_under_swap01.
              assumption.
           -- replace 1 with
                ((up_ren_n 1 swap01) (swap01 2)) at 1 by auto.
              apply nfv_ctx_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              apply nfv_ctx_under_renaming.
              apply swap01_is_bijective.
              intro Hfv. apply H1. apply fv_ctx_cons_l2. auto.
           -- repeat rewrite <- rename_axcut_ctx_preserves_length.
              replace (length_axcut_ctx E + 1) with (S (length_axcut_ctx E)) by lia.
              assert (
                length_axcut_ctx E =
                  (up_ren_n (S (length_axcut_ctx E)) swap01)
                  (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
              ).
              {
                rewrite up_ren_n_swap_Sn.
                rewrite up_ren_n_swap_not_nSn; lia.
              }
              rewrite H4 at 1.
              apply nfv_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              apply nfv_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              assumption.
           -- repeat rewrite <- rename_axcut_ctx_preserves_length.
              replace (length_axcut_ctx E + 1) with (S (length_axcut_ctx E)) by lia.
              assert (
                S (length_axcut_ctx E) =
                  (up_ren_n (S (length_axcut_ctx E)) swap01)
                  (up_ren_n (length_axcut_ctx E) swap01 (S (S (length_axcut_ctx E))))
              ).
              {
                rewrite (up_ren_n_swap_not_nSn _ (S (S (length_axcut_ctx E)))); try lia.
                rewrite up_ren_n_swap_Sn; auto.
              }
              rewrite H4 at 1.
              apply nfv_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              apply nfv_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              assumption.
        ** replace swap01 with (up_ren_n 0 swap01) by auto.
           replace 0 with (up_ren_n 0 swap01 1) at 1 by auto.
           apply well_formedness_preserved_under_swap01; assumption.
        ** rewrite <- rename_axcut_ctx_preserves_length.
           replace (length_axcut_ctx E)
              with (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
               at 1 by (rewrite up_ren_n_swap_Sn; auto).
           apply nfv_under_renaming.
           apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
           simpl in H2. assumption.
      * assert (forall P Q, P = Q -> P ≡ Q) by (intros; subst; apply c_refl).
        apply H4. f_equal.
        ** repeat rewrite <- rename_axcut_ctx_preserves_length.
           unfold downE. replace swap01 with (up_ren_n 0 swap01) at 3 by auto.
           rewrite up_ren_n_swap_down_down_Sn_ctx.
           {
            rewrite up_ren_n_swap_down_down_Sn_ctx.
            + replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
              rewrite up_ren_n_swap_down_down_Sn_ctx.
              - rewrite down_at_k_rename_id_after_k_commute_ctx; auto.
                apply swap01_is_bijective. intros [|[|]] ?; auto; exfalso; lia.
              - intro Hfv; apply H1; apply fv_ctx_cons_l2; auto.
            + replace 2 with (swap01 2) by auto. apply nfv_ctx_under_renaming.
              apply swap01_is_bijective. intros Hfv. apply H1. apply fv_ctx_cons_l2. auto.
           }
           {
            replace 1 with (up_ren_n 1 swap01 2) at 1 by auto.
            apply nfv_ctx_under_renaming.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            intro  Hfv. apply H1. apply fv_ctx_cons_l2; auto.
            replace 2 with (swap01 2) in Hfv by auto.
            apply fv_ctx_under_renaming in Hfv; auto. apply swap01_is_bijective.
           }
        ** repeat rewrite <- rename_axcut_ctx_preserves_length.
           replace (length_axcut_ctx E + 1) with (S (length_axcut_ctx E)) by lia.
           rewrite (proj1 (proj2 up_ren_n_swap_down_down_Sn)).
           -- rewrite (proj1 (proj2 up_ren_n_swap_down_down_Sn)).
              ++ rewrite down_ctx_preserves_length.
                 rewrite <- rename_axcut_ctx_preserves_length.
                 replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
                    with (up_ren_n (S (length_axcut_ctx E)) swap01) by auto.
                 rewrite (proj1 (proj2 up_ren_n_swap_down_down_Sn)); auto.
                 rewrite (proj1 (proj2  down_at_k_rename_id_after_k_commute)); auto.
                 apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
                 intros. rewrite up_ren_n_swap_not_nSn; try lia.
              ++ replace (S (S (length_axcut_ctx E)))
                    with (up_ren_n (length_axcut_ctx E) swap01 (S (S (length_axcut_ctx E))))
                      by (rewrite up_ren_n_swap_not_nSn; lia).
                 apply nfv_under_renaming.
                 apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
                 assumption.
           -- replace (S (length_axcut_ctx E))
                 with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (S (length_axcut_ctx E))))
                   at 1 by (rewrite up_ren_n_swap_Sn; auto).
              apply nfv_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              replace (S (S (length_axcut_ctx E)))
                 with (up_ren_n (length_axcut_ctx E) swap01 (S (S (length_axcut_ctx E))))
                   by (rewrite up_ren_n_swap_not_nSn; lia).
              apply nfv_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              assumption.
        ** simpl. f_equal.
           -- unfold up. replace swap01 with (up_ren_n 0 swap01) by auto.
              repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
              rewrite (proj1 shift_additive); simpl.
              rewrite (proj1 lift_k_lift_Sj_lt_commute); try lia.
              rewrite (proj1 shift_additive); auto.
           -- unfold up.
              replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
              repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
              rewrite (proj1 lift_at_k_rename_id_after_k_commute); auto.
              apply swap01_is_bijective. intros [|[|]] ?; auto; exfalso; lia.
  + rewrite reduce_axcut_equation_4.
    unfold downE; simpl.
    rewrite reduce_axcut_equation_4.
    inversion H0; subst.
    eapply c_trans. apply c_cut_comm. eapply c_trans. apply c_cong_cut. apply c_cut_comm. apply c_refl.
    eapply c_trans. apply c_cut_assoc; eauto.
    {
      assert (~ 2 ∈ P0). { intro Hfv. apply H1. apply fv_ctx_cons_r1. auto. }
      intro Hfv.
      unfold down in Hfv. apply n_fv_down_Sn in Hfv; try lia.
      replace 2 with (swap01 2) in Hfv by auto.
      apply fv_under_renaming in Hfv.
      congruence.
      apply swap01_is_bijective.
    }
    eapply c_trans. apply c_cut_comm.
    apply c_cong_cut.
    - eapply c_trans. apply c_cut_comm.
      eapply c_trans.
      * replace swap01 with (up_ren_n 0 swap01) at 5 by auto.
        rewrite up_ren_swap_over_reduce_axcut.
        ** apply IHn.
           -- repeat rewrite <- rename_axcut_ctx_preserves_length.
              inversion H; auto.
           -- replace 0 with
                ((up_ren_n 1 swap01) (swap01 1)) by auto.
              apply well_formedness_preserved_under_swap01.
              replace swap01 with (up_ren_n 0 swap01) by auto.
              apply well_formedness_preserved_under_swap01.
              assumption.
           -- replace 1 with
                ((up_ren_n 1 swap01) (swap01 2)) at 1 by auto.
              apply nfv_ctx_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              apply nfv_ctx_under_renaming.
              apply swap01_is_bijective.
              intro Hfv. apply H1. apply fv_ctx_cons_r2. auto.
           -- repeat rewrite <- rename_axcut_ctx_preserves_length.
              replace (length_axcut_ctx E + 1) with (S (length_axcut_ctx E)) by lia.
              assert (
                length_axcut_ctx E =
                  (up_ren_n (S (length_axcut_ctx E)) swap01)
                  (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
              ).
              {
                rewrite up_ren_n_swap_Sn.
                rewrite up_ren_n_swap_not_nSn; lia.
              }
              rewrite H4 at 1.
              apply nfv_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              apply nfv_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              assumption.
           -- repeat rewrite <- rename_axcut_ctx_preserves_length.
              replace (length_axcut_ctx E + 1) with (S (length_axcut_ctx E)) by lia.
              assert (
                S (length_axcut_ctx E) =
                  (up_ren_n (S (length_axcut_ctx E)) swap01)
                  (up_ren_n (length_axcut_ctx E) swap01 (S (S (length_axcut_ctx E))))
              ).
              {
                rewrite (up_ren_n_swap_not_nSn _ (S (S (length_axcut_ctx E)))); try lia.
                rewrite up_ren_n_swap_Sn; auto.
              }
              rewrite H4 at 1.
              apply nfv_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              apply nfv_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              assumption.
        ** replace swap01 with (up_ren_n 0 swap01) by auto.
           replace 0 with (up_ren_n 0 swap01 1) at 1 by auto.
           apply well_formedness_preserved_under_swap01; assumption.
        ** rewrite <- rename_axcut_ctx_preserves_length.
           replace (length_axcut_ctx E)
              with (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
               at 1 by (rewrite up_ren_n_swap_Sn; auto).
           apply nfv_under_renaming.
           apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
           simpl in H2. assumption.
      * apply c_refl_inversion_eq.
        f_equal.
        ** repeat rewrite <- rename_axcut_ctx_preserves_length.
           unfold downE. replace swap01 with (up_ren_n 0 swap01) at 3 by auto.
           rewrite up_ren_n_swap_down_down_Sn_ctx.
           {
            rewrite up_ren_n_swap_down_down_Sn_ctx.
            + replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
              rewrite up_ren_n_swap_down_down_Sn_ctx.
              - rewrite down_at_k_rename_id_after_k_commute_ctx; auto.
                apply swap01_is_bijective. intros [|[|]] ?; auto; exfalso; lia.
              - intro Hfv; apply H1; apply fv_ctx_cons_r2; auto.
            + replace 2 with (swap01 2) by auto. apply nfv_ctx_under_renaming.
              apply swap01_is_bijective. intros Hfv. apply H1. apply fv_ctx_cons_r2. auto.
           }
           {
            replace 1 with (up_ren_n 1 swap01 2) at 1 by auto.
            apply nfv_ctx_under_renaming.
            apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
            intro  Hfv. apply H1. apply fv_ctx_cons_r2; auto.
            replace 2 with (swap01 2) in Hfv by auto.
            apply fv_ctx_under_renaming in Hfv; auto. apply swap01_is_bijective.
           }
        ** repeat rewrite <- rename_axcut_ctx_preserves_length.
           replace (length_axcut_ctx E + 1) with (S (length_axcut_ctx E)) by lia.
           rewrite (proj1 (proj2 up_ren_n_swap_down_down_Sn)).
           -- rewrite (proj1 (proj2 up_ren_n_swap_down_down_Sn)).
              ++ rewrite down_ctx_preserves_length.
                 rewrite <- rename_axcut_ctx_preserves_length.
                 replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
                    with (up_ren_n (S (length_axcut_ctx E)) swap01) by auto.
                 rewrite (proj1 (proj2 up_ren_n_swap_down_down_Sn)); auto.
                 rewrite (proj1 (proj2  down_at_k_rename_id_after_k_commute)); auto.
                 apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
                 intros. rewrite up_ren_n_swap_not_nSn; try lia.
              ++ replace (S (S (length_axcut_ctx E)))
                    with (up_ren_n (length_axcut_ctx E) swap01 (S (S (length_axcut_ctx E))))
                      by (rewrite up_ren_n_swap_not_nSn; lia).
                 apply nfv_under_renaming.
                 apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
                 assumption.
           -- replace (S (length_axcut_ctx E))
                 with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (S (length_axcut_ctx E))))
                   at 1 by (rewrite up_ren_n_swap_Sn; auto).
              apply nfv_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              replace (S (S (length_axcut_ctx E)))
                 with (up_ren_n (length_axcut_ctx E) swap01 (S (S (length_axcut_ctx E))))
                   by (rewrite up_ren_n_swap_not_nSn; lia).
              apply nfv_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              assumption.
        ** simpl. f_equal.
           -- unfold up. replace swap01 with (up_ren_n 0 swap01) by auto.
              repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
              rewrite (proj1 shift_additive); simpl.
              rewrite (proj1 lift_k_lift_Sj_lt_commute); try lia.
              rewrite (proj1 shift_additive); auto.
           -- unfold up.
              replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
              repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
              rewrite (proj1 lift_at_k_rename_id_after_k_commute); auto.
              apply swap01_is_bijective. intros [|[|]] ?; auto; exfalso; lia.
    - apply c_refl_inversion_eq. f_equal. f_equal.
      assert (~ 2 ∈ P0).
      { intro Hfv. apply H1. apply fv_ctx_cons_r1. assumption. }
      assert (
        rename_process P0 (up_ren swap01) = P0
      ).
      {
        rewrite (proj1 renaming_idempotent_free_vars); auto.
        intros [|[|[|]]] ?; auto; try congruence.
      }
      rewrite H5.
      replace swap01 with (up_ren_n 0 swap01) by auto; unfold down.
      rewrite (proj1 up_ren_n_swap_down_down_Sn); auto.
Qed.

Lemma permute_cut_assoc_reduce_axcut :
  forall P E M Q,
    well_formed_axcut_ctx 0 E ->
    ~ (occurs_free_ctx 1 E) ->
    ~ occurs_free_message (length_axcut_ctx E) M ->
    ~ occurs_free_message (S (length_axcut_ctx E)) M ->
    (cut P (reduce_axcut E M Q)) ≡
    (reduce_axcut
      (downE (rename_axcut_ctx E swap01))
      (down1_message (rename_message M (up_ren_n (length_axcut_ctx E) swap01)) (length_axcut_ctx E))
      (cut (rename_process (up P) swap01) (rename_process Q swap01))
    ).
Proof.
  intros. eapply permute_cut_assoc_reduce_axcut'; eauto.
Qed.

Lemma nfv_under_substitution_extensional :
  (forall P σ i,
    (forall n, n ∈ P -> ~ (occurs_free_message i (σ n)))
    -> ~ (i ∈ (subst_process P σ))) /\
  (forall M σ i,
    (forall n, occurs_free_message n M -> ~ (occurs_free_message i (σ n)))
    -> ~ (occurs_free_message i (subst_message M σ))) /\
  (forall s σ i,
    (forall n, occurs_free_statement n s -> ~ (occurs_free_message i (σ n)))
    -> ~ (occurs_free_statement i (subst_statement s σ))).
Proof.
  apply syntax_ind; intros; simpl.
  + intro Hfv; inversion Hfv; subst.
    - eapply (H σ i); eauto; intros.
      apply H1. free_var_econstructor; eauto.
    - eapply (H0 σ i); eauto; intros.
      apply H1. free_var_econstructor; eauto.
  + intro Hfv; inversion Hfv; subst.
    - eapply (H (up_subst σ) (S i)); eauto; intros; destruct n; simpl.
      intro. inversion H3.
      intro. apply fv_up_Sn2' in H3; try lia.
      apply (H1 n); auto. free_var_econstructor; eauto.
    - eapply (H0 (up_subst σ) (S i)); eauto; intros; destruct n; simpl.
      intro. inversion H3.
      intro. apply fv_up_Sn2' in H3; try lia.
      apply (H1 n); auto. free_var_econstructor; eauto.
  + intro Hfv; inversion Hfv; subst.
    - eapply (H (up_subst σ) (S i)); eauto; intros; destruct n; simpl.
      intro. inversion H3.
      intro. apply fv_up_Sn2' in H3; try lia.
      apply (H1 n); auto. free_var_econstructor; eauto.
    - eapply (H0 σ i); eauto; intros.
      apply H1. free_var_econstructor; eauto.
  + intro. inversion H0.
  + apply H. econstructor.
  + intro Hfv; inversion Hfv; subst.
    eapply (H σ i); eauto; intros. apply H0. free_var_econstructor; eauto.
  + intro Hfv; inversion Hfv; subst.
    eapply (H (up_subst σ) (S i)); eauto; intros; destruct n; simpl.
    intro. inversion H2.
    intro. apply fv_up_Sn2' in H2; try lia.
    apply (H0 n); auto. free_var_econstructor; eauto.
  + intro Hfv; inversion Hfv; subst.
    eapply (H (up_subst σ) (S i)); eauto; intros; destruct n; simpl.
    intro. inversion H2.
    intro. apply fv_up_Sn2' in H2; try lia.
    apply (H0 n); auto. free_var_econstructor; eauto.
  + intro Hfv; inversion Hfv; subst.
    - eapply (H (up_subst σ) (S i)); eauto; intros; destruct n; simpl.
      intro. inversion H3.
      intro. apply fv_up_Sn2' in H3; try lia.
      apply (H1 n); auto. free_var_econstructor; eauto.
    - eapply (H0 (up_subst σ) (S i)); eauto; intros; destruct n; simpl.
      intro. inversion H3.
      intro. apply fv_up_Sn2' in H3; try lia.
      apply (H1 n); auto. free_var_econstructor; eauto.
  + intro Hfv; inversion Hfv; subst.
    - eapply (H (up_subst σ) (S i)); eauto; intros; destruct n; simpl.
      intro. inversion H3.
      intro. apply fv_up_Sn2' in H3; try lia.
      apply (H1 n); auto. free_var_econstructor; eauto.
    - eapply (H0 (up_subst σ) (S i)); eauto; intros; destruct n; simpl.
      intro. inversion H3.
      intro. apply fv_up_Sn2' in H3; try lia.
      apply (H1 n); auto. free_var_econstructor; eauto.
  + intro Hfv; inversion Hfv; subst.
    eapply (H (up_subst (up_subst σ)) (S (S i))); eauto; intros; destruct n; simpl.
    intro. inversion H2.
    intro. apply fv_up_Sn2' in H2; try lia. destruct n; simpl.
    inversion H2. apply fv_up_Sn2' in H2; try lia.
    apply (H0 n); auto. free_var_econstructor; eauto.
  + intro. inversion H0.
  + intro Hfv; inversion Hfv; subst.
    eapply (H σ i); eauto; intros. apply H0. free_var_econstructor; eauto.
Qed.

Lemma nfv_reduce_axcut' :
  forall n E M P k,
    n = length_axcut_ctx E ->
    well_formed_axcut_ctx 0 E ->
    ~ (occurs_free_ctx (S k) E) ->
    ~ (occurs_free_message (length_axcut_ctx E) M) ->
    ~ (occurs_free_message (length_axcut_ctx E + (S k)) M) ->
    ~ ((S k) ∈ P) ->
    ~ k ∈ (reduce_axcut E M P).
Proof.
  induction n; intros; simpl; destruct E; simpl in H; try congruence.
  + rewrite reduce_axcut_equation_1.
    simpl in *.
    apply nfv_under_substitution_extensional.
    intros. destruct n0; simpl.
    - intro. apply n_fv_down_Sn' in H6; auto. lia.
    - destruct (PeanoNat.Nat.eq_dec k n0); subst; try congruence.
      intro. inversion H6; congruence.
  + rewrite reduce_axcut_equation_2.
    simpl in *.
    apply nfv_under_substitution_extensional.
    intros. destruct n0; simpl.
    - intro. apply n_fv_down_Sn' in H6; auto. lia.
    - destruct (PeanoNat.Nat.eq_dec k n0); subst; try congruence.
      intro. inversion H6; congruence.
  + rewrite reduce_axcut_equation_3.
    intro. inversion H5; subst.
    - inversion H0; subst.
      apply (proj1 n_fv_down_Sn) in H8; try lia.
      replace (S (S k)) with (swap01 (S (S k))) in H8 by auto.
      apply fv_under_renaming in H8; try apply swap01_is_bijective.
      apply H1. apply fv_ctx_cons_l1. assumption.
    - assert (
        ~ S k ∈ reduce_axcut
                  (rename_axcut_ctx E swap01)
                  (rename_message M (up_ren_n (length_axcut_ctx E) swap01))
                  (rename_process (up P) swap01)
      ).
      {
        eapply IHn; eauto.
        + rewrite <- rename_axcut_ctx_preserves_length. inversion H; auto.
        + replace 0 with (swap01 1) by auto; replace swap01 with (up_ren_n 0 swap01) by auto.
          apply well_formedness_preserved_under_swap01.
          inversion H0; auto.
        + replace (S (S k)) with (swap01 (S (S k))) by auto.
          apply nfv_ctx_under_renaming; try apply swap01_is_bijective.
          intro. apply H1. apply fv_ctx_cons_l2. auto.
        + rewrite <- rename_axcut_ctx_preserves_length.
          replace (length_axcut_ctx E)
             with (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
               at 1
               by (rewrite up_ren_n_swap_Sn; auto).
          apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
          simpl in H2; assumption.
        + rewrite <- rename_axcut_ctx_preserves_length.
          replace (length_axcut_ctx E + S (S k))
             with (up_ren_n (length_axcut_ctx E) swap01 (length_axcut_ctx E + S (S k)))
               by (rewrite up_ren_n_swap_not_nSn; lia).
          apply nfv_under_renaming.
          apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
          intro. apply H3; simpl.
          replace (S (length_axcut_ctx E + S k)) with (length_axcut_ctx E + S (S k)) by lia.
          assumption.
        + replace (S (S k)) with (swap01 (S (S k))) by auto.
          apply nfv_under_renaming. apply swap01_is_bijective.
          intro. apply fv_up_Sn2 in H6; try lia. congruence.
      }
      congruence.
  + rewrite reduce_axcut_equation_4.
    intro. inversion H5; subst.
    - assert (
        ~ S k ∈ reduce_axcut
                  (rename_axcut_ctx E swap01)
                  (rename_message M (up_ren_n (length_axcut_ctx E) swap01))
                  (rename_process (up P) swap01)
      ).
      {
        eapply IHn; eauto.
        + rewrite <- rename_axcut_ctx_preserves_length. inversion H; auto.
        + replace 0 with (swap01 1) by auto; replace swap01 with (up_ren_n 0 swap01) by auto.
          apply well_formedness_preserved_under_swap01.
          inversion H0; auto.
        + replace (S (S k)) with (swap01 (S (S k))) by auto.
          apply nfv_ctx_under_renaming; try apply swap01_is_bijective.
          intro. apply H1. apply fv_ctx_cons_r2. auto.
        + rewrite <- rename_axcut_ctx_preserves_length.
          replace (length_axcut_ctx E)
             with (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
               at 1
               by (rewrite up_ren_n_swap_Sn; auto).
          apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
          simpl in H2; assumption.
        + rewrite <- rename_axcut_ctx_preserves_length.
          replace (length_axcut_ctx E + S (S k))
             with (up_ren_n (length_axcut_ctx E) swap01 (length_axcut_ctx E + S (S k)))
               by (rewrite up_ren_n_swap_not_nSn; lia).
          apply nfv_under_renaming.
          apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
          intro. apply H3; simpl.
          replace (S (length_axcut_ctx E + S k)) with (length_axcut_ctx E + S (S k)) by lia.
          assumption.
        + replace (S (S k)) with (swap01 (S (S k))) by auto.
          apply nfv_under_renaming. apply swap01_is_bijective.
          intro. apply fv_up_Sn2 in H6; try lia. congruence.
      }
      congruence.
    - inversion H0; subst.
      apply (proj1 n_fv_down_Sn) in H8; try lia.
      replace (S (S k)) with (swap01 (S (S k))) in H8 by auto.
      apply fv_under_renaming in H8; try apply swap01_is_bijective.
      apply H1. apply fv_ctx_cons_r1. assumption.
Qed.

Lemma nfv_reduce_axcut :
  forall E M P k,
    well_formed_axcut_ctx 0 E ->
    ~ (occurs_free_ctx (S k) E) ->
    ~ (occurs_free_message (length_axcut_ctx E) M) ->
    ~ (occurs_free_message (length_axcut_ctx E + (S k)) M) ->
    ~ ((S k) ∈ P) ->
    ~ k ∈ (reduce_axcut E M P).
Proof.
  intros; eapply nfv_reduce_axcut'; eauto.
Qed.

Lemma reduce_axcut_invariant_under_directed_cong' :
  forall n k Γ E M R Q P P',
    k <= n ->
    k = length_axcut_ctx E ->
    Q = fill_hole E M ->
    Γ ⊢ Q :# -> well_formed_axcut_ctx 0 E ->
    P ⇛ P' -> Q ⇛ R ->
      exists E' M',
        R = fill_hole E' M' /\
        E #⇛ E' /\
        (reduce_axcut E M P) ⇛ (reduce_axcut E' M' P').
Proof.
  induction n; intros; destruct E; simpl in H; try congruence; try (subst; simpl in *; exfalso; lia).
  + subst. simpl in H5. inversion H5; subst.
    - exists (nil_l n), mr2; repeat split.
      * simpl.
        apply directed_cong_in_struct_cong in H6.
        apply future_equiv_future1 in H6. rewrite H6; auto.
      * econstructor.
      * repeat rewrite reduce_axcut_equation_1.
        apply directed_cong_invariant_under_substitution; auto.
        intros [|]; simpl; try apply dc_cong_reflM.
        apply directed_cong_invariant_under_downshifting; auto.
        pose proof (nfv_well_typed_fill_hole _ _ _ _ H3 H2).
        assumption.
    - exists (nil_r n), mr2. repeat split.
      * simpl.
        apply directed_cong_in_struct_cong in H6.
        apply future_equiv_future1 in H6. rewrite H6; auto.
      * econstructor.
      * repeat rewrite reduce_axcut_equation_2.
        repeat rewrite reduce_axcut_equation_1.
        apply directed_cong_invariant_under_substitution; auto.
        intros [|]; simpl; try apply dc_cong_reflM.
        apply directed_cong_invariant_under_downshifting; auto.
        pose proof (nfv_well_typed_fill_hole _ _ _ _ H3 H2).
        assumption.
  + subst. simpl in H5. inversion H5; subst.
    - exists (nil_r n), ml2; repeat split.
      * simpl.
        apply directed_cong_in_struct_cong in H8.
        apply future_equiv_future1 in H8. rewrite H8; auto.
      * econstructor.
      * repeat rewrite reduce_axcut_equation_2.
        apply directed_cong_invariant_under_substitution; auto.
        intros [|]; simpl; try apply dc_cong_reflM.
        apply directed_cong_invariant_under_downshifting; auto.
        pose proof (nfv_well_typed_fill_hole _ _ _ _ H3 H2).
        assumption.
    - exists (nil_l n), ml2. repeat split.
      * simpl.
        apply directed_cong_in_struct_cong in H8.
        apply future_equiv_future1 in H8. rewrite H8; auto.
      * econstructor.
      * repeat rewrite reduce_axcut_equation_2.
        repeat rewrite reduce_axcut_equation_1.
        apply directed_cong_invariant_under_substitution; auto.
        intros [|]; simpl; try apply dc_cong_reflM.
        apply directed_cong_invariant_under_downshifting; auto.
        pose proof (nfv_well_typed_fill_hole _ _ _ _ H3 H2).
        assumption.
  + subst. simpl in H5. inversion H5; subst.
    - exists (nil_l n0), mr2; repeat split.
      * simpl.
        apply directed_cong_in_struct_cong in H6.
        apply future_equiv_future1 in H6. rewrite H6; auto.
      * econstructor.
      * repeat rewrite reduce_axcut_equation_1.
        apply directed_cong_invariant_under_substitution; auto.
        intros [|]; simpl; try apply dc_cong_reflM.
        apply directed_cong_invariant_under_downshifting; auto.
        pose proof (nfv_well_typed_fill_hole _ _ _ _ H3 H2).
        assumption.
    - exists (nil_r n0), mr2. repeat split.
      * simpl.
        apply directed_cong_in_struct_cong in H6.
        apply future_equiv_future1 in H6. rewrite H6; auto.
      * econstructor.
      * repeat rewrite reduce_axcut_equation_2.
        repeat rewrite reduce_axcut_equation_1.
        apply directed_cong_invariant_under_substitution; auto.
        intros [|]; simpl; try apply dc_cong_reflM.
        apply directed_cong_invariant_under_downshifting; auto.
        pose proof (nfv_well_typed_fill_hole _ _ _ _ H3 H2).
        assumption.
  + subst. simpl in H5. inversion H5; subst.
    - exists (nil_r n0), ml2; repeat split.
      * simpl.
        apply directed_cong_in_struct_cong in H8.
        apply future_equiv_future1 in H8. rewrite H8; auto.
      * econstructor.
      * repeat rewrite reduce_axcut_equation_2.
        apply directed_cong_invariant_under_substitution; auto.
        intros [|]; simpl; try apply dc_cong_reflM.
        apply directed_cong_invariant_under_downshifting; auto.
        pose proof (nfv_well_typed_fill_hole _ _ _ _ H3 H2).
        assumption.
    - exists (nil_l n0), ml2. repeat split.
      * simpl.
        apply directed_cong_in_struct_cong in H8.
        apply future_equiv_future1 in H8. rewrite H8; auto.
      * econstructor.
      * repeat rewrite reduce_axcut_equation_2.
        repeat rewrite reduce_axcut_equation_1.
        apply directed_cong_invariant_under_substitution; auto.
        intros [|]; simpl; try apply dc_cong_reflM.
        apply directed_cong_invariant_under_downshifting; auto.
        pose proof (nfv_well_typed_fill_hole _ _ _ _ H3 H2).
        assumption.
  + subst. simpl in H; simpl in H5. inversion H5; subst.
    - assert (
        (rename_process (fill_hole E M) swap01) ⇛
          (rename_process Q' swap01)
      ). { apply directed_cong_invariant_under_renaming; auto; apply swap01_is_bijective. }
      rewrite rename_axcut_ctx_over_fill_hole in H0; try apply swap01_is_bijective.
      assert (
        n >= length_axcut_ctx (rename_axcut_ctx E swap01)
      ). { rewrite <- rename_axcut_ctx_preserves_length; inversion H; lia. }
      assert (
        exists Γ',
          Γ' ⊢ (fill_hole (rename_axcut_ctx E swap01)
                          (rename_message M (up_ren_n (length_axcut_ctx E) swap01))) :#
      ) as Hwtfh.
      {
        simpl in H2; inversion H2; subst.
        destruct (swap01_preserves_well_typedness _ _ H13).
        eexists. rewrite rename_axcut_ctx_over_fill_hole in H7. eassumption.
        apply swap01_is_bijective.
      }
      destruct Hwtfh.
      assert (
        well_formed_axcut_ctx 0 (rename_axcut_ctx E swap01)
      ).
      {
        replace 0 with (swap01 1) by auto.
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; auto.
        inversion H3; auto.
      }
      assert (
        (rename_process (up P) swap01) ⇛
          (rename_process (up P') swap01)
      ).
      {
        apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
        apply directed_cong_invariant_under_upshifting; auto.
      }
      destruct (IHn _ _ _ _ _ _ _ _
                      H1
                      eq_refl
                      eq_refl
                      H7
                      H9
                      H10
                      H0) as [E'' [M'' [? [? ?]]]].
      exists (cons_r (rename_axcut_ctx E'' swap01) P'0).
      exists (rename_message M'' (up_ren_n (length_axcut_ctx E'') swap01)).
      repeat split.
      * simpl. f_equal.
        assert (
          rename_process (rename_process Q' swap01) swap01
            = rename_process (fill_hole E'' M'') swap01
        ). { f_equal; auto. }
        rewrite swap_swap_id in H14. rewrite H14.
        rewrite <- rename_axcut_ctx_over_fill_hole; auto.
        apply swap01_is_bijective.
      * econstructor; eauto.
        apply (edc_invariant_under_renaming _ _ swap01 swap01_is_bijective) in H12.
        rewrite swap_swap_idE in H12. auto.
      * repeat rewrite reduce_axcut_equation_3.
        repeat rewrite reduce_axcut_equation_4.
        apply dc_cut_comm.
        ** apply directed_cong_invariant_under_downshifting; auto.
           -- apply directed_cong_invariant_under_renaming; auto.
              apply swap01_is_bijective.
           -- inversion H3; subst.
              apply nfv_01_swap; auto.
        ** rewrite swap_swap_idE.
           rewrite <- rename_axcut_ctx_preserves_length.
           rewrite up_ren_swap_swap_idM.
           assumption.
    - assert (
        (rename_process (fill_hole E M) swap01) ⇛
          (rename_process R1 swap01)
      ). { apply directed_cong_invariant_under_renaming; auto; apply swap01_is_bijective. }
      rewrite rename_axcut_ctx_over_fill_hole in H0; try apply swap01_is_bijective.
      assert (
        n >= length_axcut_ctx (rename_axcut_ctx E swap01)
      ). { rewrite <- rename_axcut_ctx_preserves_length; inversion H; lia. }
      assert (
        exists Γ',
          Γ' ⊢ (fill_hole (rename_axcut_ctx E swap01)
                          (rename_message M (up_ren_n (length_axcut_ctx E) swap01))) :#
      ) as Hwtfh.
      {
        simpl in H2; inversion H2; subst.
        destruct (swap01_preserves_well_typedness _ _ H15).
        rewrite rename_axcut_ctx_over_fill_hole in H10.
        eexists; eauto.
        apply swap01_is_bijective.
      }
      destruct Hwtfh as [Γ' ?].
      assert (
        well_formed_axcut_ctx 0 (rename_axcut_ctx E swap01)
      ).
      {
        replace 0 with (swap01 1) by auto.
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01.
        inversion H3; auto.
      }
      assert (
        (rename_process (up P) swap01) ⇛
          (rename_process (up P') swap01)
      ).
      {
        apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
        apply directed_cong_invariant_under_upshifting; auto.
      }
      destruct (IHn _ _ _ _ _ _ _ _
                    H1
                    eq_refl
                    eq_refl
                    H10
                    H11
                    H12
                    H0) as [E'' [M'' [? [? ?]]]].
      exists (
        cons_l (down (rename_process P2 swap01))
               (cons_l (rename_process Q1 swap01)
                       (rename_axcut_ctx (upE (rename_axcut_ctx E'' swap01)) swap01))
      ).
      exists (
        rename_message
          (lift_message (rename_message M'' (up_ren_n (length_axcut_ctx E'') swap01))
            (length_axcut_ctx (rename_axcut_ctx E'' swap01)) 1)
          (up_ren_n (length_axcut_ctx (upE (rename_axcut_ctx E'' swap01))) swap01)
      ).
      repeat split.
      * simpl. f_equal. f_equal.
        rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
        replace (length_axcut_ctx (rename_axcut_ctx E'' swap01)) with (length_axcut_ctx (rename_axcut_ctx E'' swap01) + 0) by lia.
        unfold upE. rewrite <- up_ctx_over_fill_hole.
        rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
        f_equal. unfold up. f_equal.
        rewrite <- H13.
        rewrite swap_swap_id.
        reflexivity.
      * eapply edc_assoc_cut_l; eauto.
        apply (edc_invariant_under_renaming _ _ swap01 swap01_is_bijective) in H14.
        rewrite swap_swap_idE in H14.
        assumption.
      * repeat rewrite reduce_axcut_equation_3; simpl.
        repeat rewrite reduce_axcut_equation_3; simpl.
        eapply dc_cut_assoc_l.
        ** intro.
           apply n_fv_down_Sn' in H16; auto.
           -- apply ((proj1 nfv_under_renaming) _ (up_ren swap01)) in H6.
              simpl in H6; congruence.
              apply shift_preserves_bijection; apply swap01_is_bijective.
           -- replace 1 with (up_ren swap01 2) by auto.
              apply nfv_under_renaming.
              apply shift_preserves_bijection; apply swap01_is_bijective.
              inversion H3; subst.
              intro; apply H21; free_var_econstructor; eauto.
        ** replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
           assert (~ 2 ∈ P1).
           { inversion H3; subst. intro. apply H19; free_var_econstructor; eauto. }
           rewrite (proj1 up_ren_n_swap_down_down_Sn); eauto.
           apply directed_cong_invariant_under_downshifting; eauto.
        ** replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
           assert (~ 2 ∈ Q).
           { inversion H3; subst. intro. apply H19; apply fv_cut_r; eauto. }
           rewrite (proj1 up_ren_n_swap_down_down_Sn); eauto.
           apply directed_cong_invariant_under_downshifting; eauto.
        ** apply H15.
        ** unfold down.
           assert (
            ~ 1 ∈ P2
           ). { apply directed_cong_in_struct_cong in H7. eapply nfv_under_struct_cong; eauto. }
           replace swap01 with (up_ren_n 0 swap01) by auto.
           repeat rewrite (proj1 up_ren_n_swap_down_down_Sn); eauto.
           -- rewrite (proj1 down_k_down_Sj_lt_commute2); auto.
           -- apply nfv_down_lt; auto.
           -- intro. apply n_fv_down_Sn' in H17; auto.
              assert (~ 2 ∈ P1). { intro. inversion H3; subst. apply H22; free_var_econstructor; eauto. }
              apply directed_cong_in_struct_cong in H7.
              eapply nfv_under_struct_cong in H18; eauto.
        ** unfold down.
           replace swap01 with (up_ren_n 0 swap01) by auto.
           assert (
            ~ 2 ∈ Q1
           ).
           {
            intro. inversion H3; subst. apply H20; apply fv_cut_r.
            eapply free_vars_under_struct_cong; eauto.
            apply directed_cong_in_struct_cong; eauto.
           }
           rewrite (proj1 up_ren_n_swap_down_down_Sn).
           -- simpl. replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
              rewrite (proj1 up_ren_n_swap_down_down_Sn).
              ++ rewrite (proj1 down_at_k_rename_id_after_k_commute); auto.
                 apply swap01_is_bijective. intros [|[|]] ?; auto; exfalso; lia.
              ++ replace 2 with (swap01 2) by auto. apply nfv_under_renaming; auto.
                 apply swap01_is_bijective.
           -- simpl.
              replace 1 with (up_ren swap01 2) by auto.
              apply nfv_under_renaming. apply shift_preserves_bijection; apply swap01_is_bijective.
              replace 2 with (swap01 2) by auto.
              apply nfv_under_renaming; auto. apply swap01_is_bijective.
        ** repeat rewrite <- rename_axcut_ctx_preserves_length.
           repeat rewrite lift_ctx_preserves_length.
           unfold up.
           assert (
            ~ occurs_free_message (length_axcut_ctx E'') M''
           ).
           {
            replace (length_axcut_ctx E'') with (length_axcut_ctx E'' + 0) by lia.
            assert (
              exists Γ', Γ' ⊢ (fill_hole E'' M'') :#
            ).
            {
              simpl in H2; inversion H2; subst.
              apply (directed_cong_preserves_typing _ _ _ H21) in H9.
              destruct (swap01_preserves_well_typedness _ _ H9).
              rewrite H13 in H16. eexists; eauto.
            }
            destruct H16.
            eapply nfv_well_typed_fill_hole; eauto.
            eapply edc_preserves_well_formedness; eauto.
           }
           rewrite lift_over_reduce_axcut.
           -- replace swap01 with (up_ren_n 0 swap01) by auto.
              rewrite up_ren_swap_over_reduce_axcut; simpl.
              ++ f_equal.
                 {
                  unfold upE.
                  replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
                  repeat rewrite up_ren_n_swap_lift_lift_Sn_ctx.
                  rewrite lift_ctx_at_k_rename_ctx_id_after_k_commute.
                  + rewrite swap_swap_idE; auto.
                  + apply swap01_is_bijective.
                  + intros [|[|]] ?; auto; exfalso; lia.
                 }
                 {
                  unfold upE.
                  repeat rewrite lift_ctx_preserves_length.
                  repeat rewrite <- rename_axcut_ctx_preserves_length.
                  repeat rewrite (proj1 (proj2 up_ren_n_swap_lift_lift_Sn)).
                  rewrite (proj1 (proj2 lift_at_k_rename_id_after_k_commute)).
                  + rewrite up_ren_swap_swap_idM. f_equal; lia.
                  + apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
                  + intros. rewrite up_ren_n_swap_not_nSn; auto; lia.
                 }
                 {
                  replace swap01 with (up_ren_n 0 swap01) at 1 by auto.
                  repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
                  rewrite ((proj1 lift_k_lift_Sj_lt_commute) _ 1 1).
                  auto. lia.
                 }
              ++ apply upE_preserves_well_formedness2. lia.
                 eapply edc_preserves_well_formedness; eauto.
              ++ rewrite lift_ctx_preserves_length.
                 apply (proj1 (proj2 nfv_up_lt)); eauto; lia.
           -- eapply edc_preserves_well_formedness; eauto.
           -- assumption.
    - destruct E; simpl in H1; try congruence; inversion H1; subst; simpl in H.
      {
        assert (
        (rename_process (rename_process (fill_hole E M) (up_ren swap01)) swap01) ⇛
          (rename_process (rename_process R1 (up_ren swap01)) swap01)
        ). { repeat  apply directed_cong_invariant_under_renaming; auto; try apply shift_preserves_bijection; apply swap01_is_bijective. }
        rewrite rename_axcut_ctx_over_fill_hole in H0;
        try apply shift_preserves_bijection; try apply swap01_is_bijective.
        rewrite rename_axcut_ctx_over_fill_hole in H0; try apply swap01_is_bijective.
        assert (
          n >= length_axcut_ctx (rename_axcut_ctx (rename_axcut_ctx E (up_ren swap01)) swap01)
        ). { repeat rewrite <- rename_axcut_ctx_preserves_length. inversion H; lia. }
        assert (
          exists Γ',
            Γ' ⊢
              (fill_hole (rename_axcut_ctx (rename_axcut_ctx E (up_ren swap01)) swap01)
                         (rename_message
                          (rename_message M (up_ren_n (length_axcut_ctx E) (up_ren swap01)))
                          (up_ren_n (length_axcut_ctx (rename_axcut_ctx E (up_ren swap01))) swap01))) :#
        ).
        {
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply shift_preserves_bijection; try apply swap01_is_bijective.
          simpl in H2; inversion H2; subst. inversion H16; subst.
          destruct (up_ren_swap01_preserves_well_typedness _ _ H19).
          destruct (swap01_preserves_well_typedness _ _ H11).
          eauto.
        }
        destruct H11 as [Γ' HΓ'].
        assert (
          well_formed_axcut_ctx 0 (rename_axcut_ctx (rename_axcut_ctx E (up_ren swap01)) swap01)
        ).
        {
          replace 0 with (swap01 (up_ren swap01 2)) by auto.
          replace swap01 with (up_ren_n 0 swap01) by auto.
          apply well_formedness_preserved_under_swap01; simpl.
          replace 1 with (up_ren swap01 2) by auto.
          replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
          apply well_formedness_preserved_under_swap01; simpl.
          inversion H3; subst. inversion H15; auto.
        }
        assert (
          (rename_process (up (rename_process (up P) swap01)) swap01) ⇛
            (rename_process (up (rename_process (up P') swap01)) swap01)
        ).
        {
          repeat (apply directed_cong_invariant_under_renaming || apply directed_cong_invariant_under_upshifting); auto;
          apply swap01_is_bijective.
        }
        destruct (IHn _ _ _ _ _ _ _ _
                      H10
                      eq_refl
                      eq_refl
                      HΓ'
                      H11
                      H12
                      H0) as [E'' [M'' [? [? ?]]]].
        pose (rename_axcut_ctx (rename_axcut_ctx E'' swap01) (up_ren swap01)) as E'''.
        pose (
          rename_message
            (rename_message M'' (up_ren_n (length_axcut_ctx E'') swap01))
            (up_ren_n (length_axcut_ctx (rename_axcut_ctx E'' swap01)) (up_ren swap01))
        ) as M'''.
        exists (
          cons_l (cut (rename_process (up P2) swap01)
                      (rename_process Q1 swap01))
                 (downE (rename_axcut_ctx E''' swap01))
        ).
        exists (
          down1_message
            (rename_message M''' (up_ren_n (length_axcut_ctx E''') swap01))
            (length_axcut_ctx (rename_axcut_ctx E''' swap01) + 0)
        ).
        repeat split.
        + simpl. f_equal.
          unfold downE. rewrite <- down_ctx_over_fill_hole.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
          subst E''' M'''.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply shift_preserves_bijection; try apply swap01_is_bijective.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
          rewrite <- H13. unfold down.
          rewrite swap_swap_id.
          replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
          rewrite up_ren_swap_swap_idP.
          reflexivity.
        + eapply edc_assoc_ll; eauto.
          - subst E'''.
            apply (edc_invariant_under_renaming _ _ swap01 swap01_is_bijective) in H14.
            rewrite swap_swap_idE in H14.
            apply (edc_invariant_under_renaming _ _ (up_ren swap01)) in H14;
            try apply shift_preserves_bijection; try apply swap01_is_bijective.
            replace (up_ren swap01) with (up_ren_n 1 swap01) in H14 by auto.
            rewrite up_ren_swap_swap_idE in H14.
            assumption.
          - apply (proj1 (nfv_fill_hole _ _ _ H6)).
        + repeat rewrite reduce_axcut_equation_3; simpl.
          repeat rewrite reduce_axcut_equation_3; simpl.
          eapply dc_cut_assoc_r.
          - eapply nfv_reduce_axcut.
            * replace 0 with (swap01 1) by auto.
              replace swap01 with (up_ren_n 0 swap01) by auto.
              apply well_formedness_preserved_under_swap01; simpl.
              replace 1 with (up_ren swap01 2) by auto.
              replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
              apply well_formedness_preserved_under_swap01.
              inversion H3; subst. inversion H20; auto.
            * replace 2 with (swap01 2) by auto.
              apply nfv_ctx_under_renaming; try apply swap01_is_bijective.
              replace 2 with (up_ren swap01 1) by auto.
              apply nfv_ctx_under_renaming. apply shift_preserves_bijection; apply swap01_is_bijective.
              apply (proj1 (nfv_fill_hole _ _ _ H6)).
            * repeat rewrite <- rename_axcut_ctx_preserves_length.
              replace (length_axcut_ctx E)
                 with (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
                   at 1
                   by (rewrite up_ren_n_swap_Sn; auto).
              apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
                 with (up_ren_n (S (length_axcut_ctx E)) swap01) by auto.
              replace (S (length_axcut_ctx E))
                 with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (S (length_axcut_ctx E))))
                   at 1
                   by (rewrite up_ren_n_swap_Sn; auto).
              apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              replace (S (S (length_axcut_ctx E))) with (length_axcut_ctx E + 2) by lia.
              simpl in H2; inversion H2; subst. inversion H21; subst.
              inversion H3; subst. inversion H26; subst.
              apply (nfv_well_typed_fill_hole _ _ _ _ H28 H24).
            * repeat rewrite <- rename_axcut_ctx_preserves_length.
              replace (length_axcut_ctx E + 2) with (S (S (length_axcut_ctx E))) by lia.
              replace (S (S (length_axcut_ctx E)))
                 with (up_ren_n (length_axcut_ctx E) swap01 (S (S (length_axcut_ctx E))))
                   by (rewrite up_ren_n_swap_not_nSn; lia).
              apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
                 with (up_ren_n (S (length_axcut_ctx E)) swap01)
                  by auto.
              replace (S (S (length_axcut_ctx E)))
                 with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (length_axcut_ctx E)))
                   by (rewrite up_ren_n_swap_n; auto).
              apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              replace (S (length_axcut_ctx E)) with (length_axcut_ctx E + 1) by lia.
              apply (proj2 (nfv_fill_hole _ _ _ H6)).
            * unfold up. repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
              rewrite (proj1 shift_additive). apply nfv_lift_n; lia.
          - eapply directed_cong_invariant_under_downshifting.
            eapply directed_cong_invariant_under_renaming; eauto; try apply swap01_is_bijective.
            apply nfv_01_swap. inversion H3; auto.
          - eapply directed_cong_invariant_under_downshifting.
            eapply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
            eapply directed_cong_invariant_under_renaming; eauto; try apply shift_preserves_bijection; try apply swap01_is_bijective.
            replace 0 with (swap01 (up_ren swap01 2)) by auto.
            apply nfv_under_renaming; try apply swap01_is_bijective.
            apply nfv_under_renaming; try apply shift_preserves_bijection; try apply swap01_is_bijective.
            inversion H3; subst. inversion H20; subst. auto.
          - replace (up_ren (up_ren_n (length_axcut_ctx E) swap01)) with
                    (up_ren_n (length_axcut_ctx E) (up_ren swap01)).
            eapply H15.
            replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
            rewrite up_ren_n_additive.
            replace (length_axcut_ctx E + 1) with (S (length_axcut_ctx E)) by lia.
            reflexivity.
          - unfold up.
            rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
            replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
            rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
            replace swap01 with (up_ren_n 0 swap01) by auto.
            rewrite (proj1 up_ren_n_swap_down_down_Sn).
            * rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
              rewrite (proj1 lift_after_down_lt_commute_nfv); auto.
              inversion H3; subst.
              eapply nfv_under_struct_cong. eapply directed_cong_in_struct_cong; eauto.
              eauto.
            * inversion H3; subst.
              eapply nfv_under_struct_cong. eapply directed_cong_in_struct_cong; eauto.
              eauto.
          - replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
            rewrite (proj1 up_ren_n_swap_down_down_Sn).
            * replace swap01 with (up_ren_n 0 swap01) by auto.
              rewrite (proj1 up_ren_n_swap_down_down_Sn). simpl.
              replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
              rewrite (proj1 up_ren_n_swap_down_down_Sn).
              rewrite (proj1 down_at_k_rename_id_after_k_commute); auto.
              apply swap01_is_bijective. intros [|[|]] ?; auto; exfalso; lia.
              inversion H3; subst. inversion H20; subst.
              eapply nfv_under_struct_cong. apply directed_cong_in_struct_cong; eauto. eauto.
              simpl. replace 1 with (up_ren swap01 2) by auto. apply nfv_under_renaming.
              apply shift_preserves_bijection; apply swap01_is_bijective.
              inversion H3; subst. inversion H20; subst.
              eapply nfv_under_struct_cong. apply directed_cong_in_struct_cong; eauto. eauto.
            * replace 2 with (swap01 2) by auto. apply nfv_under_renaming. apply swap01_is_bijective.
              inversion H3; subst. inversion H20; subst.
              eapply nfv_under_struct_cong. apply directed_cong_in_struct_cong; eauto. eauto.
          - replace swap01 with (up_ren_n 0 swap01) by auto.
            assert (
              well_formed_axcut_ctx 0 E''
            ).
            { eapply edc_preserves_well_formedness; eauto. }
            assert (
              ~ occurs_free_message (length_axcut_ctx E'') M''
            ).
            {
              assert (
                exists Γ',
                  Γ' ⊢ fill_hole E'' M'' :#
              ).
              {
                simpl in H2; inversion H2; subst. inversion H22; subst.
                apply directed_cong_in_struct_cong in H9.
                apply ((proj1 struct_cong_preserves_typing) _ _ H9) in H25.
                rewrite <- H13.
                destruct (up_ren_swap01_preserves_well_typedness _ _ H25).
                destruct (swap01_preserves_well_typedness _ _ H17).
                eauto.
              }
              destruct H17.
              replace (length_axcut_ctx E'') with (length_axcut_ctx E'' + 0) by lia.
              eapply nfv_well_typed_fill_hole; eauto.
            }
            rewrite up_ren_swap_over_reduce_axcut; simpl; eauto.
            unfold down.
            assert ( ~ 1 ∈ R1 ).
            {
              eapply nfv_under_struct_cong. apply directed_cong_in_struct_cong; eauto. eauto.
            }
            assert ( ~ 2 ∈ rename_process (rename_process R1 (up_ren swap01)) swap01 ).
            {
              replace 2 with (swap01 (up_ren swap01 1)) by auto.
              apply nfv_under_renaming; try apply swap01_is_bijective.
              apply nfv_under_renaming; auto. apply shift_preserves_bijection; apply swap01_is_bijective.
            }
            assert ( ~ occurs_free_ctx 2 E'' ).
            {
              rewrite H13 in H19.
              apply (proj1 (nfv_fill_hole _ _ _ H19)).
            }
            rewrite down_over_reduce_axcut.
            ** f_equal.
               {
                unfold downE. subst E'''.
                replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
                rewrite up_ren_n_swap_down_down_Sn_ctx.
                + replace swap01 with (up_ren_n 0 swap01) by auto.
                  rewrite up_ren_n_swap_down_down_Sn_ctx; simpl.
                  - replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
                    rewrite up_ren_n_swap_down_down_Sn_ctx; simpl.
                    * rewrite down_at_k_rename_id_after_k_commute_ctx. rewrite swap_swap_idE; auto.
                      apply swap01_is_bijective. intros [|[|]] ?; auto; exfalso; lia.
                    * replace 2 with (swap01 2) by auto. apply nfv_ctx_under_renaming. apply swap01_is_bijective. auto.
                  - replace 1 with (up_ren swap01 (swap01 2)) by auto.
                    apply nfv_ctx_under_renaming. apply shift_preserves_bijection; apply swap01_is_bijective.
                    apply nfv_ctx_under_renaming; auto. apply swap01_is_bijective.
                + assumption.
               }
               {
                subst E'''. subst M'''.
                unfold downE. rewrite down_ctx_preserves_length.
                repeat rewrite <- rename_axcut_ctx_preserves_length.
                rewrite <- plus_n_O.
                repeat rewrite PeanoNat.Nat.add_1_r; simpl.
                replace (up_ren_n (length_axcut_ctx E'') (up_ren swap01))
                       with (up_ren_n (S (length_axcut_ctx E'')) swap01).
                repeat rewrite (proj1 (proj2 up_ren_n_swap_down_down_Sn)).
                replace (up_ren (up_ren_n (length_axcut_ctx E'') swap01))
                       with (up_ren_n (S (length_axcut_ctx E'')) swap01) by auto.
                repeat rewrite (proj1 (proj2 up_ren_n_swap_down_down_Sn)).
                rewrite (proj1 (proj2 down_at_k_rename_id_after_k_commute)).
                rewrite up_ren_swap_swap_idM; auto.
                apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
                + intros. rewrite up_ren_n_swap_not_nSn; lia.
                + replace (S (S (length_axcut_ctx E''))) with (length_axcut_ctx E'' + 2) by lia.
                  rewrite H13 in H19.
                  apply (proj2 (nfv_fill_hole _ _ _ H19)).
                + replace (S (S (length_axcut_ctx E''))) with
                          (up_ren_n (length_axcut_ctx E'') swap01 (S (S (length_axcut_ctx E'')))).
                  apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
                  replace (S (S (length_axcut_ctx E''))) with (length_axcut_ctx E'' + 2) by lia.
                  rewrite H13 in H19.
                  apply (proj2 (nfv_fill_hole _ _ _ H19)).
                  rewrite up_ren_n_swap_not_nSn; lia.
                + replace (S (length_axcut_ctx E'')) with
                          (up_ren_n (S (length_axcut_ctx E'')) swap01 (S (S (length_axcut_ctx E''))))
                          at 1 by (rewrite up_ren_n_swap_Sn; try lia; auto).
                  apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
                  replace (S (S (length_axcut_ctx E''))) with
                          (up_ren_n (length_axcut_ctx E'') swap01 (S (S (length_axcut_ctx E'')))).
                  apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
                  replace (S (S (length_axcut_ctx E''))) with (length_axcut_ctx E'' + 2) by lia.
                  rewrite H13 in H19.
                  apply (proj2 (nfv_fill_hole _ _ _ H19)).
                  rewrite up_ren_n_swap_not_nSn; lia.
                + replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
                  rewrite up_ren_n_additive. f_equal; lia.
               }
               {
                unfold up. repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
                rewrite <- (proj1 lift_after_down_lt_commute_nfv); try lia.
                rewrite (proj1 down_after_up_id); auto.
                apply nfv_lift_n; lia.
               }
            ** replace 0 with (up_ren swap01 0) by auto.
               replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
               apply well_formedness_preserved_under_swap01.
               eapply edc_preserves_well_formedness; eauto.
            ** replace 1 with (up_ren swap01 2) by auto. apply nfv_under_renaming.
               apply shift_preserves_bijection; apply swap01_is_bijective.
               unfold up. repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
               rewrite (proj1 shift_additive). apply nfv_lift_n; lia.
            ** replace 1 with (up_ren swap01 2) by auto.
               apply nfv_ctx_under_renaming; auto. apply shift_preserves_bijection; apply swap01_is_bijective.
            ** rewrite <- rename_axcut_ctx_preserves_length.
               repeat rewrite PeanoNat.Nat.add_1_r.
               replace (S (length_axcut_ctx E'')) with
                       (up_ren_n (S (length_axcut_ctx E'')) swap01 (S (S (length_axcut_ctx E''))))
                       at 1 by (rewrite up_ren_n_swap_Sn; auto).
              apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              rewrite H13 in H19.
              replace (S (S (length_axcut_ctx E''))) with (length_axcut_ctx E'' + 2) by lia.
              apply (proj2 (nfv_fill_hole _ _ _ H19)).
            ** rewrite <- rename_axcut_ctx_preserves_length.
               repeat rewrite PeanoNat.Nat.add_1_r.
               replace (length_axcut_ctx E'') with
                       (up_ren_n (S (length_axcut_ctx E'')) swap01 (length_axcut_ctx E''))
                       at 1 by (rewrite up_ren_n_swap_not_nSn; lia).
              apply nfv_under_renaming; auto. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
      }
      {
        assert (
        (rename_process (rename_process (fill_hole E M) (up_ren swap01)) swap01) ⇛
          (rename_process (rename_process Q1 (up_ren swap01)) swap01)
        ). { repeat  apply directed_cong_invariant_under_renaming; auto; try apply shift_preserves_bijection; apply swap01_is_bijective. }
        rewrite rename_axcut_ctx_over_fill_hole in H0;
        try apply shift_preserves_bijection; try apply swap01_is_bijective.
        rewrite rename_axcut_ctx_over_fill_hole in H0; try apply swap01_is_bijective.
        assert (
          n >= length_axcut_ctx (rename_axcut_ctx (rename_axcut_ctx E (up_ren swap01)) swap01)
        ). { repeat rewrite <- rename_axcut_ctx_preserves_length. inversion H; lia. }
        assert (
          exists Γ',
            Γ' ⊢
              (fill_hole (rename_axcut_ctx (rename_axcut_ctx E (up_ren swap01)) swap01)
                         (rename_message
                          (rename_message M (up_ren_n (length_axcut_ctx E) (up_ren swap01)))
                          (up_ren_n (length_axcut_ctx (rename_axcut_ctx E (up_ren swap01))) swap01))) :#
        ).
        {
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply shift_preserves_bijection; try apply swap01_is_bijective.
          simpl in H2; inversion H2; subst. inversion H16; subst.
          destruct (up_ren_swap01_preserves_well_typedness _ _ H18).
          destruct (swap01_preserves_well_typedness _ _ H11).
          eauto.
        }
        destruct H11 as [Γ' HΓ'].
        assert (
          well_formed_axcut_ctx 0 (rename_axcut_ctx (rename_axcut_ctx E (up_ren swap01)) swap01)
        ).
        {
          replace 0 with (swap01 (up_ren swap01 2)) by auto.
          replace swap01 with (up_ren_n 0 swap01) by auto.
          apply well_formedness_preserved_under_swap01; simpl.
          replace 1 with (up_ren swap01 2) by auto.
          replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
          apply well_formedness_preserved_under_swap01; simpl.
          inversion H3; subst. inversion H15; auto.
        }
        assert (
          (rename_process (up (rename_process (up P) swap01)) swap01) ⇛
            (rename_process (up (rename_process (up P') swap01)) swap01)
        ).
        {
          repeat (apply directed_cong_invariant_under_renaming || apply directed_cong_invariant_under_upshifting); auto;
          apply swap01_is_bijective.
        }
        destruct (IHn _ _ _ _ _ _ _ _
                      H10
                      eq_refl
                      eq_refl
                      HΓ'
                      H11
                      H12
                      H0) as [E'' [M'' [? [? ?]]]].
        exists (
          cons_r
            (cons_l
              (rename_process (up P2) swap01)
              (rename_axcut_ctx (rename_axcut_ctx (rename_axcut_ctx E'' swap01) (up_ren swap01)) swap01))
            (down (rename_process R1 swap01))
        ).
        exists (
          rename_message
            (rename_message
              (rename_message
                M''
                (up_ren_n (length_axcut_ctx E'') swap01))
              (up_ren_n (length_axcut_ctx (rename_axcut_ctx E'' swap01)) (up_ren swap01)))
            (up_ren_n (length_axcut_ctx ((rename_axcut_ctx (rename_axcut_ctx E'' swap01) (up_ren swap01)))) swap01)
        ).
        repeat split.
        + simpl. f_equal. f_equal.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply shift_preserves_bijection; try apply swap01_is_bijective.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
          rewrite <- H13.
          replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
          rewrite swap_swap_id. rewrite up_ren_swap_swap_idP. reflexivity.
        + eapply edc_assoc_lr; eauto.
          apply (edc_invariant_under_renaming _ _ swap01 swap01_is_bijective) in H14.
          rewrite swap_swap_idE in H14.
          apply (edc_invariant_under_renaming _ _ (up_ren swap01)) in H14;
          try apply shift_preserves_bijection; try apply swap01_is_bijective.
          replace (up_ren swap01) with (up_ren_n 1 swap01) in H14 by auto.
          rewrite up_ren_swap_swap_idE in H14.
          assumption.
        + repeat rewrite reduce_axcut_equation_3; simpl.
          repeat rewrite reduce_axcut_equation_4; simpl.
          repeat rewrite reduce_axcut_equation_3; simpl.
          assert (
            well_formed_axcut_ctx 0 E''
          ) as HE''ctx. { eapply edc_preserves_well_formedness; eauto. }
          eapply dc_cut_assoc_r.
          - inversion H3; subst. inversion H20; subst.
            intro. apply n_fv_down_Sn in H16; try lia.
            replace 2 with (swap01 2) in H16 by auto; apply fv_under_renaming in H16;
            try apply swap01_is_bijective.
            replace 2 with (up_ren swap01 1) in H16 by auto; apply fv_under_renaming in H16;
            try apply shift_preserves_bijection; try apply swap01_is_bijective.
            congruence.
          - eapply directed_cong_invariant_under_downshifting.
            eapply directed_cong_invariant_under_renaming; eauto.
            apply swap01_is_bijective.
            apply nfv_01_swap. inversion H3; auto.
          - replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
               with (up_ren_n (length_axcut_ctx E) (up_ren swap01)).
            apply H15.
            replace (up_ren swap01) with (up_ren_n 1 swap01) by auto;
            rewrite up_ren_n_additive.
            replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
               with (up_ren_n (S (length_axcut_ctx E)) swap01) by auto.
            f_equal; lia.
          - eapply directed_cong_invariant_under_downshifting.
            eapply directed_cong_invariant_under_renaming.
            eapply directed_cong_invariant_under_renaming; try apply shift_preserves_bijection; eauto.
            all: try apply swap01_is_bijective.
            replace 0 with (swap01 (up_ren swap01 2)) by auto.
            apply nfv_under_renaming; try apply swap01_is_bijective.
            apply nfv_under_renaming; try apply shift_preserves_bijection; try apply swap01_is_bijective.
            inversion H3; subst. inversion H20; auto.
          - unfold up.
            rewrite (proj1 up_after_down_id); try rewrite swap_swap_id.
            assert (
              ~ 1 ∈ P2
            ).
            {
              eapply nfv_under_struct_cong.
              eapply directed_cong_in_struct_cong; eauto.
              inversion H3; auto.
            }
            * unfold down. replace swap01 with (up_ren_n 0 swap01) by auto.
              rewrite (proj1 up_ren_n_swap_down_down_Sn).
              rewrite (proj1 up_ren_n_swap_lift_lift_Sn); simpl.
              replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
              rewrite (proj1 up_ren_n_swap_down_down_Sn); simpl.
              rewrite <- (proj1 lift_after_down_ge_commute); try lia.
              rewrite (proj1 up_after_down_id); auto.
              ** intro. apply fv_up_Sn2' in H17. congruence. lia.
              ** simpl.
                 replace 1 with (up_ren swap01 (swap01 2)) by auto.
                 apply nfv_under_renaming; try apply shift_preserves_bijection; try apply swap01_is_bijective.
                 apply nfv_under_renaming; try apply swap01_is_bijective.
                 simpl. intro. apply fv_up_Sn2 in H17; try lia. congruence.
            * apply nfv_01_swap. eapply nfv_under_struct_cong.
              eapply directed_cong_in_struct_cong; eauto.
              inversion H3; auto.
          - repeat rewrite <- rename_axcut_ctx_preserves_length.
            replace swap01 with (up_ren_n 0 swap01) by auto.
            rewrite up_ren_swap_over_reduce_axcut; simpl; eauto.
            {
              f_equal.
              + repeat (erewrite rename_axcut_ctx_compose; eauto).
                intros. unfold Basics.compose.
                destruct x as [|[|[|]]]; auto.
              + replace (length_axcut_ctx E'' + 1) with (S (length_axcut_ctx E'')) by lia.
                replace (up_ren (up_ren_n (length_axcut_ctx E'') swap01))
                   with (up_ren_n (S (length_axcut_ctx E'')) swap01)
                     by auto.
                replace (up_ren_n (length_axcut_ctx E'') (up_ren swap01))
                   with (up_ren_n (S (length_axcut_ctx E'')) swap01)
                    by  (replace (up_ren swap01) with (up_ren_n 1 swap01) by auto; rewrite up_ren_n_additive; f_equal; lia).
                repeat (erewrite (proj1 (proj2 renamings_compose)); eauto).
                intros. unfold Basics.compose.
                destruct (PeanoNat.Nat.eq_dec (length_axcut_ctx E'') x); subst.
                - rewrite up_ren_n_swap_n. rewrite up_ren_n_swap_n.
                  rewrite up_ren_n_swap_not_nSn with (j := S (S (length_axcut_ctx E''))); try lia.
                  rewrite up_ren_n_swap_Sn. rewrite up_ren_n_swap_Sn.
                  rewrite up_ren_n_swap_not_nSn; lia.
                - destruct (PeanoNat.Nat.eq_dec (S (length_axcut_ctx E'')) x); subst.
                  * rewrite up_ren_n_swap_Sn. rewrite up_ren_n_swap_n.
                    rewrite up_ren_n_swap_not_nSn with (j := length_axcut_ctx E''); try lia.
                    repeat rewrite up_ren_n_swap_n. rewrite up_ren_n_swap_not_nSn; lia.
                  * destruct (PeanoNat.Nat.eq_dec (S (S (length_axcut_ctx E''))) x); subst.
                    ** rewrite up_ren_n_swap_Sn.
                       rewrite up_ren_n_swap_not_nSn with (j := S (S (length_axcut_ctx E''))); try lia.
                       repeat rewrite up_ren_n_swap_Sn.
                       rewrite up_ren_n_swap_not_nSn with (j := length_axcut_ctx E''); try lia.
                       rewrite up_ren_n_swap_n. auto.
                    ** repeat rewrite up_ren_n_swap_not_nSn; try lia.
              + unfold up; replace swap01 with (up_ren_n 0 swap01) by auto.
                repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
                rewrite <- (proj1 lift_k_lift_Sj_lt_commute); auto.
            }
            {
              assert (
                exists Γ',
                  Γ' ⊢ fill_hole E'' M'' :#
              ).
              {
                simpl in H2. inversion H2; subst. inversion H21; subst.
                apply directed_cong_in_struct_cong in H8.
                apply ((proj1 struct_cong_preserves_typing) _ _ H8) in H23.
                destruct (up_ren_swap01_preserves_well_typedness _ _ H23).
                destruct (swap01_preserves_well_typedness _ _ H16).
                rewrite <- H13. eauto.
              }
              destruct H16.
              replace (length_axcut_ctx E'') with (length_axcut_ctx E'' + 0) by lia.
              eapply nfv_well_typed_fill_hole; eauto.
            }
          - assert ( ~ 1 ∈ R1 ). { eapply nfv_under_struct_cong. eapply directed_cong_in_struct_cong; eauto. auto. }
            assert ( ~ 2 ∈ R1 ).
            {
              eapply nfv_under_struct_cong. eapply directed_cong_in_struct_cong; eauto.
              inversion H3; subst. inversion H21; auto.
            }
            replace swap01 with (up_ren_n 0 swap01) by auto.
            rewrite (proj1 up_ren_n_swap_down_down_Sn); simpl.
            replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
            rewrite (proj1 up_ren_n_swap_down_down_Sn); simpl; auto.
            unfold down. replace swap01 with (up_ren_n 0 swap01) by auto.
            repeat rewrite (proj1 up_ren_n_swap_down_down_Sn); eauto.
            rewrite (proj1 down_k_down_Sj_lt_commute2); try lia; eauto.
            * eapply (proj1 nfv_down_lt); auto.
            * intro. apply (proj1 n_fv_down_Sn') in H18; auto.
            * replace 1 with (up_ren swap01 2) by auto.
              apply nfv_under_renaming; auto. apply shift_preserves_bijection.
              apply swap01_is_bijective.
      }
    - assert (
        (rename_process (fill_hole E M) swap01) ⇛
          (rename_process Q' swap01)
      ). { apply directed_cong_invariant_under_renaming; auto; apply swap01_is_bijective. }
      rewrite rename_axcut_ctx_over_fill_hole in H0; try apply swap01_is_bijective.
      assert (
        n >= length_axcut_ctx (rename_axcut_ctx E swap01)
      ). { rewrite <- rename_axcut_ctx_preserves_length; inversion H; lia. }
      assert (
        exists Γ',
          Γ' ⊢ (fill_hole (rename_axcut_ctx E swap01)
                          (rename_message M (up_ren_n (length_axcut_ctx E) swap01))) :#
      ) as Hwtfh.
      {
        simpl in H2; inversion H2; subst.
        destruct (swap01_preserves_well_typedness _ _ H13).
        eexists. rewrite rename_axcut_ctx_over_fill_hole in H7. eassumption.
        apply swap01_is_bijective.
      }
      destruct Hwtfh.
      assert (
        well_formed_axcut_ctx 0 (rename_axcut_ctx E swap01)
      ).
      {
        replace 0 with (swap01 1) by auto.
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; auto.
        inversion H3; auto.
      }
      assert (
        (rename_process (up P) swap01) ⇛
          (rename_process (up P') swap01)
      ).
      {
        apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
        apply directed_cong_invariant_under_upshifting; auto.
      }
      destruct (IHn _ _ _ _ _ _ _ _
                      H1
                      eq_refl
                      eq_refl
                      H7
                      H9
                      H10
                      H0) as [E'' [M'' [? [? ?]]]].
      exists (cons_l P'0 (rename_axcut_ctx E'' swap01)).
      exists (rename_message M'' (up_ren_n (length_axcut_ctx E'') swap01)).
      repeat split.
      * simpl. f_equal.
        assert (
          rename_process (rename_process Q' swap01) swap01
            = rename_process (fill_hole E'' M'') swap01
        ). { f_equal; auto. }
        rewrite swap_swap_id in H14. rewrite H14.
        rewrite <- rename_axcut_ctx_over_fill_hole; auto.
        apply swap01_is_bijective.
      * econstructor; eauto.
        apply (edc_invariant_under_renaming _ _ swap01 swap01_is_bijective) in H12.
        rewrite swap_swap_idE in H12. auto.
      * repeat rewrite reduce_axcut_equation_3.
        apply dc_cong_cut.
        ** apply directed_cong_invariant_under_downshifting; auto.
           -- apply directed_cong_invariant_under_renaming; auto.
              apply swap01_is_bijective.
           -- inversion H3; subst.
              apply nfv_01_swap; auto.
        ** rewrite swap_swap_idE.
           rewrite <- rename_axcut_ctx_preserves_length.
           rewrite up_ren_swap_swap_idM.
           assumption.
  + subst. simpl in H5. inversion H5; subst; simpl in H.
    - assert (
        (rename_process (fill_hole E M) swap01) ⇛
          (rename_process P'0 swap01)
      ). { apply directed_cong_invariant_under_renaming; auto; apply swap01_is_bijective. }
      rewrite rename_axcut_ctx_over_fill_hole in H0; try apply swap01_is_bijective.
      assert (
        n >= length_axcut_ctx (rename_axcut_ctx E swap01)
      ). { rewrite <- rename_axcut_ctx_preserves_length; inversion H; lia. }
      assert (
        exists Γ',
          Γ' ⊢ (fill_hole (rename_axcut_ctx E swap01)
                          (rename_message M (up_ren_n (length_axcut_ctx E) swap01))) :#
      ) as Hwtfh.
      {
        simpl in H2; inversion H2; subst.
        destruct (swap01_preserves_well_typedness _ _ H12).
        eexists. rewrite rename_axcut_ctx_over_fill_hole in H7. eassumption.
        apply swap01_is_bijective.
      }
      destruct Hwtfh.
      assert (
        well_formed_axcut_ctx 0 (rename_axcut_ctx E swap01)
      ).
      {
        replace 0 with (swap01 1) by auto.
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; auto.
        inversion H3; auto.
      }
      assert (
        (rename_process (up P) swap01) ⇛
          (rename_process (up P') swap01)
      ).
      {
        apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
        apply directed_cong_invariant_under_upshifting; auto.
      }
      destruct (IHn _ _ _ _ _ _ _ _
                      H1
                      eq_refl
                      eq_refl
                      H7
                      H9
                      H10
                      H0) as [E'' [M'' [? [? ?]]]].
      exists (cons_l Q' (rename_axcut_ctx E'' swap01)).
      exists (rename_message M'' (up_ren_n (length_axcut_ctx E'') swap01)).
      repeat split.
      * simpl. f_equal.
        assert (
          rename_process (rename_process P'0 swap01) swap01
            = rename_process (fill_hole E'' M'') swap01
        ). { f_equal; auto. }
        rewrite swap_swap_id in H14. rewrite H14.
        rewrite <- rename_axcut_ctx_over_fill_hole; auto.
        apply swap01_is_bijective.
      * econstructor; eauto.
        apply (edc_invariant_under_renaming _ _ swap01 swap01_is_bijective) in H12.
        rewrite swap_swap_idE in H12. auto.
      * repeat rewrite reduce_axcut_equation_3.
        repeat rewrite reduce_axcut_equation_4.
        apply dc_cut_comm.
        ** rewrite swap_swap_idE.
           rewrite <- rename_axcut_ctx_preserves_length.
           rewrite up_ren_swap_swap_idM.
           assumption.
        ** apply directed_cong_invariant_under_downshifting; auto.
           -- apply directed_cong_invariant_under_renaming; auto.
              apply swap01_is_bijective.
           -- inversion H3; subst.
              apply nfv_01_swap; auto.
    - destruct E; simpl in H0; try congruence; inversion H0; subst; simpl in H.
      {
        assert (
        (rename_process (rename_process (fill_hole E M) (up_ren swap01)) swap01) ⇛
          (rename_process (rename_process Q1 (up_ren swap01)) swap01)
        ). { repeat  apply directed_cong_invariant_under_renaming; auto; try apply shift_preserves_bijection; apply swap01_is_bijective. }
        rewrite rename_axcut_ctx_over_fill_hole in H1;
        try apply shift_preserves_bijection; try apply swap01_is_bijective.
        rewrite rename_axcut_ctx_over_fill_hole in H1; try apply swap01_is_bijective.
        assert (
          n >= length_axcut_ctx (rename_axcut_ctx (rename_axcut_ctx E (up_ren swap01)) swap01)
        ). { repeat rewrite <- rename_axcut_ctx_preserves_length. inversion H; lia. }
        assert (
          exists Γ',
            Γ' ⊢
              (fill_hole (rename_axcut_ctx (rename_axcut_ctx E (up_ren swap01)) swap01)
                         (rename_message
                          (rename_message M (up_ren_n (length_axcut_ctx E) (up_ren swap01)))
                          (up_ren_n (length_axcut_ctx (rename_axcut_ctx E (up_ren swap01))) swap01))) :#
        ).
        {
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply shift_preserves_bijection; try apply swap01_is_bijective.
          simpl in H2; inversion H2; subst. inversion H15; subst.
          destruct (up_ren_swap01_preserves_well_typedness _ _ H19).
          destruct (swap01_preserves_well_typedness _ _ H11).
          eauto.
        }
        destruct H11 as [Γ' HΓ'].
        assert (
          well_formed_axcut_ctx 0 (rename_axcut_ctx (rename_axcut_ctx E (up_ren swap01)) swap01)
        ).
        {
          replace 0 with (swap01 (up_ren swap01 2)) by auto.
          replace swap01 with (up_ren_n 0 swap01) by auto.
          apply well_formedness_preserved_under_swap01; simpl.
          replace 1 with (up_ren swap01 2) by auto.
          replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
          apply well_formedness_preserved_under_swap01; simpl.
          inversion H3; subst. inversion H15; auto.
        }
        assert (
          (rename_process (up (rename_process (up P) swap01)) swap01) ⇛
            (rename_process (up (rename_process (up P') swap01)) swap01)
        ).
        {
          repeat (apply directed_cong_invariant_under_renaming || apply directed_cong_invariant_under_upshifting); auto;
          apply swap01_is_bijective.
        }
        destruct (IHn _ _ _ _ _ _ _ _
                      H10
                      eq_refl
                      eq_refl
                      HΓ'
                      H11
                      H12
                      H1) as [E'' [M'' [? [? ?]]]].
        exists (
          cons_l
            (down (rename_process P2 swap01))
            (cons_r
              (rename_axcut_ctx (rename_axcut_ctx (rename_axcut_ctx E'' swap01) (up_ren swap01)) swap01)
              (rename_process (up R1) swap01))
        ).
        exists (
          rename_message
            (rename_message
              (rename_message
                M''
                (up_ren_n (length_axcut_ctx E'') swap01))
              (up_ren_n (length_axcut_ctx (rename_axcut_ctx E'' swap01)) (up_ren swap01)))
            (up_ren_n (length_axcut_ctx ((rename_axcut_ctx (rename_axcut_ctx E'' swap01) (up_ren swap01)))) swap01)
        ).
        repeat split.
        + simpl. f_equal. f_equal.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply shift_preserves_bijection; try apply swap01_is_bijective.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
          rewrite <- H13.
          replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
          rewrite swap_swap_id. rewrite up_ren_swap_swap_idP. reflexivity.
        + eapply edc_assoc_rl; eauto.
          apply (edc_invariant_under_renaming _ _ swap01 swap01_is_bijective) in H14.
          rewrite swap_swap_idE in H14.
          apply (edc_invariant_under_renaming _ _ (up_ren swap01)) in H14;
          try apply shift_preserves_bijection; try apply swap01_is_bijective.
          replace (up_ren swap01) with (up_ren_n 1 swap01) in H14 by auto.
          rewrite up_ren_swap_swap_idE in H14.
          assumption.
        + repeat rewrite reduce_axcut_equation_3; simpl.
          repeat rewrite reduce_axcut_equation_4; simpl.
          repeat rewrite reduce_axcut_equation_3; simpl.
          assert (
            well_formed_axcut_ctx 0 E''
          ) as HE''ctx. { eapply edc_preserves_well_formedness; eauto. }
          eapply dc_cut_assoc_l.
          - inversion H3; subst. inversion H20; subst.
            intro. apply n_fv_down_Sn in H16; try lia.
            replace 2 with (swap01 2) in H16 by auto; apply fv_under_renaming in H16;
            try apply swap01_is_bijective.
            replace 2 with (up_ren swap01 1) in H16 by auto; apply fv_under_renaming in H16;
            try apply shift_preserves_bijection; try apply swap01_is_bijective.
            congruence.
          - eapply directed_cong_invariant_under_downshifting.
            eapply directed_cong_invariant_under_renaming.
            eapply directed_cong_invariant_under_renaming; try apply shift_preserves_bijection; eauto.
            all: try apply swap01_is_bijective.
            replace 0 with (swap01 (up_ren swap01 2)) by auto.
            apply nfv_under_renaming; try apply swap01_is_bijective.
            apply nfv_under_renaming; try apply shift_preserves_bijection; try apply swap01_is_bijective.
            inversion H3; subst. inversion H20; auto.
          - replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
               with (up_ren_n (length_axcut_ctx E) (up_ren swap01)).
            apply H15.
            replace (up_ren swap01) with (up_ren_n 1 swap01) by auto;
            rewrite up_ren_n_additive.
            replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
               with (up_ren_n (S (length_axcut_ctx E)) swap01) by auto.
            f_equal; lia.
          - eapply directed_cong_invariant_under_downshifting.
            eapply directed_cong_invariant_under_renaming; eauto.
            apply swap01_is_bijective.
            apply nfv_01_swap. inversion H3; auto.
          - assert ( ~ 1 ∈ P2 ). { eapply nfv_under_struct_cong. eapply directed_cong_in_struct_cong; eauto. auto. }
            assert ( ~ 2 ∈ P2 ).
            {
              eapply nfv_under_struct_cong. eapply directed_cong_in_struct_cong; eauto.
              inversion H3; subst. inversion H21; auto.
            }
            replace swap01 with (up_ren_n 0 swap01) by auto.
            rewrite (proj1 up_ren_n_swap_down_down_Sn); simpl.
            replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
            rewrite (proj1 up_ren_n_swap_down_down_Sn); simpl; auto.
            unfold down. replace swap01 with (up_ren_n 0 swap01) by auto.
            repeat rewrite (proj1 up_ren_n_swap_down_down_Sn); eauto.
            rewrite (proj1 down_k_down_Sj_lt_commute2); try lia; eauto.
            * eapply (proj1 nfv_down_lt); auto.
            * intro. apply (proj1 n_fv_down_Sn') in H18; auto.
            * replace 1 with (up_ren swap01 2) by auto.
              apply nfv_under_renaming; auto. apply shift_preserves_bijection.
              apply swap01_is_bijective.
          - repeat rewrite <- rename_axcut_ctx_preserves_length.
            replace swap01 with (up_ren_n 0 swap01) by auto.
            rewrite up_ren_swap_over_reduce_axcut; simpl; eauto.
            {
              f_equal.
              + repeat (erewrite rename_axcut_ctx_compose; eauto).
                intros. unfold Basics.compose.
                destruct x as [|[|[|]]]; auto.
              + replace (length_axcut_ctx E'' + 1) with (S (length_axcut_ctx E'')) by lia.
                replace (up_ren (up_ren_n (length_axcut_ctx E'') swap01))
                   with (up_ren_n (S (length_axcut_ctx E'')) swap01)
                     by auto.
                replace (up_ren_n (length_axcut_ctx E'') (up_ren swap01))
                   with (up_ren_n (S (length_axcut_ctx E'')) swap01)
                    by  (replace (up_ren swap01) with (up_ren_n 1 swap01) by auto; rewrite up_ren_n_additive; f_equal; lia).
                repeat (erewrite (proj1 (proj2 renamings_compose)); eauto).
                intros. unfold Basics.compose.
                destruct (PeanoNat.Nat.eq_dec (length_axcut_ctx E'') x); subst.
                - rewrite up_ren_n_swap_n. rewrite up_ren_n_swap_n.
                  rewrite up_ren_n_swap_not_nSn with (j := S (S (length_axcut_ctx E''))); try lia.
                  rewrite up_ren_n_swap_Sn. rewrite up_ren_n_swap_Sn.
                  rewrite up_ren_n_swap_not_nSn; lia.
                - destruct (PeanoNat.Nat.eq_dec (S (length_axcut_ctx E'')) x); subst.
                  * rewrite up_ren_n_swap_Sn. rewrite up_ren_n_swap_n.
                    rewrite up_ren_n_swap_not_nSn with (j := length_axcut_ctx E''); try lia.
                    repeat rewrite up_ren_n_swap_n. rewrite up_ren_n_swap_not_nSn; lia.
                  * destruct (PeanoNat.Nat.eq_dec (S (S (length_axcut_ctx E''))) x); subst.
                    ** rewrite up_ren_n_swap_Sn.
                       rewrite up_ren_n_swap_not_nSn with (j := S (S (length_axcut_ctx E''))); try lia.
                       repeat rewrite up_ren_n_swap_Sn.
                       rewrite up_ren_n_swap_not_nSn with (j := length_axcut_ctx E''); try lia.
                       rewrite up_ren_n_swap_n. auto.
                    ** repeat rewrite up_ren_n_swap_not_nSn; try lia.
              + unfold up; replace swap01 with (up_ren_n 0 swap01) by auto.
                repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
                rewrite <- (proj1 lift_k_lift_Sj_lt_commute); auto.
            }
            {
              assert (
                exists Γ',
                  Γ' ⊢ fill_hole E'' M'' :#
              ).
              {
                simpl in H2. inversion H2; subst. inversion H20; subst.
                apply directed_cong_in_struct_cong in H8.
                apply ((proj1 struct_cong_preserves_typing) _ _ H8) in H24.
                destruct (up_ren_swap01_preserves_well_typedness _ _ H24).
                destruct (swap01_preserves_well_typedness _ _ H16).
                rewrite <- H13. eauto.
              }
              destruct H16.
              replace (length_axcut_ctx E'') with (length_axcut_ctx E'' + 0) by lia.
              eapply nfv_well_typed_fill_hole; eauto.
            }
          - unfold up.
            rewrite (proj1 up_after_down_id); try rewrite swap_swap_id.
            assert (
              ~ 1 ∈ R1
            ).
            {
              eapply nfv_under_struct_cong.
              eapply directed_cong_in_struct_cong; eauto.
              inversion H3; auto.
            }
            * unfold down. replace swap01 with (up_ren_n 0 swap01) by auto.
              rewrite (proj1 up_ren_n_swap_down_down_Sn).
              rewrite (proj1 up_ren_n_swap_lift_lift_Sn); simpl.
              replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
              rewrite (proj1 up_ren_n_swap_down_down_Sn); simpl.
              rewrite <- (proj1 lift_after_down_ge_commute); try lia.
              rewrite (proj1 up_after_down_id); auto.
              ** intro. apply fv_up_Sn2' in H17. congruence. lia.
              ** simpl.
                 replace 1 with (up_ren swap01 (swap01 2)) by auto.
                 apply nfv_under_renaming; try apply shift_preserves_bijection; try apply swap01_is_bijective.
                 apply nfv_under_renaming; try apply swap01_is_bijective.
                 simpl. intro. apply fv_up_Sn2 in H17; try lia. congruence.
            * apply nfv_01_swap. eapply nfv_under_struct_cong.
              eapply directed_cong_in_struct_cong; eauto.
              inversion H3; auto.
      }
      {
        assert (
        (rename_process (rename_process (fill_hole E M) (up_ren swap01)) swap01) ⇛
          (rename_process (rename_process P2 (up_ren swap01)) swap01)
        ). { repeat  apply directed_cong_invariant_under_renaming; auto; try apply shift_preserves_bijection; apply swap01_is_bijective. }
        rewrite rename_axcut_ctx_over_fill_hole in H1;
        try apply shift_preserves_bijection; try apply swap01_is_bijective.
        rewrite rename_axcut_ctx_over_fill_hole in H1; try apply swap01_is_bijective.
        assert (
          n >= length_axcut_ctx (rename_axcut_ctx (rename_axcut_ctx E (up_ren swap01)) swap01)
        ). { repeat rewrite <- rename_axcut_ctx_preserves_length. inversion H; lia. }
        assert (
          exists Γ',
            Γ' ⊢
              (fill_hole (rename_axcut_ctx (rename_axcut_ctx E (up_ren swap01)) swap01)
                         (rename_message
                          (rename_message M (up_ren_n (length_axcut_ctx E) (up_ren swap01)))
                          (up_ren_n (length_axcut_ctx (rename_axcut_ctx E (up_ren swap01))) swap01))) :#
        ).
        {
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply shift_preserves_bijection; try apply swap01_is_bijective.
          simpl in H2; inversion H2; subst. inversion H15; subst.
          destruct (up_ren_swap01_preserves_well_typedness _ _ H18).
          destruct (swap01_preserves_well_typedness _ _ H11).
          eauto.
        }
        destruct H11 as [Γ' HΓ'].
        assert (
          well_formed_axcut_ctx 0 (rename_axcut_ctx (rename_axcut_ctx E (up_ren swap01)) swap01)
        ).
        {
          replace 0 with (swap01 (up_ren swap01 2)) by auto.
          replace swap01 with (up_ren_n 0 swap01) by auto.
          apply well_formedness_preserved_under_swap01; simpl.
          replace 1 with (up_ren swap01 2) by auto.
          replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
          apply well_formedness_preserved_under_swap01; simpl.
          inversion H3; subst. inversion H15; auto.
        }
        assert (
          (rename_process (up (rename_process (up P) swap01)) swap01) ⇛
            (rename_process (up (rename_process (up P') swap01)) swap01)
        ).
        {
          repeat (apply directed_cong_invariant_under_renaming || apply directed_cong_invariant_under_upshifting); auto;
          apply swap01_is_bijective.
        }
        destruct (IHn _ _ _ _ _ _ _ _
                      H10
                      eq_refl
                      eq_refl
                      HΓ'
                      H11
                      H12
                      H1) as [E'' [M'' [? [? ?]]]].
        pose (rename_axcut_ctx (rename_axcut_ctx E'' swap01) (up_ren swap01)) as E'''.
        pose (
          rename_message
            (rename_message M'' (up_ren_n (length_axcut_ctx E'') swap01))
            (up_ren_n (length_axcut_ctx (rename_axcut_ctx E'' swap01)) (up_ren swap01))
        ) as M'''.
        exists (
          cons_r (downE (rename_axcut_ctx E''' swap01))
                 (cut (rename_process Q1 swap01)
                      (rename_process (up R1) swap01))
        ).
        exists (
          down1_message
            (rename_message M''' (up_ren_n (length_axcut_ctx E''') swap01))
            (length_axcut_ctx (rename_axcut_ctx E''' swap01) + 0)
        ).
        repeat split.
        + simpl. f_equal.
          unfold downE. rewrite <- down_ctx_over_fill_hole.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
          subst E''' M'''.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply shift_preserves_bijection; try apply swap01_is_bijective.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
          rewrite <- H13. unfold down.
          rewrite swap_swap_id.
          replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
          rewrite up_ren_swap_swap_idP.
          reflexivity.
        + eapply edc_assoc_rr; eauto.
          - subst E'''.
            apply (edc_invariant_under_renaming _ _ swap01 swap01_is_bijective) in H14.
            rewrite swap_swap_idE in H14.
            apply (edc_invariant_under_renaming _ _ (up_ren swap01)) in H14;
            try apply shift_preserves_bijection; try apply swap01_is_bijective.
            replace (up_ren swap01) with (up_ren_n 1 swap01) in H14 by auto.
            rewrite up_ren_swap_swap_idE in H14.
            assumption.
          - apply (proj1 (nfv_fill_hole _ _ _ H6)).
        + repeat rewrite reduce_axcut_equation_4; simpl.
          repeat rewrite reduce_axcut_equation_4; simpl.
          eapply dc_cut_assoc_l.
          - eapply nfv_reduce_axcut.
            * replace 0 with (swap01 1) by auto.
              replace swap01 with (up_ren_n 0 swap01) by auto.
              apply well_formedness_preserved_under_swap01; simpl.
              replace 1 with (up_ren swap01 2) by auto.
              replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
              apply well_formedness_preserved_under_swap01.
              inversion H3; subst. inversion H20; auto.
            * replace 2 with (swap01 2) by auto.
              apply nfv_ctx_under_renaming; try apply swap01_is_bijective.
              replace 2 with (up_ren swap01 1) by auto.
              apply nfv_ctx_under_renaming. apply shift_preserves_bijection; apply swap01_is_bijective.
              apply (proj1 (nfv_fill_hole _ _ _ H6)).
            * repeat rewrite <- rename_axcut_ctx_preserves_length.
              replace (length_axcut_ctx E)
                 with (up_ren_n (length_axcut_ctx E) swap01 (S (length_axcut_ctx E)))
                   at 1
                   by (rewrite up_ren_n_swap_Sn; auto).
              apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
                 with (up_ren_n (S (length_axcut_ctx E)) swap01) by auto.
              replace (S (length_axcut_ctx E))
                 with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (S (length_axcut_ctx E))))
                   at 1
                   by (rewrite up_ren_n_swap_Sn; auto).
              apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              replace (S (S (length_axcut_ctx E))) with (length_axcut_ctx E + 2) by lia.
              simpl in H2; inversion H2; subst. inversion H20; subst.
              inversion H3; subst. inversion H26; subst.
              apply (nfv_well_typed_fill_hole _ _ _ _ H28 H23).
            * repeat rewrite <- rename_axcut_ctx_preserves_length.
              replace (length_axcut_ctx E + 2) with (S (S (length_axcut_ctx E))) by lia.
              replace (S (S (length_axcut_ctx E)))
                 with (up_ren_n (length_axcut_ctx E) swap01 (S (S (length_axcut_ctx E))))
                   by (rewrite up_ren_n_swap_not_nSn; lia).
              apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              replace (up_ren (up_ren_n (length_axcut_ctx E) swap01))
                 with (up_ren_n (S (length_axcut_ctx E)) swap01)
                  by auto.
              replace (S (S (length_axcut_ctx E)))
                 with (up_ren_n (S (length_axcut_ctx E)) swap01 (S (length_axcut_ctx E)))
                   by (rewrite up_ren_n_swap_n; auto).
              apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              replace (S (length_axcut_ctx E)) with (length_axcut_ctx E + 1) by lia.
              apply (proj2 (nfv_fill_hole _ _ _ H6)).
            * unfold up. repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
              rewrite (proj1 shift_additive). apply nfv_lift_n; lia.
          - replace (up_ren (up_ren_n (length_axcut_ctx E) swap01)) with
                    (up_ren_n (length_axcut_ctx E) (up_ren swap01)).
            eapply H15.
            replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
            rewrite up_ren_n_additive.
            replace (length_axcut_ctx E + 1) with (S (length_axcut_ctx E)) by lia.
            reflexivity.
          - eapply directed_cong_invariant_under_downshifting.
            eapply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
            eapply directed_cong_invariant_under_renaming; eauto; try apply shift_preserves_bijection; try apply swap01_is_bijective.
            replace 0 with (swap01 (up_ren swap01 2)) by auto.
            apply nfv_under_renaming; try apply swap01_is_bijective.
            apply nfv_under_renaming; try apply shift_preserves_bijection; try apply swap01_is_bijective.
            inversion H3; subst. inversion H20; subst. auto.
          - eapply directed_cong_invariant_under_downshifting.
            eapply directed_cong_invariant_under_renaming; eauto; try apply swap01_is_bijective.
            apply nfv_01_swap. inversion H3; auto.
          - replace swap01 with (up_ren_n 0 swap01) by auto.
            assert (
              well_formed_axcut_ctx 0 E''
            ).
            { eapply edc_preserves_well_formedness; eauto. }
            assert (
              ~ occurs_free_message (length_axcut_ctx E'') M''
            ).
            {
              assert (
                exists Γ',
                  Γ' ⊢ fill_hole E'' M'' :#
              ).
              {
                simpl in H2; inversion H2; subst. inversion H21; subst.
                apply directed_cong_in_struct_cong in H7.
                apply ((proj1 struct_cong_preserves_typing) _ _ H7) in H24.
                rewrite <- H13.
                destruct (up_ren_swap01_preserves_well_typedness _ _ H24).
                destruct (swap01_preserves_well_typedness _ _ H17).
                eauto.
              }
              destruct H17.
              replace (length_axcut_ctx E'') with (length_axcut_ctx E'' + 0) by lia.
              eapply nfv_well_typed_fill_hole; eauto.
            }
            rewrite up_ren_swap_over_reduce_axcut; simpl; eauto.
            unfold down.
            assert ( ~ 1 ∈ P2 ).
            {
              eapply nfv_under_struct_cong. apply directed_cong_in_struct_cong; eauto. eauto.
            }
            assert ( ~ 2 ∈ rename_process (rename_process P2 (up_ren swap01)) swap01 ).
            {
              replace 2 with (swap01 (up_ren swap01 1)) by auto.
              apply nfv_under_renaming; try apply swap01_is_bijective.
              apply nfv_under_renaming; auto. apply shift_preserves_bijection; apply swap01_is_bijective.
            }
            assert ( ~ occurs_free_ctx 2 E'' ).
            {
              rewrite H13 in H19.
              apply (proj1 (nfv_fill_hole _ _ _ H19)).
            }
            rewrite down_over_reduce_axcut.
            ** f_equal.
               {
                unfold downE. subst E'''.
                replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
                rewrite up_ren_n_swap_down_down_Sn_ctx.
                + replace swap01 with (up_ren_n 0 swap01) by auto.
                  rewrite up_ren_n_swap_down_down_Sn_ctx; simpl.
                  - replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
                    rewrite up_ren_n_swap_down_down_Sn_ctx; simpl.
                    * rewrite down_at_k_rename_id_after_k_commute_ctx. rewrite swap_swap_idE; auto.
                      apply swap01_is_bijective. intros [|[|]] ?; auto; exfalso; lia.
                    * replace 2 with (swap01 2) by auto. apply nfv_ctx_under_renaming. apply swap01_is_bijective. auto.
                  - replace 1 with (up_ren swap01 (swap01 2)) by auto.
                    apply nfv_ctx_under_renaming. apply shift_preserves_bijection; apply swap01_is_bijective.
                    apply nfv_ctx_under_renaming; auto. apply swap01_is_bijective.
                + assumption.
               }
               {
                subst E'''. subst M'''.
                unfold downE. rewrite down_ctx_preserves_length.
                repeat rewrite <- rename_axcut_ctx_preserves_length.
                rewrite <- plus_n_O.
                repeat rewrite PeanoNat.Nat.add_1_r; simpl.
                replace (up_ren_n (length_axcut_ctx E'') (up_ren swap01))
                       with (up_ren_n (S (length_axcut_ctx E'')) swap01).
                repeat rewrite (proj1 (proj2 up_ren_n_swap_down_down_Sn)).
                replace (up_ren (up_ren_n (length_axcut_ctx E'') swap01))
                       with (up_ren_n (S (length_axcut_ctx E'')) swap01) by auto.
                repeat rewrite (proj1 (proj2 up_ren_n_swap_down_down_Sn)).
                rewrite (proj1 (proj2 down_at_k_rename_id_after_k_commute)).
                rewrite up_ren_swap_swap_idM; auto.
                apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
                + intros. rewrite up_ren_n_swap_not_nSn; lia.
                + replace (S (S (length_axcut_ctx E''))) with (length_axcut_ctx E'' + 2) by lia.
                  rewrite H13 in H19.
                  apply (proj2 (nfv_fill_hole _ _ _ H19)).
                + replace (S (S (length_axcut_ctx E''))) with
                          (up_ren_n (length_axcut_ctx E'') swap01 (S (S (length_axcut_ctx E'')))).
                  apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
                  replace (S (S (length_axcut_ctx E''))) with (length_axcut_ctx E'' + 2) by lia.
                  rewrite H13 in H19.
                  apply (proj2 (nfv_fill_hole _ _ _ H19)).
                  rewrite up_ren_n_swap_not_nSn; lia.
                + replace (S (length_axcut_ctx E'')) with
                          (up_ren_n (S (length_axcut_ctx E'')) swap01 (S (S (length_axcut_ctx E''))))
                          at 1 by (rewrite up_ren_n_swap_Sn; try lia; auto).
                  apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
                  replace (S (S (length_axcut_ctx E''))) with
                          (up_ren_n (length_axcut_ctx E'') swap01 (S (S (length_axcut_ctx E'')))).
                  apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
                  replace (S (S (length_axcut_ctx E''))) with (length_axcut_ctx E'' + 2) by lia.
                  rewrite H13 in H19.
                  apply (proj2 (nfv_fill_hole _ _ _ H19)).
                  rewrite up_ren_n_swap_not_nSn; lia.
                + replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
                  rewrite up_ren_n_additive. f_equal; lia.
               }
               {
                unfold up. repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
                rewrite <- (proj1 lift_after_down_lt_commute_nfv); try lia.
                rewrite (proj1 down_after_up_id); auto.
                apply nfv_lift_n; lia.
               }
            ** replace 0 with (up_ren swap01 0) by auto.
               replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
               apply well_formedness_preserved_under_swap01.
               eapply edc_preserves_well_formedness; eauto.
            ** replace 1 with (up_ren swap01 2) by auto. apply nfv_under_renaming.
               apply shift_preserves_bijection; apply swap01_is_bijective.
               unfold up. repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
               rewrite (proj1 shift_additive). apply nfv_lift_n; lia.
            ** replace 1 with (up_ren swap01 2) by auto.
               apply nfv_ctx_under_renaming; auto. apply shift_preserves_bijection; apply swap01_is_bijective.
            ** rewrite <- rename_axcut_ctx_preserves_length.
               repeat rewrite PeanoNat.Nat.add_1_r.
               replace (S (length_axcut_ctx E'')) with
                       (up_ren_n (S (length_axcut_ctx E'')) swap01 (S (S (length_axcut_ctx E''))))
                       at 1 by (rewrite up_ren_n_swap_Sn; auto).
              apply nfv_under_renaming. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              rewrite H13 in H19.
              replace (S (S (length_axcut_ctx E''))) with (length_axcut_ctx E'' + 2) by lia.
              apply (proj2 (nfv_fill_hole _ _ _ H19)).
            ** rewrite <- rename_axcut_ctx_preserves_length.
               repeat rewrite PeanoNat.Nat.add_1_r.
               replace (length_axcut_ctx E'') with
                       (up_ren_n (S (length_axcut_ctx E'')) swap01 (length_axcut_ctx E''))
                       at 1 by (rewrite up_ren_n_swap_not_nSn; lia).
              apply nfv_under_renaming; auto. apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
          - replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
            rewrite (proj1 up_ren_n_swap_down_down_Sn).
            * replace swap01 with (up_ren_n 0 swap01) by auto.
              rewrite (proj1 up_ren_n_swap_down_down_Sn). simpl.
              replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
              rewrite (proj1 up_ren_n_swap_down_down_Sn).
              rewrite (proj1 down_at_k_rename_id_after_k_commute); auto.
              apply swap01_is_bijective. intros [|[|]] ?; auto; exfalso; lia.
              inversion H3; subst. inversion H20; subst.
              eapply nfv_under_struct_cong. apply directed_cong_in_struct_cong; eauto. eauto.
              simpl. replace 1 with (up_ren swap01 2) by auto. apply nfv_under_renaming.
              apply shift_preserves_bijection; apply swap01_is_bijective.
              inversion H3; subst. inversion H20; subst.
              eapply nfv_under_struct_cong. apply directed_cong_in_struct_cong; eauto. eauto.
            * replace 2 with (swap01 2) by auto. apply nfv_under_renaming. apply swap01_is_bijective.
              inversion H3; subst. inversion H20; subst.
              eapply nfv_under_struct_cong. apply directed_cong_in_struct_cong; eauto. eauto.
          - unfold up.
            rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
            replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
            rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
            replace swap01 with (up_ren_n 0 swap01) by auto.
            rewrite (proj1 up_ren_n_swap_down_down_Sn).
            * rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
              rewrite (proj1 lift_after_down_lt_commute_nfv); auto.
              inversion H3; subst.
              eapply nfv_under_struct_cong. eapply directed_cong_in_struct_cong; eauto.
              eauto.
            * inversion H3; subst.
              eapply nfv_under_struct_cong. eapply directed_cong_in_struct_cong; eauto.
              eauto.
      }
    - assert (
        (rename_process (fill_hole E M) swap01) ⇛
          (rename_process P2 swap01)
      ). { apply directed_cong_invariant_under_renaming; auto; apply swap01_is_bijective. }
      rewrite rename_axcut_ctx_over_fill_hole in H0; try apply swap01_is_bijective.
      assert (
        n >= length_axcut_ctx (rename_axcut_ctx E swap01)
      ). { rewrite <- rename_axcut_ctx_preserves_length; inversion H; lia. }
      assert (
        exists Γ',
          Γ' ⊢ (fill_hole (rename_axcut_ctx E swap01)
                          (rename_message M (up_ren_n (length_axcut_ctx E) swap01))) :#
      ) as Hwtfh.
      {
        simpl in H2; inversion H2; subst.
        destruct (swap01_preserves_well_typedness _ _ H14).
        rewrite rename_axcut_ctx_over_fill_hole in H10.
        eexists; eauto.
        apply swap01_is_bijective.
      }
      destruct Hwtfh as [Γ' ?].
      assert (
        well_formed_axcut_ctx 0 (rename_axcut_ctx E swap01)
      ).
      {
        replace 0 with (swap01 1) by auto.
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01.
        inversion H3; auto.
      }
      assert (
        (rename_process (up P) swap01) ⇛
          (rename_process (up P') swap01)
      ).
      {
        apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
        apply directed_cong_invariant_under_upshifting; auto.
      }
      destruct (IHn _ _ _ _ _ _ _ _
                    H1
                    eq_refl
                    eq_refl
                    H10
                    H11
                    H12
                    H0) as [E'' [M'' [? [? ?]]]].
      exists (
        cons_r (cons_r (rename_axcut_ctx (upE (rename_axcut_ctx E'' swap01)) swap01)
                       (rename_process Q1 swap01))
               (down (rename_process R1 swap01))
      ).
      exists (
        rename_message
          (lift_message (rename_message M'' (up_ren_n (length_axcut_ctx E'') swap01))
            (length_axcut_ctx (rename_axcut_ctx E'' swap01)) 1)
          (up_ren_n (length_axcut_ctx (upE (rename_axcut_ctx E'' swap01))) swap01)
      ).
      repeat split.
      * simpl. f_equal. f_equal.
        rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
        replace (length_axcut_ctx (rename_axcut_ctx E'' swap01)) with (length_axcut_ctx (rename_axcut_ctx E'' swap01) + 0) by lia.
        unfold upE. rewrite <- up_ctx_over_fill_hole.
        rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
        f_equal. unfold up. f_equal.
        rewrite <- H13.
        rewrite swap_swap_id.
        reflexivity.
      * eapply edc_assoc_cut_r; eauto.
        apply (edc_invariant_under_renaming _ _ swap01 swap01_is_bijective) in H14.
        rewrite swap_swap_idE in H14.
        assumption.
      * repeat rewrite reduce_axcut_equation_4; simpl.
        repeat rewrite reduce_axcut_equation_4; simpl.
        eapply dc_cut_assoc_r.
        ** intro.
           apply n_fv_down_Sn' in H16; auto.
           -- apply ((proj1 nfv_under_renaming) _ (up_ren swap01)) in H6.
              simpl in H6; congruence.
              apply shift_preserves_bijection; apply swap01_is_bijective.
           -- replace 1 with (up_ren swap01 2) by auto.
              apply nfv_under_renaming.
              apply shift_preserves_bijection; apply swap01_is_bijective.
              inversion H3; subst.
              intro; apply H21; free_var_econstructor; eauto.
        ** apply H15.
        ** replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
           assert (~ 2 ∈ Q).
           { inversion H3; subst. intro. apply H19; apply fv_cut_l; eauto. }
           rewrite (proj1 up_ren_n_swap_down_down_Sn); eauto.
           apply directed_cong_invariant_under_downshifting; eauto.
        ** replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
           assert (~ 2 ∈ R0).
           { inversion H3; subst. intro. apply H19; free_var_econstructor; eauto. }
           rewrite (proj1 up_ren_n_swap_down_down_Sn); eauto.
           apply directed_cong_invariant_under_downshifting; eauto.
        ** repeat rewrite <- rename_axcut_ctx_preserves_length.
           repeat rewrite lift_ctx_preserves_length.
           unfold up.
           assert (
            ~ occurs_free_message (length_axcut_ctx E'') M''
           ).
           {
            replace (length_axcut_ctx E'') with (length_axcut_ctx E'' + 0) by lia.
            assert (
              exists Γ', Γ' ⊢ (fill_hole E'' M'') :#
            ).
            {
              simpl in H2; inversion H2; subst.
              apply (directed_cong_preserves_typing _ _ _ H20) in H7.
              destruct (swap01_preserves_well_typedness _ _ H7).
              rewrite H13 in H16. eexists; eauto.
            }
            destruct H16.
            eapply nfv_well_typed_fill_hole; eauto.
            eapply edc_preserves_well_formedness; eauto.
           }
           rewrite lift_over_reduce_axcut.
           -- replace swap01 with (up_ren_n 0 swap01) by auto.
              rewrite up_ren_swap_over_reduce_axcut; simpl.
              ++ f_equal.
                 {
                  unfold upE.
                  replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
                  repeat rewrite up_ren_n_swap_lift_lift_Sn_ctx.
                  rewrite lift_ctx_at_k_rename_ctx_id_after_k_commute.
                  + rewrite swap_swap_idE; auto.
                  + apply swap01_is_bijective.
                  + intros [|[|]] ?; auto; exfalso; lia.
                 }
                 {
                  unfold upE.
                  repeat rewrite lift_ctx_preserves_length.
                  repeat rewrite <- rename_axcut_ctx_preserves_length.
                  repeat rewrite (proj1 (proj2 up_ren_n_swap_lift_lift_Sn)).
                  rewrite (proj1 (proj2 lift_at_k_rename_id_after_k_commute)).
                  + rewrite up_ren_swap_swap_idM. f_equal; lia.
                  + apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
                  + intros. rewrite up_ren_n_swap_not_nSn; auto; lia.
                 }
                 {
                  replace swap01 with (up_ren_n 0 swap01) at 1 by auto.
                  repeat rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
                  rewrite ((proj1 lift_k_lift_Sj_lt_commute) _ 1 1).
                  auto. lia.
                 }
              ++ apply upE_preserves_well_formedness2. lia.
                 eapply edc_preserves_well_formedness; eauto.
              ++ rewrite lift_ctx_preserves_length.
                 apply (proj1 (proj2 nfv_up_lt)); eauto; lia.
           -- eapply edc_preserves_well_formedness; eauto.
           -- assumption.
        ** unfold down.
           replace swap01 with (up_ren_n 0 swap01) by auto.
           assert (
            ~ 2 ∈ Q1
           ).
           {
            intro. inversion H3; subst. apply H20; apply fv_cut_l.
            eapply free_vars_under_struct_cong; eauto.
            apply directed_cong_in_struct_cong; eauto.
           }
           rewrite (proj1 up_ren_n_swap_down_down_Sn).
           -- simpl. replace (up_ren swap01) with (up_ren_n 1 swap01) by auto.
              rewrite (proj1 up_ren_n_swap_down_down_Sn).
              ++ rewrite (proj1 down_at_k_rename_id_after_k_commute); auto.
                 apply swap01_is_bijective. intros [|[|]] ?; auto; exfalso; lia.
              ++ replace 2 with (swap01 2) by auto. apply nfv_under_renaming; auto.
                 apply swap01_is_bijective.
           -- simpl.
              replace 1 with (up_ren swap01 2) by auto.
              apply nfv_under_renaming. apply shift_preserves_bijection; apply swap01_is_bijective.
              replace 2 with (swap01 2) by auto.
              apply nfv_under_renaming; auto. apply swap01_is_bijective.
        ** unfold down.
           assert (
            ~ 1 ∈ R1
           ). { apply directed_cong_in_struct_cong in H9. eapply nfv_under_struct_cong; eauto. }
           replace swap01 with (up_ren_n 0 swap01) by auto.
           repeat rewrite (proj1 up_ren_n_swap_down_down_Sn); eauto.
           -- rewrite (proj1 down_k_down_Sj_lt_commute2); auto.
           -- apply nfv_down_lt; auto.
           -- intro. apply n_fv_down_Sn' in H17; auto.
              assert (~ 2 ∈ R0). { intro. inversion H3; subst. apply H22; apply fv_cut_r; eauto. }
              apply directed_cong_in_struct_cong in H9.
              eapply nfv_under_struct_cong in H18; eauto.
    - assert (
        (rename_process (fill_hole E M) swap01) ⇛
          (rename_process P'0 swap01)
      ). { apply directed_cong_invariant_under_renaming; auto; apply swap01_is_bijective. }
      rewrite rename_axcut_ctx_over_fill_hole in H0; try apply swap01_is_bijective.
      assert (
        n >= length_axcut_ctx (rename_axcut_ctx E swap01)
      ). { rewrite <- rename_axcut_ctx_preserves_length; inversion H; lia. }
      assert (
        exists Γ',
          Γ' ⊢ (fill_hole (rename_axcut_ctx E swap01)
                          (rename_message M (up_ren_n (length_axcut_ctx E) swap01))) :#
      ) as Hwtfh.
      {
        simpl in H2; inversion H2; subst.
        destruct (swap01_preserves_well_typedness _ _ H12).
        eexists. rewrite rename_axcut_ctx_over_fill_hole in H7. eassumption.
        apply swap01_is_bijective.
      }
      destruct Hwtfh.
      assert (
        well_formed_axcut_ctx 0 (rename_axcut_ctx E swap01)
      ).
      {
        replace 0 with (swap01 1) by auto.
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01; auto.
        inversion H3; auto.
      }
      assert (
        (rename_process (up P) swap01) ⇛
          (rename_process (up P') swap01)
      ).
      {
        apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
        apply directed_cong_invariant_under_upshifting; auto.
      }
      destruct (IHn _ _ _ _ _ _ _ _
                      H1
                      eq_refl
                      eq_refl
                      H7
                      H9
                      H10
                      H0) as [E'' [M'' [? [? ?]]]].
      exists (cons_r (rename_axcut_ctx E'' swap01) Q').
      exists (rename_message M'' (up_ren_n (length_axcut_ctx E'') swap01)).
      repeat split.
      * simpl. f_equal.
        assert (
          rename_process (rename_process P'0 swap01) swap01
            = rename_process (fill_hole E'' M'') swap01
        ). { f_equal; auto. }
        rewrite swap_swap_id in H14. rewrite H14.
        rewrite <- rename_axcut_ctx_over_fill_hole; auto.
        apply swap01_is_bijective.
      * econstructor; eauto.
        apply (edc_invariant_under_renaming _ _ swap01 swap01_is_bijective) in H12.
        rewrite swap_swap_idE in H12. auto.
      * repeat rewrite reduce_axcut_equation_3.
        repeat rewrite reduce_axcut_equation_4.
        apply dc_cong_cut.
        ** rewrite swap_swap_idE.
           rewrite <- rename_axcut_ctx_preserves_length.
           rewrite up_ren_swap_swap_idM.
           assumption.
        ** apply directed_cong_invariant_under_downshifting; auto.
           -- apply directed_cong_invariant_under_renaming; auto.
              apply swap01_is_bijective.
           -- inversion H3; subst.
              apply nfv_01_swap; auto.
Qed.

Lemma reduce_axcut_invariant_under_directed_cong :
  forall Γ E M R Q P P',
    Q = fill_hole E M ->
    Γ ⊢ Q :# -> well_formed_axcut_ctx 0 E ->
    P ⇛ P' -> Q ⇛ R ->
      exists E' M',
        R = fill_hole E' M' /\
        E #⇛ E' /\
        (reduce_axcut E M P) ⇛ (reduce_axcut E' M' P').
Proof.
  intros. eapply reduce_axcut_invariant_under_directed_cong'; eauto.
Qed.
