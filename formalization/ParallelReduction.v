From FD Require Import Syntax.
From FD Require Import Reduction.
From FD Require Import FreeVars.
From FD Require Import Renaming.
From FD Require Import FreeVars.
From FD Require Import StructCong.
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

(* ↠* ∪ ▶ *)
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
