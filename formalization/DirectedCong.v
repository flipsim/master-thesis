From FD Require Import Syntax.
From FD Require Import FreeVars.
From FD Require Import Renaming.
From FD Require Import FreeVars.
From FD Require Import StructCong.
From FD Require Import ConfluenceDefs.

From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Relations.Operators_Properties.
From Stdlib Require Import Relation_Definitions.
From Stdlib Require Import Lia.

(* This file contains the definition of structural congruence that is
   used to define parallel reduction. Opposed to structural congruence,
   this relation is not symmetric by definition, hence we call it
   "directed congruence". It requires less congruence rules than ≡ which
   reduces the amount of case distinction to prove the diamond property
   for parallel reduction. Key properties include:

   (i)   Symmetry is admissable for directed congruence.
   (ii)  ≡ ⊂ ⇛^*
   (iii) ⇛ ⊂ ≡

   NB: If symmetry were to be added as a rule, then ⊵ would have to consider
   addtional AxCut rules in order to allow diverging reductions to reconciliate
   in one step. Thus, admissibility of symmetry helps to drastically reduce
   the amount of case distinctions.

   NB: ⇛ can be thought of as being able to perform multiple congruences
   at all, i.e. a parallel congruence (e.g. associating and commuting a cut
   in one step)
*)

(******************************************************************************)
(* Directed Structural Congruence (technical device for Church-Rosser)        *)
(******************************************************************************)
(* ⇛ (Rrightarrow)  *)
Reserved Notation "P '⇛' Q" (no associativity, at level 1).
Reserved Notation "M '!⇛' N" (no associativity, at level 1).
Reserved Notation "s '$⇛' r" (no associativity, at level 1).

Inductive directed_congruence : process -> process -> Prop :=
  (* links *)
  | dc_cong_link : forall ml1 ml2 mr1 mr2,
      ml1 !⇛ ml2 -> mr1 !⇛ mr2 -> (link ml1 mr1) ⇛ (link ml2 mr2)
  | dc_link : forall ml1 ml2 mr1 mr2,
      ml1 !⇛ ml2 -> mr1 !⇛ mr2 -> (link ml1 mr1) ⇛ (link mr2 ml2)

  (* cuts *)
  | dc_cut_comm : forall P P' Q Q', P ⇛ P' -> Q ⇛ Q' -> (cut P Q) ⇛ (cut Q' P')
  | dc_cut_assoc_l : forall P Q R P1 Q1 R1 P' Q' R',
      ~ (1 ∈ P) ->
      P ⇛ P1 -> Q ⇛ Q1 -> R ⇛ R1 ->
      P' = down (rename_process P1 swap01) ->
      Q' = rename_process Q1 swap01 ->
      R' = rename_process (up R1) swap01 ->
      (cut (cut P Q) R) ⇛ (cut P' (cut Q' R'))
  | dc_cut_assoc_r : forall P Q R P1 Q1 R1 P' Q' R',
      ~ (1 ∈ R) ->
      P ⇛ P1 -> Q ⇛ Q1 -> R ⇛ R1 ->
      P' = rename_process (up P1) swap01 ->
      Q' = rename_process Q1 swap01 ->
      R' = down (rename_process R1 swap01) ->
      (cut P (cut Q R)) ⇛ (cut (cut P' Q') R')
  | dc_cong_cut : forall P P' Q Q', P ⇛ P' -> Q ⇛ Q' -> (cut P Q) ⇛ (cut P' Q')

  (* seqs *)
  | dc_cong_seq : forall P P' s s', P ⇛ P' -> s $⇛ s' -> (seq P s) ⇛ (seq P' s')

  (* stop *)
  | dc_stop : stop ⇛ stop
where
  "P '⇛' Q" := (directed_congruence P Q)

with directed_congruence_message : message -> message -> Prop :=
  | dc_cong_prefix : forall s s', s $⇛ s' -> (prefix s) !⇛ (prefix s')
  | dc_cong_reflM : forall m, m !⇛ m
where
  "M '!⇛' N" := (directed_congruence_message M N)

with directed_congruence_statement : statement -> statement -> Prop :=
  | dc_cong_choose_l : forall P P',
                        P ⇛ P' ->
                        (choose_left P) $⇛ (choose_left P')
  | dc_cong_choose_r : forall P P',
                        P ⇛ P' ->
                        (choose_right P) $⇛ (choose_right P')
  | dc_cong_choice : forall P P' Q Q',
                      P ⇛ P' -> Q ⇛ Q' -> (offer_choice P Q) $⇛ (offer_choice P' Q')
  | dc_cong_send : forall P P' Q Q',
                    P ⇛ P' -> Q ⇛ Q' -> (send P Q) $⇛ (send P' Q')
  | dc_cong_receive : forall P P', P ⇛ P' -> (receive P) $⇛ (receive P')
  | dc_cong_close : close $⇛ close
  | dc_cong_wait : forall P P', P ⇛ P' -> (wait P) $⇛ (wait P')
  | dc_cong_reflS : forall s, s $⇛ s
where
  "s '$⇛' r" := (directed_congruence_statement s r).

(* Mutual induction principle for directed congruence *)
Scheme directed_congP_ind := Induction for directed_congruence Sort Prop
  with directed_congM_ind := Induction for directed_congruence_message Sort Prop
  with directed_congS_ind := Induction for directed_congruence_statement Sort Prop.
Combined Scheme directed_cong_ind from directed_congP_ind, directed_congM_ind, directed_congS_ind.

Local Hint Rewrite
  swap_swap_id
  down_after_up_process_id
  up_after_down_process_id
    : up_down_rename_rewrites.

Lemma directed_cong_reflexive :
  forall P, P ⇛ P.
Proof.
  intros. induction P.
  + apply dc_cong_link; apply dc_cong_reflM.
  + apply dc_cong_cut; auto.
  + apply dc_cong_seq; auto. apply dc_cong_reflS.
  + econstructor.
Qed.

(******************************************************************************)
(* Specialized inversion                                                      *)
(******************************************************************************)
Lemma directed_cong_inversion_prefix :
  forall s m, (prefix s) !⇛ m -> exists s', m = prefix s' /\ s $⇛ s'.
Proof. intros. inversion H; subst; eauto. exists s. split; eauto. apply dc_cong_reflS. Qed.

Lemma directed_cong_inversion_send :
  forall P Q s, (send P Q) $⇛ s ->
    exists P' Q', s = send P' Q' /\ P ⇛ P' /\ Q ⇛ Q'.
Proof. intros. inversion H; subst; eauto. eexists; eexists; split; auto; split; apply directed_cong_reflexive. Qed.

Lemma directed_cong_inversion_receive :
  forall P s, (receive P) $⇛ s -> exists P', s = receive P' /\ P ⇛ P'.
Proof. intros. inversion H; subst; eauto. eexists; split; auto. apply directed_cong_reflexive. Qed.

Lemma directed_cong_inversion_choosel :
  forall P s, (choose_left P) $⇛ s -> exists P', s = choose_left P' /\ P ⇛ P'.
Proof. intros. inversion H; subst; eauto. eexists; split; auto. apply directed_cong_reflexive. Qed.

Lemma directed_cong_inversion_chooser :
  forall P s, (choose_right P) $⇛ s -> exists P', s = choose_right P' /\ P ⇛ P'.
Proof. intros. inversion H; subst; eauto. eexists; split; auto. apply directed_cong_reflexive. Qed.

Lemma directed_cong_inversion_choice :
  forall P Q s, (offer_choice P Q) $⇛ s ->
    exists P' Q', s = offer_choice P' Q' /\ P ⇛ P' /\ Q ⇛ Q'.
Proof. intros. inversion H; subst; eauto. eexists; eexists; split; auto; split; apply directed_cong_reflexive. Qed.

Lemma directed_cong_inversion_close :
  forall s, close $⇛ s -> s = close.
Proof. intros. inversion H; subst; auto. Qed.

Lemma directed_cong_inversion_wait :
  forall P s, (wait P) $⇛ s -> exists P', s = wait P' /\ P ⇛ P'.
Proof. intros. inversion H; subst; eauto. eexists; split; auto. apply directed_cong_reflexive. Qed.

(******************************************************************************)
(* Properties about directed congruence                                       *)
(******************************************************************************)

(* ⇛ ⊂ ≡ *)
Lemma directed_cong_in_struct_cong :
  (forall P Q, P ⇛ Q -> P ≡ Q) /\
  (forall M N, M !⇛ N -> M !≡ N) /\
  (forall s t, s $⇛ t -> s $≡ t).
Proof.
  apply directed_cong_ind; intros; try (now (econstructor; eauto)).
  + eapply c_trans. apply c_link. apply c_cong_link; auto.
  + eapply c_trans. apply c_cut_comm. apply c_cong_cut; auto.
  + eapply c_trans.
    - eapply c_cong_cut; eauto. eapply c_cong_cut; eauto.
    - subst; apply c_cut_assoc; auto. intro Hfv. apply c_comm in H.
      apply ((proj1 free_vars_under_struct_cong) _ _ H _) in Hfv. congruence.
  + apply c_comm. eapply c_trans.
    - eapply c_cut_assoc; auto. rewrite e. apply nfv_10_swap. apply nfv_lift_n; lia.
    - subst; autorewrite with up_down_rename_rewrites.
      * apply c_cong_cut. apply c_comm; auto. apply c_cong_cut; apply c_comm; auto.
      * apply nfv_01_swap. intro Hfv. apply c_comm in H1.
        apply ((proj1 free_vars_under_struct_cong) _ _ H1 _) in Hfv. congruence.
  + apply struct_cong_reflM.
  + apply struct_cong_reflS.
Qed.

Lemma ren_up_up_ren_commute :
  (forall P, forall r k,
    bijective r -> (forall j, j < k -> r j = j) ->
    rename_process (lift_process P k 1) (up_ren r)
      = lift_process (rename_process P r) k 1)
  /\
  (forall M, forall r k,
    bijective r -> (forall j, j < k -> r j = j) ->
    rename_message (lift_message M k 1) (up_ren r)
      = lift_message (rename_message M r) k 1)
  /\
  (forall s, forall r k,
    bijective r -> (forall j, j < k -> r j = j) ->
    rename_statement (lift_statement s k 1) (up_ren r)
      = lift_statement (rename_statement s r) k 1).
Proof.
  apply syntax_ind; intros; simpl;
  assert (bijective (up_ren r)) by (apply shift_preserves_bijection; auto);
  try assert (forall j : nat, j < S k -> up_ren r j = j) by 
    (intros; unfold up_ren; destruct j; auto; try rewrite H0; try rewrite H1; try rewrite H2; lia);
  try now (try rewrite H; try rewrite H0; auto).
  + unfold relocate.
    destruct (Nat.leb k n) eqn:E.
    - simpl.
      apply PeanoNat.Nat.leb_le in E.
      destruct (Nat.leb k (r n)) eqn:E1; auto.
      exfalso.
      apply PeanoNat.Nat.leb_nle in E1.
      assert (r n < k) by lia.
      assert (r (r n) = (r n)) by (rewrite H0; auto).
      destruct H.
      assert (g (r (r n)) = g (r n)). { rewrite H4; auto. }
      repeat rewrite c in H. lia.
    - apply PeanoNat.Nat.leb_nle in E.
      assert (n < k) by lia.
      assert (n < (S k)) by lia.
      destruct (Nat.leb k (r n)) eqn:E1.
      * exfalso.
        apply PeanoNat.Nat.leb_le in E1.
        rewrite (H0 _ H3) in E1. lia.
      * repeat rewrite (H2 _ H4). rewrite (H0 _ H3). reflexivity.
  + rewrite (H (up_ren (up_ren r))); auto.
    repeat apply shift_preserves_bijection; auto.
    intros. destruct j as [|[|]]; simpl; try lia. rewrite H1; lia.
Qed.

Lemma down_ren_up_ren_commute :
  (forall P, forall r k,
    bijective r -> (forall j, j < k -> r j = j) ->
    ~ (k ∈ P) ->
    down1_process (rename_process P (up_ren r)) k =
    rename_process (down1_process P k) r) /\
  (forall M, forall r k,
    bijective r -> (forall j, j < k -> r j = j) ->
    ~ (occurs_free_message k M) ->
    down1_message (rename_message M (up_ren r)) k =
    rename_message (down1_message M k) r) /\
  (forall s, forall r k,
    bijective r -> (forall j, j < k -> r j = j) ->
    ~ (occurs_free_statement k s) ->
    down1_statement (rename_statement s (up_ren r)) k =
    rename_statement (down1_statement s k) r).
Proof.
  apply syntax_ind; intros; simpl;
  assert (bijective (up_ren r)) by (apply shift_preserves_bijection; auto);
  try assert (forall j : nat, j < S k -> up_ren r j = j) by 
    (intros; unfold up_ren; destruct j; auto; try rewrite H0; try rewrite H1; try rewrite H2; lia);
  try now (try rewrite H; try rewrite H0; auto).
  + rewrite H. rewrite H0; auto. all: auto.
    - intro Hnfv. destruct (((proj1 (proj2 free_vars_decidable))) m0 k); auto.
      apply H3. free_var_econstructor; auto.
    - intro Hnfv. destruct (((proj1 (proj2 free_vars_decidable))) m k); auto.
      apply H3. free_var_econstructor; auto.
  + rewrite H. rewrite H0; auto. all: auto.
    - intro Hnfv. destruct (((proj1 free_vars_decidable)) p0 (S k)); auto.
      apply H3. free_var_econstructor; auto.
    - intro Hnfv. destruct (((proj1 free_vars_decidable)) p (S k)); auto.
      apply H3. free_var_econstructor; auto.
  + rewrite H. rewrite H0; auto. all: auto.
    - intro Hnfv. destruct (((proj2 (proj2 free_vars_decidable))) s k); auto.
      apply H3. free_var_econstructor; auto.
    - intro Hnfv. destruct (((proj1 free_vars_decidable)) p (S k)); auto.
      apply H3. free_var_econstructor; auto.
  + assert (k <> n). { intro Hneq. subst. apply H1. econstructor. }
    destruct (Nat.ltb k n) eqn:E.
    - apply PeanoNat.Nat.ltb_lt in E. destruct n; try (exfalso; lia).
      simpl.
      destruct (Nat.ltb k (S (r n))) eqn:E1; auto.
      exfalso. apply PeanoNat.Nat.ltb_nlt in E1.
      assert (r n < k) by lia.
      assert (r (r n) = (r n)) by (rewrite H0; auto).
      destruct H.
      assert (g (r (r n)) = g (r n)). { rewrite H6; auto. }
      repeat rewrite c in H. lia.
    - apply PeanoNat.Nat.ltb_nlt in E.
      assert (n < k) by lia.
      assert (n < S k) by lia.
      rewrite (H3 _ H6). apply PeanoNat.Nat.ltb_nlt in E. rewrite E.
      simpl. rewrite (H0 _ H5). reflexivity.
  + rewrite H; auto. intro Hnfv. destruct (((proj2 (proj2 free_vars_decidable))) s k); auto.
    apply H2; free_var_econstructor; auto.
  + rewrite H; auto. intro Hnfv. destruct (((proj1 free_vars_decidable)) p (S k)); auto.
    apply H2; free_var_econstructor; auto.
  + rewrite H; auto. intro Hnfv. destruct (((proj1 free_vars_decidable)) p (S k)); auto.
    apply H2; free_var_econstructor; auto.
  + rewrite H. rewrite H0; auto. all: auto.
    - intro Hnfv. destruct (((proj1 free_vars_decidable)) p0 (S k)); auto.
      apply H3. free_var_econstructor; auto.
    - intro Hnfv. destruct (((proj1 free_vars_decidable)) p (S k)); auto.
      apply H3. free_var_econstructor; auto.
  + rewrite H. rewrite H0; auto. all: auto.
    - intro Hnfv. destruct (((proj1 free_vars_decidable)) p0 (S k)); auto.
      apply H3. free_var_econstructor; auto.
    - intro Hnfv. destruct (((proj1 free_vars_decidable)) p (S k)); auto.
      apply H3. free_var_econstructor; auto.
  + rewrite (H (up_ren (up_ren r))); auto.
    - repeat apply shift_preserves_bijection; auto.
    - intros [|[|]] ?; simpl; auto. assert (n < k) by lia.
      rewrite (H1 _ H6). auto.
    - intro Hnfv. destruct (((proj1 free_vars_decidable)) p (S (S k))); auto.
      apply H2; free_var_econstructor; auto.
  + rewrite H; auto. intro Hnfv. destruct (((proj1 free_vars_decidable)) p k); auto.
    apply H2; free_var_econstructor; auto.
Qed.

Lemma directed_cong_invariant_under_renaming :
  (forall P Q, P ⇛ Q -> forall r, bijective r -> (rename_process P r) ⇛ (rename_process Q r))
  /\
  (forall M N, M !⇛ N -> forall r, bijective r -> (rename_message M r) !⇛ (rename_message N r))
  /\
  (forall s t, s $⇛ t -> forall r, bijective r -> (rename_statement s r) $⇛ (rename_statement t r)).
Proof.
  apply directed_cong_ind; intros; try (now (simpl; econstructor; eauto));
  try (now (simpl; econstructor; try apply H; try apply H0; auto;
       try apply shift_preserves_bijection;try apply shift_preserves_bijection;  auto)).
  + simpl. subst. eapply dc_cut_assoc_l.
    - replace 1 with ((up_ren (up_ren r)) 1) by auto. apply nfv_under_renaming; auto.
      repeat apply shift_preserves_bijection; auto.
    - apply H; repeat apply shift_preserves_bijection; auto.
    - apply H0; repeat apply shift_preserves_bijection; auto.
    - apply H1; repeat apply shift_preserves_bijection; auto.
    - assert (
        (rename_process (down (rename_process P1 swap01)) (up_ren r)) =
        (down (rename_process (rename_process P1 swap01) (up_ren (up_ren r))))
      ).
      {
        unfold down. rewrite <- (proj1 down_ren_up_ren_commute); auto.
        + apply shift_preserves_bijection; auto.
        + intros [|[|]] ?; exfalso; lia.
        + apply nfv_01_swap; auto. intro Hfv. apply directed_cong_in_struct_cong in d.
          apply c_comm in d. apply ((proj1 free_vars_under_struct_cong) _ _ d) in Hfv; congruence.
      }
      rewrite H3.
      assert (
        rename_process (rename_process P1 (up_ren (up_ren r))) swap01 =
        rename_process (rename_process P1 swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H4. auto.
    - assert (
        rename_process (rename_process Q1 (up_ren (up_ren r))) swap01 =
        rename_process (rename_process Q1 swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H3. auto.
    - assert (
        (rename_process (rename_process (up R1) swap01) (up_ren (up_ren r))) =
        (rename_process (rename_process (up R1) (up_ren (up_ren r))) swap01)
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H3.
      assert (
        up (rename_process R1 (up_ren r)) =
        rename_process (up R1) (up_ren (up_ren r))
      ).
      {
        unfold up.
        rewrite (proj1 ren_up_up_ren_commute); auto.
        + apply shift_preserves_bijection; auto.
        + intros. exfalso; lia.
      }
      rewrite H4. auto.
  + eapply dc_cut_assoc_r; fold rename_process.
    - replace 1 with ((up_ren (up_ren r)) 1) by auto.
      apply nfv_under_renaming; auto. repeat apply shift_preserves_bijection; auto.
    - apply H. apply shift_preserves_bijection; auto.
    - apply H0; repeat apply shift_preserves_bijection; auto.
    - apply H1; repeat apply shift_preserves_bijection; auto.
    - rewrite e.
      assert (
        rename_process (rename_process (up P1) (up_ren (up_ren r))) swap01 =
        rename_process (rename_process (up P1) swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite <- H3.
      assert (
        up (rename_process P1 (up_ren r)) =
        rename_process (up P1) (up_ren (up_ren r))
      ).
      {
        unfold up.
        rewrite (proj1 ren_up_up_ren_commute); auto.
        + apply shift_preserves_bijection; auto.
        + intros. exfalso; lia.
      }
      rewrite H4. auto.
    - rewrite e0.
      rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
      rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
      reflexivity. all: intros[|[|]]; auto.
    - rewrite e1.
      assert (
        rename_process (rename_process R1 (up_ren (up_ren r))) swap01 =
        rename_process (rename_process R1 swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H3.
      assert (
        (rename_process (down (rename_process R1 swap01)) (up_ren r)) =
        (down (rename_process (rename_process R1 swap01) (up_ren (up_ren r))))
      ).
      {
        unfold down. rewrite <- (proj1 down_ren_up_ren_commute); auto.
        + apply shift_preserves_bijection; auto.
        + intros [|[|]] ?; exfalso; lia.
        + apply nfv_01_swap; auto. intro Hfv. apply directed_cong_in_struct_cong in d1.
          apply c_comm in d1. apply ((proj1 free_vars_under_struct_cong) _ _ d1) in Hfv; congruence.
      }
      rewrite H4. auto.
Qed.

Lemma lift_after_down_lt_commute :
  (forall P,
    forall k1 k2, k2 < k1 ->
      lift_process (down1_process P k2) k1 1
        = down1_process (lift_process P (S k1) 1) k2) /\
  (forall M,
    forall k1 k2, k2 < k1 ->
      lift_message (down1_message M k2) k1 1
        = down1_message (lift_message M (S k1) 1) k2) /\
  (forall s,
    forall k1 k2, k2 < k1 ->
      lift_statement (down1_statement s k2) k1 1
        = down1_statement (lift_statement s (S k1) 1) k2).
Proof.
  apply syntax_ind; intros; simpl; auto;
    try (now (rewrite (H (S k1) (S k2)); try lia; auto));
    try (now (rewrite (H (S k1) (S k2)); try lia; rewrite (H0 (S k1) (S k2)); try lia; auto)).
  + rewrite H; auto. rewrite H0; auto.
  + rewrite (H (S k1) (S k2)); try lia. rewrite (H0 k1 k2); try lia. auto.
  + unfold relocate.
    destruct (Nat.leb (S k1) n) eqn:E.
    - simpl. apply PeanoNat.Nat.leb_le in E.
      assert (k2 < n) by lia. apply PeanoNat.Nat.ltb_lt in H0.
      assert (k2 < S n) by lia. apply PeanoNat.Nat.ltb_lt in H1.
      rewrite H0, H1. destruct n; try (exfalso; lia). simpl.
      unfold relocate. assert (k1 <= n) by lia.
      apply PeanoNat.Nat.leb_le in H2. rewrite H2; reflexivity.
    - apply PeanoNat.Nat.leb_nle in E.
      assert (n <= k1) by lia.
      destruct (Nat.ltb k2 n) eqn:E1.
      * simpl. unfold relocate.
        assert (~ (k1 <= (Nat.pred n))) by lia.
        apply PeanoNat.Nat.leb_nle in H1. rewrite H1. reflexivity.
      * simpl. unfold relocate.
        apply PeanoNat.Nat.ltb_nlt in E1.
        destruct (PeanoNat.Nat.eq_dec n k1).
        ++ exfalso. lia.
        ++ assert (~ (k1 <= n)) by lia. apply PeanoNat.Nat.leb_nle in H1. rewrite H1. reflexivity.
  + rewrite H; auto.
  + rewrite (H (S (S k1)) (S (S k2))); try lia; auto.
  + rewrite (H k1 k2); try lia; auto.
Qed.

Lemma down_after_down_gt_commute :
  (forall P,
    forall k1 k2, k1 < (S k2) ->
      down1_process (lift_process P k1 1) (S (S k2))
        = lift_process (down1_process P (S k2)) k1 1) /\
  (forall M,
    forall k1 k2, k1 < (S k2) ->
      down1_message (lift_message M k1 1) (S (S k2))
        = lift_message (down1_message M (S k2)) k1 1) /\
  (forall s,
    forall k1 k2, k1 < (S k2) ->
      down1_statement (lift_statement s k1 1) (S (S k2))
        = lift_statement (down1_statement s (S k2)) k1 1).
Proof.
  apply syntax_ind; intros; simpl; auto;
    try (now (rewrite (H (S k1) (S k2)); try lia; auto));
    try (now (rewrite (H (S k1) (S k2)); try lia; rewrite (H0 (S k1) (S k2)); try lia; auto)).
  + rewrite H; auto. rewrite H0; auto.
  + rewrite (H (S k1) (S k2)); try lia. rewrite (H0 k1 k2); try lia. auto.
  + destruct (Nat.ltb (S k2) n) eqn:E.
    - simpl. unfold relocate. apply PeanoNat.Nat.ltb_lt in E.
      assert (k1 <= n) by lia. assert (k1 <= Nat.pred n) by lia.
      apply PeanoNat.Nat.leb_le in H0.
      apply PeanoNat.Nat.leb_le in H1.
      rewrite H0, H1. simpl. assert (S (S k2) < (S n)) by lia.
      apply PeanoNat.Nat.ltb_lt in H2. rewrite H2. destruct n; try (exfalso; lia).
      simpl. auto.
    - simpl. unfold relocate. apply PeanoNat.Nat.ltb_nlt in E.
      destruct (Nat.leb k1 n) eqn:E1.
      * simpl. assert (~ (S (S k2)) < (S n)) by lia. apply PeanoNat.Nat.ltb_nlt in H0.
        rewrite H0; auto.
      * apply PeanoNat.Nat.leb_nle in E1. assert (~ S (S k2) < n) by lia.
        apply PeanoNat.Nat.ltb_nlt in H0. rewrite H0. auto.
  + rewrite H; auto.
  + rewrite (H (S (S k1)) (S (S k2))); try lia; auto.
  + rewrite (H k1 k2); try lia; auto.
Qed.

Lemma lift_at_k_rename_id_after_k_commute :
  (forall P,
    forall k r, bijective r -> (forall j, k <= j -> r j = j) ->
      lift_process (rename_process P r) k 1
        = rename_process (lift_process P k 1) r) /\
  (forall M,
    forall k r, bijective r -> (forall j, k <= j -> r j = j) ->
      lift_message (rename_message M r) k 1
        = rename_message (lift_message M k 1) r) /\
  (forall s,
    forall k r, bijective r -> (forall j, k <= j -> r j = j) ->
      lift_statement (rename_statement s r) k 1
        = rename_statement (lift_statement s k 1) r).
Proof.
  apply syntax_ind; intros; simpl; auto;
  assert (bijective (up_ren r)) by (apply shift_preserves_bijection; auto);
  try assert (forall j : nat, S k <= j -> up_ren r j = j) by
    (intros; unfold up_ren; destruct j; auto; try rewrite H0; try rewrite H1; try rewrite H2; lia);
  try (now (try rewrite H; try rewrite H0; auto)).
  + unfold relocate.
    simpl. destruct (Nat.leb k n) eqn:E.
    * rewrite (H0 n); auto; try rewrite E;
      apply PeanoNat.Nat.leb_le in E; try lia.
      rewrite (H0 (S n)); auto.
    * destruct (Nat.leb k (r n)) eqn:E1; auto.
      apply PeanoNat.Nat.leb_nle in E. assert (k > n) by lia.
      apply PeanoNat.Nat.leb_le in E1.
      destruct (Compare_dec.le_gt_dec k n).
      ++ exfalso. lia.
      ++ exfalso.
         destruct H.
         assert (r n = n).
         {
          specialize H0 with (r n). apply H0 in E1.
          assert (g0 (r (r n)) = g0 (r n)) by (rewrite E1; auto).
          repeat rewrite c in H. auto.
         }
         rewrite H in E1. congruence.
  + rewrite (H (S (S k)) (up_ren (up_ren r))); auto.
    * repeat apply shift_preserves_bijection; auto.
    * intros [|[|]] ?; auto. simpl. rewrite H1; try lia.
Qed.

Lemma down_at_k_rename_id_after_k_commute :
  (forall P,
    forall k r, bijective r -> (forall j, k <= j -> r j = j) ->
      down1_process (rename_process P r) k
        = rename_process (down1_process P k) r) /\
  (forall M,
    forall k r, bijective r -> (forall j, k <= j -> r j = j) ->
      down1_message (rename_message M r) k
        = rename_message (down1_message M k) r) /\
  (forall s,
    forall k r, bijective r -> (forall j, k <= j -> r j = j) ->
      down1_statement (rename_statement s r) k
        = rename_statement (down1_statement s k) r).
Proof.
  apply syntax_ind; intros; simpl; auto;
  assert (bijective (up_ren r)) by (apply shift_preserves_bijection; auto);
  try assert (forall j : nat, S k <= j -> up_ren r j = j) by
    (intros; unfold up_ren; destruct j; auto; try rewrite H0; try rewrite H1; try rewrite H2; lia);
  try (now (try rewrite H; try rewrite H0; auto)).
  + destruct (Nat.ltb k n) eqn:E; simpl.
    - apply PeanoNat.Nat.ltb_lt in E.
      assert (Nat.ltb k n = true) by (apply PeanoNat.Nat.ltb_lt in E; auto).
      destruct n; try (exfalso; lia). simpl.
      assert (k <= (S n)) by lia. rewrite (H0 (S n)); auto. simpl.
      rewrite H3. rewrite H0; auto. lia.
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
          repeat rewrite c in H4. auto.
         }
         rewrite H in E1. congruence.
  + rewrite (H (S (S k)) (up_ren (up_ren r))); auto.
    * repeat apply shift_preserves_bijection; auto.
    * intros [|[|]] ?; auto. simpl. rewrite H1; try lia.
Qed.

Lemma lift_k_lift_Sj_lt_commute :
  (forall P,
    forall k j, k < S j ->
      lift_process (lift_process P k 1) (S j) 1
        = lift_process (lift_process P j 1) k 1) /\
  (forall M,
    forall k j, k < S j ->
      lift_message (lift_message M k 1) (S j) 1
        = lift_message (lift_message M j 1) k 1) /\
  (forall s,
    forall k j, k < S j ->
      lift_statement (lift_statement s k 1) (S j) 1
        = lift_statement (lift_statement s j 1) k 1).
Proof.
  apply syntax_ind; intros; simpl; auto;
  try (now (rewrite H; auto; rewrite H0; auto));
  try (now (rewrite (H (S k) (S j)); try lia; auto; rewrite (H0 (S k) (S j)); try lia; auto)).
  + rewrite (H (S k) (S j)); try lia. rewrite H0; auto.
  + unfold relocate. destruct (Nat.leb j n) eqn:E.
    - apply PeanoNat.Nat.leb_le in E. simpl.
      assert (k <= S n) by lia. apply PeanoNat.Nat.leb_le in H0. rewrite H0.
      destruct (Compare_dec.le_gt_dec k n).
      * apply PeanoNat.Nat.leb_le in l. rewrite l.
        assert (j <= n) by lia. apply PeanoNat.Nat.leb_le in H1. rewrite H1; auto.
      * apply PeanoNat.Nat.leb_le in H0. exfalso. lia.
    - apply PeanoNat.Nat.leb_nle in E. simpl.
      destruct (Compare_dec.le_gt_dec k n).
      * apply PeanoNat.Nat.leb_le in l. rewrite l. assert (~ (j <= n)) by lia.
        apply PeanoNat.Nat.leb_nle in H0. rewrite H0. auto.
      * assert (~ (k <= n)) by lia. apply PeanoNat.Nat.leb_nle in H0. rewrite H0.
        destruct n; auto. assert (~ (j <= n)) by lia. apply PeanoNat.Nat.leb_nle in H1.
        rewrite H1; auto.
  + rewrite (H (S (S k)) (S (S j))); try lia. auto.
Qed.

Lemma down_k_down_Sj_lt_commute :
  (forall P,
    forall k j, k < S j ->
      down1_process (down1_process P k) (S j)
        = down1_process (down1_process P (S (S j))) k) /\
  (forall M,
    forall k j, k < S j ->
      down1_message (down1_message M k) (S j)
        = down1_message (down1_message M (S (S j))) k) /\
  (forall s,
    forall k j, k < S j ->
      down1_statement (down1_statement s k) (S j)
        = down1_statement (down1_statement s (S (S j))) k).
Proof.
  apply syntax_ind; intros; simpl; auto;
  try (now (rewrite H; auto; rewrite H0; auto));
  try (now (rewrite (H (S k) (S j)); try lia; auto; rewrite (H0 (S k) (S j)); try lia; auto)).
  + rewrite (H (S k) (S j)); try lia. rewrite H0; auto.
  + destruct (Nat.ltb (S (S j)) n) eqn:E.
    - apply PeanoNat.Nat.ltb_lt in E. assert (k < n) by lia.
      apply PeanoNat.Nat.ltb_lt in H0. rewrite H0. destruct n; try (exfalso; lia).
      simpl. assert (S j < n) by lia. apply PeanoNat.Nat.ltb_lt in H1. rewrite H1.
      assert (k < n) by lia. apply PeanoNat.Nat.ltb_lt in H2. rewrite H2. auto.
    - apply PeanoNat.Nat.ltb_nlt in E. simpl.
      destruct (Nat.ltb k n) eqn:E1.
      * apply PeanoNat.Nat.ltb_lt in E1; destruct n; try (exfalso; lia).
        simpl. assert (~ (S j < n)) by lia. apply PeanoNat.Nat.ltb_nlt in H0.
        rewrite H0; auto.
      * apply PeanoNat.Nat.ltb_nlt in E1. simpl.
        assert (~ (S j < n)) by lia. apply PeanoNat.Nat.ltb_nlt in H0. rewrite H0; auto.
  + rewrite (H (S (S k)) (S (S j))); try lia. auto.
Qed.

Lemma directed_cong_invariant_under_upshifting :
  (forall P Q, P ⇛ Q -> forall k, (lift_process P k 1) ⇛ (lift_process Q k 1)) /\
  (forall M N, M !⇛ N -> forall k, (lift_message M k 1) !⇛ (lift_message N k 1)) /\
  (forall s t, s $⇛ t -> forall k, (lift_statement s k 1) $⇛ (lift_statement t k 1)).
Proof.
  apply directed_cong_ind; intros; try now (econstructor; eauto).
  + simpl; subst. eapply dc_cut_assoc_l.
    - apply nfv_up_lt; auto; lia.
    - apply H.
    - apply H0.
    - apply H1.
    - unfold down.
      rewrite (proj1 lift_after_down_lt_commute); try lia.
      rewrite (proj1 lift_at_k_rename_id_after_k_commute); auto. apply swap01_is_bijective.
      intros [|[|]] ?; auto; exfalso; lia.
    - rewrite <- (proj1 lift_at_k_rename_id_after_k_commute); auto; try apply swap01_is_bijective.
      intros [|[|]] ?; auto; exfalso; lia.
    - unfold up. rewrite <- (proj1 lift_k_lift_Sj_lt_commute); try lia.
      rewrite (proj1 lift_at_k_rename_id_after_k_commute); try apply swap01_is_bijective; auto.
      intros [|[|]] ?; auto; exfalso; lia.
  + simpl; subst. eapply dc_cut_assoc_r.
    - apply nfv_up_lt; auto; lia.
    - apply H.
    - apply H0.
    - apply H1.
    - unfold up. rewrite <- (proj1 lift_k_lift_Sj_lt_commute); try lia.
      rewrite (proj1 lift_at_k_rename_id_after_k_commute); try apply swap01_is_bijective; auto.
      intros [|[|]] ?; auto; exfalso; lia.
    - rewrite <- (proj1 lift_at_k_rename_id_after_k_commute); auto; try apply swap01_is_bijective.
      intros [|[|]] ?; auto; exfalso; lia.
    - unfold down.
      rewrite (proj1 lift_after_down_lt_commute); try lia.
      rewrite (proj1 lift_at_k_rename_id_after_k_commute); auto. apply swap01_is_bijective.
      intros [|[|]] ?; auto; exfalso; lia.
Qed.

Lemma directed_cong_invariant_under_downshifting :
  (forall P Q, P ⇛ Q -> forall k,
    (~ k ∈ P) -> ((down1_process P k) ⇛ (down1_process Q k))) /\
  (forall M N, M !⇛ N -> forall k,
    (~ (occurs_free_message k M)) -> ((down1_message M k) !⇛ (down1_message N k))) /\
  (forall s t, s $⇛ t -> forall k,
    (~ (occurs_free_statement k s)) -> ((down1_statement s k) $⇛ (down1_statement t k))).
Proof.
  apply directed_cong_ind; intros; simpl; try (now (econstructor));
  try match goal with
  | [ IH1 : forall _, ~ _ -> (down1_message ?ml1 _) !⇛ (down1_message ?ml2 _),
      IH2 : forall _, ~ _ -> (down1_message ?mr1 _) !⇛ (down1_message ?mr2 _),
      H   : ~ _
      |- _ ]
    => econstructor; try apply IH1; try apply IH2; intro Hfv; apply H; free_var_econstructor; auto
  | [ IH1 : forall _, ~ _ -> (down1_process ?pl1 _) ⇛ (down1_process ?pl2 _),
      IH2 : forall _, ~ _ -> (down1_process ?pr1 _) ⇛ (down1_process ?pr2 _),
      k   : nat,
      H   : ~ _
      |- _ ]
    => econstructor; try apply (IH1 (S k)); try apply (IH2 (S k)); intro Hfv; apply H; free_var_econstructor; auto
  | [ IH1 : forall _, ~ _ -> (down1_process ?pl1 _) ⇛ (down1_process ?pl2 _),
      k   : nat,
      H   : ~ _
      |- _ ]
    => econstructor; try apply (IH1 (S k)); try apply IH1; intro Hfv; apply H; free_var_econstructor; auto
  end.
  + eapply dc_cut_assoc_l; subst.
    - apply nfv_down_lt; auto; lia.
    - apply H. intro Hfv. apply H2. repeat free_var_econstructor; auto.
    - apply H0. intro Hfv. apply H2. repeat free_var_econstructor; auto.
    - apply H1. intro Hfv. apply H2. repeat free_var_econstructor; auto.
    - unfold down.
      rewrite <- (proj1 down_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      rewrite (proj1 down_k_down_Sj_lt_commute); auto; try lia.
      intros [|[|]] ?; auto; exfalso; lia.
    - rewrite <- (proj1 down_at_k_rename_id_after_k_commute); auto; try apply swap01_is_bijective.
      intros [|[|]] ?; auto; exfalso; lia.
    - unfold up.
      rewrite (proj1 down_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      rewrite <- (proj1 down_after_down_gt_commute); try lia. auto.
      intros [|[|]] ?; eauto; exfalso; lia.
  + eapply dc_cut_assoc_r; subst.
    - apply nfv_down_lt; auto; lia.
    - apply H. intro Hfv. apply H2. repeat free_var_econstructor; auto.
    - apply H0. intro Hfv. apply H2. apply fv_cut_r. free_var_econstructor; auto.
    - apply H1. intro Hfv. apply H2. apply fv_cut_r; apply fv_cut_r; auto.
    - unfold up.
      rewrite (proj1 down_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      rewrite <- (proj1 down_after_down_gt_commute); try lia. auto.
      intros [|[|]] ?; eauto; exfalso; lia.
    - rewrite <- (proj1 down_at_k_rename_id_after_k_commute); auto; try apply swap01_is_bijective.
      intros [|[|]] ?; auto; exfalso; lia.
    - unfold down.
      rewrite <- (proj1 down_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      rewrite (proj1 down_k_down_Sj_lt_commute); auto; try lia.
      intros [|[|]] ?; auto; exfalso; lia.
  + econstructor; try apply (H (S k)); try apply H0; intro Hfv; apply H1; free_var_econstructor; auto.
  + econstructor; apply H; intro Hfv; apply H0; free_var_econstructor; auto.
Qed.

(******************************************************************************)
(* Symmetry is admissible                                                     *)
(******************************************************************************)
Lemma directed_cong_symm :
  (forall P1 P2, P1 ⇛ P2 -> P2 ⇛ P1) /\
  (forall M1 M2, M1 !⇛ M2 -> M2 !⇛ M1) /\
  (forall s1 s2, s1 $⇛ s2 -> s2 $⇛ s1).
Proof.
  apply directed_cong_ind; intros; try now (econstructor; eauto).
  + assert ((rename_process Q1 swap01) ⇛ (rename_process Q swap01)).
    { apply directed_cong_invariant_under_renaming; auto. apply swap01_is_bijective. }
    assert ((rename_process (up R1) swap01) ⇛ (rename_process (up R) swap01)).
    {
      apply directed_cong_invariant_under_renaming.
      + apply (proj1 directed_cong_invariant_under_upshifting); auto.
      + apply swap01_is_bijective.
    }
    replace P with
      (rename_process (up (down (rename_process P swap01))) swap01)
      by (autorewrite with up_down_rename_rewrites; try eapply nfv_01_swap; eauto).
    replace Q with
      (rename_process (rename_process Q swap01) swap01)
      by (autorewrite with up_down_rename_rewrites; eauto).
    replace R with
      (down (rename_process (rename_process (up R) swap01) swap01))
      by (autorewrite with up_down_rename_rewrites; eauto).
    subst.
    eapply dc_cut_assoc_r; eauto. apply nfv_10_swap. apply nfv_lift_n. lia.
    apply directed_cong_invariant_under_downshifting.
    apply directed_cong_invariant_under_renaming; auto. apply swap01_is_bijective.
    apply nfv_01_swap. intro Hfv. apply directed_cong_in_struct_cong in H.
    apply ((proj1 free_vars_under_struct_cong) _ _ H) in Hfv; congruence.
  + assert ((rename_process (up P1) swap01) ⇛ (rename_process (up P) swap01)).
    {
      apply directed_cong_invariant_under_renaming.
      + apply (proj1 directed_cong_invariant_under_upshifting); auto.
      + apply swap01_is_bijective.
    }
    assert ((rename_process Q1 swap01) ⇛ (rename_process Q swap01)).
    { apply directed_cong_invariant_under_renaming; auto. apply swap01_is_bijective. }
    assert ((down (rename_process R1 swap01)) ⇛ (down (rename_process R swap01))).
    {
      apply directed_cong_invariant_under_downshifting.
      + apply directed_cong_invariant_under_renaming; auto. apply swap01_is_bijective.
      + apply nfv_01_swap. intro Hfv.
        apply directed_cong_in_struct_cong in d1. apply c_comm in d1.
        apply (proj1 free_vars_under_struct_cong) with (k := 1) in d1. apply n.
        apply d1. auto.
    }
    replace P with
      (down (rename_process (rename_process (up P) swap01) swap01))
      by (autorewrite with up_down_rename_rewrites; try eapply nfv_01_swap; eauto).
    replace Q with
      (rename_process (rename_process Q swap01) swap01)
      by (autorewrite with up_down_rename_rewrites; eauto).
    replace R with
      (rename_process (up (down (rename_process R swap01))) swap01)
      by (autorewrite with up_down_rename_rewrites; try eapply nfv_01_swap; eauto).
    subst.
    eapply dc_cut_assoc_l; eauto. apply nfv_10_swap. apply nfv_lift_n. lia.
Qed.

Corollary directed_cong_symmetric : symmetric _ directed_congruence.
Proof. unfold symmetric; intros. apply (proj1 directed_cong_symm) in H. auto. Qed.

Lemma directed_cong_diamond : diamond_property directed_congruence.
Proof. apply diamond_property_for_symmR. apply directed_cong_symmetric. Qed.

(* ≡ ⊂ ⇛^* *)
Lemma struct_cong_in_trans_directed_cong :
  (forall P Q, P ≡ Q -> clos_trans_1n _ directed_congruence P Q) /\
  (forall M N, M !≡ N -> clos_trans_1n _ directed_congruence_message M N) /\
  (forall s t, s $≡ t -> clos_trans_1n _ directed_congruence_statement s t).
Proof.
  apply struct_cong_ind; intros.
  + apply t1n_step; econstructor; apply dc_cong_reflM.
  + apply t1n_step. apply dc_cut_comm; apply directed_cong_reflexive.
  + apply t1n_step. eapply dc_cut_assoc_l; try apply directed_cong_reflexive; auto.
  + apply t1n_step; apply directed_cong_reflexive.
  + apply symmetric_clos_trans_1n in H; auto. apply directed_cong_symmetric.
  + apply clos_trans_t1n.
    apply clos_t1n_trans in H.
    apply clos_t1n_trans in H0.
    eapply t_trans; eauto.
  + assert (clos_trans_1n _ directed_congruence (link m1 m2) (link m1' m2)).
    {
      clear s s0 H0. induction H.
      + eapply Relation_Operators.t1n_trans.
        - apply dc_cong_link. apply H. apply dc_cong_reflM.
        - apply t1n_step. repeat econstructor.
      + eapply Relation_Operators.t1n_trans.
        - apply dc_cong_link. apply H. apply dc_cong_reflM.
        - eapply Relation_Operators.t1n_trans.
          * apply dc_cong_link; apply dc_cong_reflM.
          * apply IHclos_trans_1n.
    }
    apply clos_trans_t1n. eapply t_trans; apply clos_t1n_trans. { eassumption. }
    clear s s0 H H1. induction H0.
    - eapply Relation_Operators.t1n_trans.
      * apply dc_cong_link. apply dc_cong_reflM. apply H.
      * apply t1n_step. apply dc_cong_link; apply dc_cong_reflM.
    - eapply Relation_Operators.t1n_trans.
      * apply dc_cong_link. apply dc_cong_reflM. apply H.
      * eapply Relation_Operators.t1n_trans. { apply dc_cong_link; apply dc_cong_reflM. } auto.
  + assert (clos_trans_1n _ directed_congruence (cut P Q) (cut P' Q)).
    {
      clear s s0 H0. induction H.
      + apply t1n_step. apply dc_cong_cut; eauto. apply directed_cong_reflexive.
      + eapply Relation_Operators.t1n_trans.
        apply dc_cong_cut; eauto. apply directed_cong_reflexive. auto.
    }
    apply clos_trans_t1n. eapply t_trans; apply clos_t1n_trans. { eassumption. }
    clear s s0 H H1. induction H0.
    - apply t1n_step. apply dc_cong_cut. apply directed_cong_reflexive. auto.
    - eapply Relation_Operators.t1n_trans; eauto.
      apply dc_cong_cut. apply directed_cong_reflexive. eapply H.
  + assert (clos_trans_1n _ directed_congruence (seq P s) (seq P' s)).
    {
      clear H0 s0 s1 s'. induction H.
      + apply t1n_step. econstructor; eauto. apply dc_cong_reflS.
      + eapply Relation_Operators.t1n_trans.
        - econstructor; [apply H | apply dc_cong_reflS].
        - apply IHclos_trans_1n.
    }
    apply clos_trans_t1n. eapply t_trans; apply clos_t1n_trans. { eassumption. }
    clear s0 s1 H H1 P. induction H0.
    - apply t1n_step. econstructor; eauto. apply directed_cong_reflexive.
    - eapply Relation_Operators.t1n_trans.
      * econstructor; [apply directed_cong_reflexive | apply H].
      * apply IHclos_trans_1n.
  + apply t1n_step; econstructor.
  + clear s0. induction H; intros.
    - repeat econstructor; eauto.
    - eapply Relation_Operators.t1n_trans. { econstructor; eauto. } apply IHclos_trans_1n.
  + clear s. induction H; intros.
    - repeat econstructor; eauto.
    - eapply Relation_Operators.t1n_trans. { econstructor; eauto. } apply IHclos_trans_1n.
  + clear s. induction H; intros.
    - repeat econstructor; eauto.
    - eapply Relation_Operators.t1n_trans. { econstructor; eauto. } apply IHclos_trans_1n.
  + assert (clos_trans_1n _ directed_congruence_statement (offer_choice P Q) (offer_choice P' Q)).
    {
      clear s s0 H0 Q' H0. induction H.
      + apply t1n_step. econstructor; eauto. apply directed_cong_reflexive.
      + eapply Relation_Operators.t1n_trans.
        - econstructor; [apply H | apply directed_cong_reflexive].
        - apply IHclos_trans_1n.
    }
    apply clos_trans_t1n. eapply t_trans; apply clos_t1n_trans. { eassumption. }
    clear s s0 H H1. induction H0.
    - apply t1n_step. econstructor; eauto. apply directed_cong_reflexive.
    - eapply Relation_Operators.t1n_trans.
      * econstructor; [apply directed_cong_reflexive | apply H].
      * apply IHclos_trans_1n.
  + assert (clos_trans_1n _ directed_congruence_statement (send P Q) (send P' Q)).
    {
      clear s s0 H0 Q' H0. induction H.
      + apply t1n_step. econstructor; eauto. apply directed_cong_reflexive.
      + eapply Relation_Operators.t1n_trans.
        - econstructor; [apply H | apply directed_cong_reflexive].
        - apply IHclos_trans_1n.
    }
    apply clos_trans_t1n. eapply t_trans; apply clos_t1n_trans. { eassumption. }
    clear s s0 H H1. induction H0.
    - apply t1n_step. econstructor; eauto. apply directed_cong_reflexive.
    - eapply Relation_Operators.t1n_trans.
      * econstructor; [apply directed_cong_reflexive | apply H].
      * apply IHclos_trans_1n.
  + clear s. induction H; intros.
    - repeat econstructor; eauto.
    - eapply Relation_Operators.t1n_trans. { econstructor; eauto. } apply IHclos_trans_1n.
  + apply t1n_step; econstructor.
  + clear s. induction H; intros.
    - repeat econstructor; eauto.
    - eapply Relation_Operators.t1n_trans. { econstructor; eauto. } apply IHclos_trans_1n.
Qed.

(******************************************************************************)
(* Directed congruence is invariant under substitution                        *)
(******************************************************************************)
Definition subst_dc_equiv (σ1 σ2 : substitution) : Prop :=
  forall i, (σ1 i) !⇛ (σ2 i).

Lemma subst_dc_equiv_refl :
  (forall P, forall σ1 σ2, subst_dc_equiv σ1 σ2
    -> (subst_process P σ1) ⇛ (subst_process P σ2)) /\
  (forall M, forall σ1 σ2, subst_dc_equiv σ1 σ2
    -> (subst_message M σ1) !⇛ (subst_message M σ2)) /\
  (forall s, forall σ1 σ2, subst_dc_equiv σ1 σ2
    -> (subst_statement s σ1) $⇛ (subst_statement s σ2)).
Proof.
  apply syntax_ind; intros; simpl;
  assert (subst_dc_equiv (up_subst σ1) (up_subst σ2)) by
    (intros [|]; simpl; try econstructor; apply directed_cong_invariant_under_upshifting; auto);
  try (now (econstructor; try apply H; try apply H0; eauto)).
  + apply (H n).
  + econstructor. apply H. intros [|]; simpl; try econstructor;
    apply directed_cong_invariant_under_upshifting; auto.
Qed.

(* r identity after k and for all i: ren (σ i) r = σ i *)
(* show in a separate lemma: forall k, j < k -> j free and for all j >= k: r j = j,
   then renaming idempotent OR:
   forall i, r i ≠ i, i not free -> renaming idempotent
   *)
Fixpoint up_subst_n (n : nat) (σ : substitution) : substitution :=
  match n with
  | O    => σ
  | S n' => up_subst (up_subst_n n' σ)
  end.

(* Properties about up_subst_n *)
Lemma up_subst_n_lt :
  forall n k σ, n < k -> up_subst_n k σ n = future n.
Proof.
  intros.
  generalize dependent n.
  induction k; intros.
  + inversion H.
  + simpl. destruct n; auto.
    simpl. rewrite IHk; auto. lia.
Qed.

Lemma up_subst_n_ge :
  forall n k σ, k <= n -> up_subst_n k σ n = lift_message (σ (n - k)) 0 k.
Proof.
  intros.
  generalize dependent n.
  induction k; intros.
  + rewrite PeanoNat.Nat.sub_0_r; simpl.
    rewrite (proj1 (proj2 shift_with_0_idempotent)). auto.
  + simpl. assert (k <= n) by lia. destruct n; try (exfalso; lia).
    simpl. rewrite IHk; try lia. unfold upM.
    rewrite (proj1 (proj2 shift_additive)). replace (k + 1) with (S k) by lia.
    auto.
Qed.

Lemma shift_shift_raise_bound :
  (forall P n1 n2 k1 k2, n1 <= n2 -> n2 <= n1 + k1 ->
    (lift_process (lift_process P n1 k1) n2 k2) =
    (lift_process (lift_process P n1 k1) (n1 + k1) k2)) /\
  (forall M n1 n2 k1 k2, n1 <= n2 -> n2 <= n1 + k1 ->
    (lift_message (lift_message M n1 k1) n2 k2) =
    (lift_message (lift_message M n1 k1) (n1 + k1) k2)) /\
  (forall s n1 n2 k1 k2, n1 <= n2 -> n2 <= n1 + k1 ->
    (lift_statement (lift_statement s n1 k1) n2 k2) =
    (lift_statement (lift_statement s n1 k1) (n1 + k1) k2)).
Proof.
  apply syntax_ind; intros; simpl; try rewrite H; try rewrite H0; auto; try lia.
  unfold relocate.
  destruct (Nat.leb n1 n) eqn:E.
  + apply PeanoNat.Nat.leb_le in E. assert (n2 <= k1 + n) by lia.
    apply PeanoNat.Nat.leb_le in H1. rewrite H1.
    assert (n1 <= k1 + n) by lia. assert (n1 + k1 <= k1 + n) by lia.
    apply PeanoNat.Nat.leb_le in H3. rewrite H3. auto.
  + apply PeanoNat.Nat.leb_nle in E.
    assert (~ (n2 <= n)) by lia. apply PeanoNat.Nat.leb_nle in H1.
    assert (~ (n1 + k1 <= n)) by lia. apply PeanoNat.Nat.leb_nle in H2.
    rewrite H1. rewrite H2. auto.
Qed.

Lemma subst_up_lift_commute :
  (forall P, forall σ k,
    subst_process (lift_process P k 1) (up_subst_n (S k) σ)
      = lift_process (subst_process P (up_subst_n k σ)) k 1)
  /\
  (forall M, forall σ k,
    subst_message (lift_message M k 1) (up_subst_n (S k) σ)
      = lift_message (subst_message M (up_subst_n k σ)) k 1)
  /\
  (forall s, forall σ k,
    subst_statement (lift_statement s k 1) (up_subst_n (S k) σ)
      = lift_statement (subst_statement s (up_subst_n k σ)) k 1).
Proof.
  apply syntax_ind; intros; simpl;
  try replace (up_subst (up_subst_n k σ)) with (up_subst_n (S k) σ) by auto;
  try replace (up_subst (up_subst_n (S k) σ)) with (up_subst_n (S (S k)) σ) by auto;
  try now (try rewrite H; try rewrite H0; auto).
  + simpl. unfold relocate.
    destruct (Nat.leb k n) eqn:E.
    - simpl. apply PeanoNat.Nat.leb_le in E. unfold upM.
      rewrite up_subst_n_ge; auto.
      rewrite ((proj1 (proj2 shift_shift_raise_bound)) _ 0 0 k 1); try lia. auto.
    - apply PeanoNat.Nat.leb_nle in E.
      assert (n < k) by lia.
      assert (n < S k) by lia.
      replace (up_subst (up_subst_n k σ)) with (up_subst_n (S k) σ) by auto.
      assert (up_subst_n (S k) σ n = future n) by (apply up_subst_n_lt; auto).
      rewrite H1.
      assert (up_subst_n k σ n = future n) by (apply up_subst_n_lt; auto).
      rewrite H2. simpl. unfold relocate. apply PeanoNat.Nat.leb_nle in E. rewrite E.
      auto.
  + replace (up_subst (up_subst_n (S (S k)) σ)) with (up_subst_n (S (S (S k))) σ) by auto.
    rewrite H. auto.
Qed.

Lemma down_after_lift_Sk :
  (forall P, forall n1 k,
    down1_process (lift_process P n1 (S k)) (n1 + k) = lift_process P n1 k)
  /\
  (forall M, forall n1 k,
    down1_message (lift_message M n1 (S k)) (n1 + k) = lift_message M n1 k)
  /\
  (forall s, forall n1 k,
    down1_statement (lift_statement s n1 (S k)) (n1 + k) = lift_statement s n1 k).
Proof.
  apply syntax_ind; intros; simpl; try rewrite H; try rewrite H0; auto; try lia.
  unfold relocate.
  destruct (Nat.leb n1 n) eqn:E; simpl.
  + apply PeanoNat.Nat.leb_le in E. assert (n1 + k < S (k + n)) by lia.
    apply PeanoNat.Nat.ltb_lt in H. rewrite H; auto.
  + apply PeanoNat.Nat.leb_nle in E. assert (~ (n1 + k <  n)) by lia.
    apply PeanoNat.Nat.ltb_nlt in H. rewrite H; auto.
Qed.

Lemma subst_up_down_commute :
  (forall P, forall σ k,
    ~ (k ∈ P) ->
    down1_process (subst_process P (up_subst_n (S k) σ)) k =
    subst_process (down1_process P k) (up_subst_n k σ)) /\
  (forall M, forall σ k,
    ~ (occurs_free_message k M) ->
    down1_message (subst_message M (up_subst_n (S k) σ)) k =
    subst_message (down1_message M k) (up_subst_n k σ)) /\
  (forall s, forall σ k,
    ~ (occurs_free_statement k s) ->
    down1_statement (subst_statement s (up_subst_n (S k) σ)) k =
    subst_statement (down1_statement s k) (up_subst_n k σ)).
Proof.
  apply syntax_ind; intros; simpl;
  try replace (up_subst (up_subst_n k σ)) with (up_subst_n (S k) σ) by auto;
  try replace (up_subst (up_subst_n (S k) σ)) with (up_subst_n (S (S k)) σ) by auto;
  try (now (try rewrite H; try rewrite H0; auto; intro Hfv; try apply H1; try apply H0; free_var_econstructor; eauto)).
  + destruct (Nat.ltb k n) eqn:E.
    - apply PeanoNat.Nat.ltb_lt in E.
      assert (S k <= n) by lia.
      assert (up_subst_n (S k) σ n = lift_message (σ (n - (S k))) 0 (S k))
        by (apply up_subst_n_ge; auto).
      rewrite H1. simpl.
      assert (up_subst_n k σ (Nat.pred n) = lift_message (σ (Nat.pred n - k)) 0 k).
      { rewrite up_subst_n_ge; auto. lia. }
      rewrite  H2. simpl.
      assert (n - S k = Nat.pred n - k) by lia.
      rewrite H3. rewrite (proj1 (proj2 down_after_lift_Sk)). auto.
    - apply PeanoNat.Nat.ltb_nlt in E.
      assert (n < (S k)) by lia.
      assert (up_subst_n (S k) σ n = future n) by (apply up_subst_n_lt; auto).
      rewrite H1. simpl. apply PeanoNat.Nat.ltb_nlt in E. rewrite E.
      apply PeanoNat.Nat.ltb_nlt in E.
      assert (n <> k). { intro Heq. apply H. rewrite Heq; econstructor. }
      assert (n < k) by lia.
      assert (up_subst_n k σ n = future n) by (apply up_subst_n_lt; auto).
      rewrite H4.
      auto.
  + replace (up_subst (up_subst_n (S (S k)) σ)) with (up_subst_n (S (S (S k))) σ) by auto.
    rewrite H; auto. intro Hfv. apply H0. free_var_econstructor. auto.
Qed.

Lemma ren_subst_commute :
  (forall P, forall r σ k,
    bijective r -> (forall j, j >= k -> r j = j) ->
    (forall j, j < k -> (σ j) = (future j)) ->
    (forall j, j >= k -> (rename_message (σ j) r) = (σ j)) ->
    subst_process (rename_process P r) σ
      = rename_process (subst_process P σ) r)
  /\
  (forall M, forall r σ k,
    bijective r -> (forall j, j >= k -> r j = j) ->
    (forall j, j < k -> (σ j) = (future j)) ->
    (forall j, j >= k -> (rename_message (σ j) r) = (σ j)) ->
    subst_message (rename_message M r) σ
      = rename_message (subst_message M σ) r)
  /\
  (forall s, forall r σ k,
    bijective r -> (forall j, j >= k -> r j = j) ->
    (forall j, j < k -> (σ j) = (future j)) ->
    (forall j, j >= k -> (rename_message (σ j) r) = (σ j)) ->
    subst_statement (rename_statement s r) σ
      = rename_statement (subst_statement s σ) r).
Proof.
  apply syntax_ind; intros; simpl;
  try now (try rewrite (H _ _ k); try rewrite (H0 _ _ k); auto).
  + assert (
      forall j : nat, j >= (S k) -> up_ren r j = j
    ).
    { intros [|] ?; auto; simpl. rewrite H2; auto; lia. }
    assert (
      forall j : nat, j < S k -> up_subst σ j = future j
    ).
    {
      intros [|] ?; auto; simpl. rewrite H3; simpl; auto; lia.
    }
    assert (
      forall j : nat, j >= S k -> rename_message (up_subst σ j) (up_ren r) = up_subst σ j
    ).
    {
      intros [|] ?; auto; simpl.
      unfold upM.
      rewrite (proj1 (proj2 ren_up_up_ren_commute)); auto.
      + rewrite H4; auto; lia.
      + intros; exfalso; lia.
    }
    assert (
      bijective (up_ren r)
    ) by (apply shift_preserves_bijection; auto).
    rewrite (H _ _ (S k)); try rewrite (H0 _ _ (S k)); auto.
  + assert (
      forall j : nat, j >= (S k) -> up_ren r j = j
    ).
    { intros [|] ?; auto; simpl. rewrite H2; auto; lia. }
    assert (
      forall j : nat, j < S k -> up_subst σ j = future j
    ).
    {
      intros [|] ?; auto; simpl. rewrite H3; simpl; auto; lia.
    }
    assert (
      forall j : nat, j >= S k -> rename_message (up_subst σ j) (up_ren r) = up_subst σ j
    ).
    {
      intros [|] ?; auto; simpl.
      unfold upM.
      rewrite (proj1 (proj2 ren_up_up_ren_commute)); auto.
      + rewrite H4; auto; lia.
      + intros; exfalso; lia.
    }
    assert (
      bijective (up_ren r)
    ) by (apply shift_preserves_bijection; auto).
    rewrite (H _ _ (S k)); try rewrite (H0 _ _ (k)); auto.
  + destruct (Compare_dec.lt_dec n k).
    - rewrite H1. rewrite H1; simpl. auto. auto.
      destruct (Compare_dec.lt_dec (r n) k); auto.
      apply Compare_dec.not_lt in n0.
      rewrite H0 in n0; try lia.
      assert ( (r (r n)) = (r n)). { rewrite H0; auto. }
      assert (r n = n).
      {
        destruct H. assert (g (r (r n)) = g (r n)) by auto.
        rewrite c in H. rewrite c in H. auto.
      }
      rewrite <- H4; auto.
    - apply Compare_dec.not_lt in n0. rewrite H0; auto.
      rewrite H2; auto.
  + assert (
      forall j : nat, j >= (S k) -> up_ren r j = j
    ).
    { intros [|] ?; auto; simpl. rewrite H1; auto; lia. }
    assert (
      forall j : nat, j < S k -> up_subst σ j = future j
    ).
    {
      intros [|] ?; auto; simpl. rewrite H2; simpl; auto; lia.
    }
    assert (
      forall j : nat, j >= S k -> rename_message (up_subst σ j) (up_ren r) = up_subst σ j
    ).
    {
      intros [|] ?; auto; simpl.
      unfold upM.
      rewrite (proj1 (proj2 ren_up_up_ren_commute)); auto.
      + rewrite H3; auto; lia.
      + intros; exfalso; lia.
    }
    assert (
      bijective (up_ren r)
    ) by (apply shift_preserves_bijection; auto).
    rewrite (H _ _ (S k)); try rewrite (H0 _ _ (S k)); auto.
  + assert (
      forall j : nat, j >= (S k) -> up_ren r j = j
    ).
    { intros [|] ?; auto; simpl. rewrite H1; auto; lia. }
    assert (
      forall j : nat, j < S k -> up_subst σ j = future j
    ).
    {
      intros [|] ?; auto; simpl. rewrite H2; simpl; auto; lia.
    }
    assert (
      forall j : nat, j >= S k -> rename_message (up_subst σ j) (up_ren r) = up_subst σ j
    ).
    {
      intros [|] ?; auto; simpl.
      unfold upM.
      rewrite (proj1 (proj2 ren_up_up_ren_commute)); auto.
      + rewrite H3; auto; lia.
      + intros; exfalso; lia.
    }
    assert (
      bijective (up_ren r)
    ) by (apply shift_preserves_bijection; auto).
    rewrite (H _ _ (S k)); try rewrite (H0 _ _ (S k)); auto.
  + assert (
      forall j : nat, j >= (S k) -> up_ren r j = j
    ).
    { intros [|] ?; auto; simpl. rewrite H2; auto; lia. }
    assert (
      forall j : nat, j < S k -> up_subst σ j = future j
    ).
    {
      intros [|] ?; auto; simpl. rewrite H3; simpl; auto; lia.
    }
    assert (
      forall j : nat, j >= S k -> rename_message (up_subst σ j) (up_ren r) = up_subst σ j
    ).
    {
      intros [|] ?; auto; simpl.
      unfold upM.
      rewrite (proj1 (proj2 ren_up_up_ren_commute)); auto.
      + rewrite H4; auto; lia.
      + intros; exfalso; lia.
    }
    assert (
      bijective (up_ren r)
    ) by (apply shift_preserves_bijection; auto).
    rewrite (H _ _ (S k)); try rewrite (H0 _ _ (S k)); auto.
  + assert (
      forall j : nat, j >= (S k) -> up_ren r j = j
    ).
    { intros [|] ?; auto; simpl. rewrite H2; auto; lia. }
    assert (
      forall j : nat, j < S k -> up_subst σ j = future j
    ).
    {
      intros [|] ?; auto; simpl. rewrite H3; simpl; auto; lia.
    }
    assert (
      forall j : nat, j >= S k -> rename_message (up_subst σ j) (up_ren r) = up_subst σ j
    ).
    {
      intros [|] ?; auto; simpl.
      unfold upM.
      rewrite (proj1 (proj2 ren_up_up_ren_commute)); auto.
      + rewrite H4; auto; lia.
      + intros; exfalso; lia.
    }
    assert (
      bijective (up_ren r)
    ) by (apply shift_preserves_bijection; auto).
    rewrite (H _ _ (S k)); try rewrite (H0 _ _ (S k)); auto.
  + rewrite (H _ _ (S (S k))); auto.
    - repeat apply shift_preserves_bijection; auto.
    - intros [|[|]] ?; auto; simpl. rewrite H1; auto; lia.
    - intros [|[|]] ?; auto; simpl. rewrite H2; simpl; auto; lia.
    - intros [|[|]] ?; auto; simpl. unfold upM.
      rewrite (proj1 (proj2 ren_up_up_ren_commute)); auto.
      rewrite (proj1 (proj2 ren_up_up_ren_commute)); auto.
      rewrite H3; auto. lia.
      * intros; exfalso; lia.
      * apply shift_preserves_bijection; auto.
      * intros; exfalso; lia.
Qed.

Lemma fv_up_Sn2' :
  (forall (p : process),
    forall n k, k <= n -> (S n) ∈ (lift_process p k 1) -> n ∈ p)
  /\
  (forall (m : message),
    forall n k, k <= n -> occurs_free_message (S n) (lift_message m k 1) -> occurs_free_message n m)
  /\
  (forall (s : statement),
    forall n k, k <= n -> occurs_free_statement (S n) (lift_statement s k 1) -> occurs_free_statement n s).
Proof.
  apply syntax_ind; intros; simpl.
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
  + inversion H0; subst.
    destruct (Nat.leb k n) eqn:E.
    - unfold relocate in H3. rewrite E in H3. simpl in H3.
      inversion H3. econstructor.
    - unfold relocate in H3. rewrite E in H3.
      rewrite H3 in H0. apply PeanoNat.Nat.leb_nle in E.
      assert (n < n0) by lia. exfalso; lia.
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

Lemma nfv_under_substitution :
  (forall P σ i,
    ~ (i ∈ P) ->
    (forall n, n <> i -> ~ (occurs_free_message i (σ n)))
    -> ~ (i ∈ (subst_process P σ))) /\
  (forall M σ i,
    ~ (occurs_free_message i M) ->
    (forall n, n <> i -> ~ (occurs_free_message i (σ n)))
    -> ~ (occurs_free_message i (subst_message M σ))) /\
  (forall s σ i,
    ~ (occurs_free_statement i s) ->
    (forall n, n <> i -> ~ (occurs_free_message i (σ n)))
    -> ~ (occurs_free_statement i (subst_statement s σ))).
Proof.
  apply syntax_ind; intros;
  (* assert that up_subst σ also satisfies free variables condition *)
  try assert ( Hfvup : forall n : nat, n <> S i -> ~ occurs_free_message (S i) (up_subst σ n))
  by (
    intros; intro Hfv2; destruct n; simpl in Hfv2; auto; [
      inversion Hfv2
    | apply fv_up_Sn2' in Hfv2;
      try apply (proj1 (PeanoNat.Nat.succ_inj_wd_neg _ _)) in H3;
      try apply (proj1 (PeanoNat.Nat.succ_inj_wd_neg _ _)) in H2; auto; try lia;
      try apply (H2 n); try apply (H1 n); auto
    ]
  ).
  + intro Hfv. inversion Hfv; subst.
    - assert (~ (occurs_free_message i m)).
      { intro Hfv1. apply H1; free_var_econstructor; eauto. }
      apply (H σ i H3 H2); auto.
    - assert (~ (occurs_free_message i m0)).
      { intro Hfv1. apply H1; free_var_econstructor; eauto. }
      apply (H0 σ i H3 H2); auto.
  + intro Hfv; inversion Hfv; subst.
    - eapply (H (up_subst σ) (S i)); auto.
      intro Hfv1; apply H1; free_var_econstructor; auto.
    - eapply (H0 (up_subst σ) (S i)); auto.
      intro Hfv1; apply H1; free_var_econstructor; auto.
  + intro Hfv; inversion Hfv; subst.
    - eapply (H (up_subst σ) (S i)); auto.
      intro Hfv1; apply H1; free_var_econstructor; auto.
    - eapply (H0 σ i); auto.
      intro Hfv1; apply H1; free_var_econstructor; auto.
  + simpl. intros; auto.
  + intro Hfv. destruct (PeanoNat.Nat.eq_dec n i).
    - subst. apply H. free_var_econstructor.
    - apply (H0 n n0). simpl in Hfv. auto.
  + intro Hfv; inversion Hfv; subst.
    eapply (H σ i); auto. intro Hfv1; apply H0; free_var_econstructor; auto.
  + intro Hfv; inversion Hfv; subst.
    eapply (H (up_subst σ) (S i)); auto. intro Hfv1; apply H0; free_var_econstructor; auto.
  + intro Hfv; inversion Hfv; subst.
    eapply (H (up_subst σ) (S i)); auto. intro Hfv1; apply H0; free_var_econstructor; auto.
  + intro Hfv; inversion Hfv; subst.
    - eapply (H (up_subst σ) (S i)); auto.
      intro Hfv1; apply H1; free_var_econstructor; auto.
    - eapply (H0 (up_subst σ) (S i)); auto.
      intro Hfv1; apply H1; free_var_econstructor; auto.
  + intro Hfv; inversion Hfv; subst.
    - eapply (H (up_subst σ) (S i)); auto.
      intro Hfv1; apply H1; free_var_econstructor; auto.
    - eapply (H0 (up_subst σ) (S i)); auto.
      intro Hfv1; apply H1; free_var_econstructor; auto.
  + intro Hfv; inversion Hfv; subst.
    eapply (H (up_subst (up_subst σ)) (S (S i))); auto.
    - intros Hfv1; apply H0. free_var_econstructor. auto.
    - intros; intro Hfv2; destruct n; simpl in Hfv2; auto; [
        inversion Hfv2
      | apply fv_up_Sn2' in Hfv2;
        try apply (proj1 (PeanoNat.Nat.succ_inj_wd_neg _ _)) in H3;
        try apply (proj1 (PeanoNat.Nat.succ_inj_wd_neg _ _)) in H2; auto; try lia;
        try apply (Hfvup n); auto
      ].
  + simpl. intros; auto.
  + intro Hfv; inversion Hfv; subst.
    eapply (H σ i); auto. intro Hfv1; apply H0; free_var_econstructor; auto.
Qed.

Lemma renaming_idempotent_free_vars :
  (forall P r,
    (forall n, n ∈ P -> r n = n) ->
    (rename_process P r) = P) /\
  (forall M r,
    (forall n, occurs_free_message n M -> r n = n) ->
    (rename_message M r) = M) /\
  (forall s r,
    (forall n, occurs_free_statement n s -> r n = n) ->
    (rename_statement s r) = s).
Proof.
  apply syntax_ind; intros; simpl;
  try rewrite H; try rewrite H0; auto;
  try (intros; apply H1; free_var_econstructor; auto);
  try (intros; apply H0; free_var_econstructor; auto);
  try (intros; destruct n; simpl; auto; rewrite H1; auto; free_var_econstructor; auto);
  try (intros; destruct n; simpl; auto; rewrite H0; auto; free_var_econstructor; auto).
  + econstructor.
  + intros. destruct n as [|[|]]; auto; simpl. rewrite H0; auto.
    free_var_econstructor; auto.
Qed.

Lemma directed_cong_invariant_under_substitution :
  (forall P Q, P ⇛ Q -> forall σ1 σ2, subst_dc_equiv σ1 σ2
    -> (subst_process P σ1) ⇛ (subst_process Q σ2)) /\
  (forall M N, M !⇛ N -> forall σ1 σ2, subst_dc_equiv σ1 σ2
    -> (subst_message M σ1) !⇛ (subst_message N σ2)) /\
  (forall s t, s $⇛ t -> forall σ1 σ2, subst_dc_equiv σ1 σ2
    -> (subst_statement s σ1) $⇛ (subst_statement t σ2)).
Proof.
  apply directed_cong_ind; intros; simpl;
  assert (subst_dc_equiv (up_subst σ1) (up_subst σ2)) by
    (intros [|]; simpl; try econstructor; apply directed_cong_invariant_under_upshifting; auto);
  try (now (econstructor; try apply H; try apply H0; auto)).
  + assert (subst_dc_equiv (up_subst (up_subst σ1)) (up_subst (up_subst σ2)))
      by (intros [|]; simpl; try econstructor; apply directed_cong_invariant_under_upshifting; auto).
    eapply dc_cut_assoc_l.
    - apply nfv_under_substitution; intros; try congruence.
      intro Hfv. destruct n0 as [|[|]]; try (exfalso; lia); simpl in Hfv; auto.
      * inversion Hfv.
      * unfold upM in Hfv.
        rewrite (proj1 (proj2 shift_additive) _ 0 1 1) in Hfv; simpl in Hfv.
        apply nfv_lift_n in Hfv. auto. lia.
    - apply H; eauto.
    - apply H0; eauto.
    - apply H1; eauto.
    - rewrite e.
      assert (
        rename_process (subst_process P1 (up_subst (up_subst σ2))) swap01 =
        subst_process (rename_process P1 swap01) (up_subst (up_subst σ2))
      ).
      {
        rewrite ((proj1 ren_subst_commute) _ _ _ 2); auto.
        * apply swap01_is_bijective.
        * intros [|[|]] ?; auto; exfalso; lia.
        * intros [|[|]] ?; auto; exfalso; lia.
        * intros. destruct j as [|[|]]; try (exfalso; lia); simpl.
          apply renaming_idempotent_free_vars. intros [|[|]].
          - simpl. unfold upM. rewrite (proj1 (proj2 shift_additive)); simpl.
            intros.
            assert (~ (occurs_free_message 0 (lift_message (σ2 n0) 0 2))).
            { apply nfv_lift_n; lia. }
            congruence.
          - simpl. unfold upM. rewrite (proj1 (proj2 shift_additive)); simpl.
            intros.
            assert (~ (occurs_free_message 1 (lift_message (σ2 n0) 0 2))).
            { apply nfv_lift_n; lia. }
            congruence.
          - auto.
      }
      rewrite H5.
      unfold down. replace (up_subst σ2) with (up_subst_n 0 (up_subst σ2)) by auto.
      replace (up_subst (up_subst_n 0 (up_subst σ2))) with (up_subst_n 1 (up_subst σ2)) by auto.
      rewrite (proj1 subst_up_down_commute); auto.
      apply nfv_01_swap. intro Hfv. apply directed_cong_in_struct_cong in d.
      apply c_comm in d. apply ((proj1 free_vars_under_struct_cong) _ _ d) in Hfv. congruence.
    - rewrite e0.
      rewrite ((proj1 ren_subst_commute) _ _ _ 2); auto.
      * apply swap01_is_bijective.
      * intros [|[|]] ?; auto; exfalso; lia.
      * intros [|[|]] ?; auto; exfalso; lia.
      * intros. destruct j as [|[|]]; try (exfalso; lia); simpl.
        apply renaming_idempotent_free_vars. intros [|[|]].
        ** simpl. unfold upM. rewrite (proj1 (proj2 shift_additive)); simpl.
           intros.
           assert (~ (occurs_free_message 0 (lift_message (σ2 n0) 0 2))).
           { apply nfv_lift_n; lia. }
           congruence.
        ** simpl. unfold upM. rewrite (proj1 (proj2 shift_additive)); simpl.
           intros.
           assert (~ (occurs_free_message 1 (lift_message (σ2 n0) 0 2))).
           { apply nfv_lift_n; lia. }
           congruence.
        ** auto.
    - rewrite e1.
      assert (
        subst_process (rename_process (up R1) swap01) (up_subst (up_subst σ2)) =
        rename_process (subst_process (up R1) (up_subst (up_subst σ2))) swap01
      ).
      {
        rewrite ((proj1 ren_subst_commute) _ _ _ 2); auto.
        * apply swap01_is_bijective.
        * intros [|[|]] ?; auto; exfalso; lia.
        * intros [|[|]] ?; auto; exfalso; lia.
        * intros. destruct j as [|[|]]; try (exfalso; lia); simpl.
          apply renaming_idempotent_free_vars. intros [|[|]].
          - simpl. unfold upM. rewrite (proj1 (proj2 shift_additive)); simpl.
            intros.
            assert (~ (occurs_free_message 0 (lift_message (σ2 n0) 0 2))).
            { apply nfv_lift_n; lia. }
            congruence.
          - simpl. unfold upM. rewrite (proj1 (proj2 shift_additive)); simpl.
            intros.
            assert (~ (occurs_free_message 1 (lift_message (σ2 n0) 0 2))).
            { apply nfv_lift_n; lia. }
            congruence.
          - auto.
      }
      rewrite H5. unfold up.
      replace (up_subst σ2) with (up_subst_n 1 σ2) by auto.
      rewrite (proj1 subst_up_lift_commute); auto.
  + assert (subst_dc_equiv (up_subst (up_subst σ1)) (up_subst (up_subst σ2)))
      by (intros [|]; simpl; try econstructor; apply directed_cong_invariant_under_upshifting; auto).
    eapply dc_cut_assoc_r.
    - apply nfv_under_substitution; intros; try congruence.
      intro Hfv. destruct n0 as [|[|]]; try (exfalso; lia); simpl in Hfv; auto.
      * inversion Hfv.
      * unfold upM in Hfv.
        rewrite (proj1 (proj2 shift_additive) _ 0 1 1) in Hfv; simpl in Hfv.
        apply nfv_lift_n in Hfv. auto. lia.
    - apply H; eauto.
    - apply H0; eauto.
    - apply H1; eauto.
    - rewrite e.
      assert (
        subst_process (rename_process (up P1) swap01) (up_subst (up_subst σ2)) =
        rename_process (subst_process (up P1) (up_subst (up_subst σ2))) swap01
      ).
      {
        rewrite ((proj1 ren_subst_commute) _ _ _ 2); auto.
        * apply swap01_is_bijective.
        * intros [|[|]] ?; auto; exfalso; lia.
        * intros [|[|]] ?; auto; exfalso; lia.
        * intros. destruct j as [|[|]]; try (exfalso; lia); simpl.
          apply renaming_idempotent_free_vars. intros [|[|]].
          - simpl. unfold upM. rewrite (proj1 (proj2 shift_additive)); simpl.
            intros.
            assert (~ (occurs_free_message 0 (lift_message (σ2 n0) 0 2))).
            { apply nfv_lift_n; lia. }
            congruence.
          - simpl. unfold upM. rewrite (proj1 (proj2 shift_additive)); simpl.
            intros.
            assert (~ (occurs_free_message 1 (lift_message (σ2 n0) 0 2))).
            { apply nfv_lift_n; lia. }
            congruence.
          - auto.
      }
      rewrite H5. unfold up.
      replace (up_subst σ2) with (up_subst_n 1 σ2) by auto.
      rewrite (proj1 subst_up_lift_commute); auto.
    - rewrite e0.
      rewrite ((proj1 ren_subst_commute) _ _ _ 2); auto.
      * apply swap01_is_bijective.
      * intros [|[|]] ?; auto; exfalso; lia.
      * intros [|[|]] ?; auto; exfalso; lia.
      * intros. destruct j as [|[|]]; try (exfalso; lia); simpl.
        apply renaming_idempotent_free_vars. intros [|[|]].
        ** simpl. unfold upM. rewrite (proj1 (proj2 shift_additive)); simpl.
           intros.
           assert (~ (occurs_free_message 0 (lift_message (σ2 n0) 0 2))).
           { apply nfv_lift_n; lia. }
           congruence.
        ** simpl. unfold upM. rewrite (proj1 (proj2 shift_additive)); simpl.
           intros.
           assert (~ (occurs_free_message 1 (lift_message (σ2 n0) 0 2))).
           { apply nfv_lift_n; lia. }
           congruence.
        ** auto.
    - rewrite e1.
      assert (
        rename_process (subst_process R1 (up_subst (up_subst σ2))) swap01 =
        subst_process (rename_process R1 swap01) (up_subst (up_subst σ2))
      ).
      {
        rewrite ((proj1 ren_subst_commute) _ _ _ 2); auto.
        * apply swap01_is_bijective.
        * intros [|[|]] ?; auto; exfalso; lia.
        * intros [|[|]] ?; auto; exfalso; lia.
        * intros. destruct j as [|[|]]; try (exfalso; lia); simpl.
          apply renaming_idempotent_free_vars. intros [|[|]].
          - simpl. unfold upM. rewrite (proj1 (proj2 shift_additive)); simpl.
            intros.
            assert (~ (occurs_free_message 0 (lift_message (σ2 n0) 0 2))).
            { apply nfv_lift_n; lia. }
            congruence.
          - simpl. unfold upM. rewrite (proj1 (proj2 shift_additive)); simpl.
            intros.
            assert (~ (occurs_free_message 1 (lift_message (σ2 n0) 0 2))).
            { apply nfv_lift_n; lia. }
            congruence.
          - auto.
      }
      rewrite H5.
      unfold down. replace (up_subst σ2) with (up_subst_n 0 (up_subst σ2)) by auto.
      replace (up_subst (up_subst_n 0 (up_subst σ2))) with (up_subst_n 1 (up_subst σ2)) by auto.
      rewrite (proj1 subst_up_down_commute); auto.
      apply nfv_01_swap. intro Hfv. apply directed_cong_in_struct_cong in d1.
      apply c_comm in d1. apply ((proj1 free_vars_under_struct_cong) _ _ d1) in Hfv. congruence.
  + apply subst_dc_equiv_refl; auto.
  + econstructor. apply H. intros [|]; simpl; try econstructor;
    apply directed_cong_invariant_under_upshifting; auto.
  + apply subst_dc_equiv_refl; auto.
Qed.
