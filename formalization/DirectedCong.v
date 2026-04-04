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
*)

(******************************************************************************)
(* Directed Structural Congruence (technical device for Church-Rosser)        *)
(******************************************************************************)
(* ⇛ (Rrightarrow)  *)
Reserved Notation "P '⇛' Q" (no associativity, at level 1).
Reserved Notation "M '!⇛' N" (no associativity, at level 1).
Reserved Notation "s '$⇛' r" (no associativity, at level 1).

Inductive directed_congruence : process -> process -> Prop :=
  | c_refl : forall P, P ⇛ P
  | c_link : forall ml1 ml2 mr1 mr2,
              ml1 !⇛ ml2 ->
              mr1 !⇛ mr2 -> 
              (link ml1 mr1) ⇛ (link mr2 ml2)
  | c_cut_comm : forall P1 P2 Q1 Q2,
                  P1 ⇛ P2 ->
                  Q1 ⇛ Q2 ->
                  (cut P1 Q1) ⇛ (cut Q2 P2)
  | c_cut_assoc_l : forall P Q R P1 Q1 R1 P' Q' R',
                      ~ (1 ∈ P) ->
                      P ⇛ P1 ->
                      Q ⇛ Q1 ->
                      R ⇛ R1 ->
                      P' = down (rename_process P1 swap01) ->
                      Q' = rename_process Q1 swap01 ->
                      R' = rename_process (up R1) swap01 ->
                      (cut (cut P Q) R) ⇛ (cut P' (cut Q' R'))
  | c_cut_assoc_r : forall P Q R P1 Q1 R1 P' Q' R',
                      ~ (1 ∈ R) ->
                      P ⇛ P1 ->
                      Q ⇛ Q1 ->
                      R ⇛ R1 ->
                      P' = rename_process (up P1) swap01 ->
                      Q' = rename_process Q1 swap01 ->
                      R' = down (rename_process R1 swap01) ->
                      (cut P (cut Q R)) ⇛ (cut (cut P' Q') R')
  | c_cong_seq : forall P P' s s',
                  P ⇛ P' -> s $⇛ s' -> (seq P s) ⇛ (seq P' s')
where
  "P '⇛' Q" := (directed_congruence P Q)

with directed_congruence_message : message -> message -> Prop :=
  | c_cong_prefix : forall s s', s $⇛ s' -> (prefix s) !⇛ (prefix s')
  | c_cong_reflM : forall m, m !⇛ m
where
  "M '!⇛' N" := (directed_congruence_message M N)

with directed_congruence_statement : statement -> statement -> Prop :=
  | c_cong_choose_l : forall P P',
                        P ⇛ P' ->
                        (choose_left P) $⇛ (choose_left P')
  | c_cong_choose_r : forall P P',
                        P ⇛ P' ->
                        (choose_right P) $⇛ (choose_right P')
  | c_cong_choice : forall P P' Q Q',
                      P ⇛ P' -> Q ⇛ Q' -> (offer_choice P Q) $⇛ (offer_choice P' Q')
  | c_cong_send : forall P P' Q Q',
                    P ⇛ P' -> Q ⇛ Q' -> (send P Q) $⇛ (send P' Q')
  | c_cong_receive : forall P P', P ⇛ P' -> (receive P) $⇛ (receive P')
  | c_cong_close : close $⇛ close
  | c_cong_wait : forall P P', P ⇛ P' -> (wait P) $⇛ (wait P')
  | c_cong_reflS : forall s, s $⇛ s
where
  "s '$⇛' r" := (directed_congruence_statement s r).

(* Mutual induction principle for strucutral congruence *)
Scheme directed_congP_ind := Induction for directed_congruence Sort Prop
  with directed_congM_ind := Induction for directed_congruence_message Sort Prop
  with directed_congS_ind := Induction for directed_congruence_statement Sort Prop.
Combined Scheme directed_cong_ind from directed_congP_ind, directed_congM_ind, directed_congS_ind.

Local Hint Rewrite
  swap_swap_id
  down_after_up_process_id
  up_after_down_process_id
    : up_down_rename_rewrites.

(* ⇛ ⊂ ≡ *)
Lemma directed_cong_in_struct_cong :
  (forall P Q, P ⇛ Q -> P ≡ Q) /\
  (forall M N, M !⇛ N -> M !≡ N) /\
  (forall s t, s $⇛ t -> s $≡ t).
Proof.
  apply directed_cong_ind; intros; try now (econstructor; eauto).
  + eapply c_trans. eapply StructCong.c_link. apply c_cong_link; auto.
  + eapply c_trans. eapply StructCong.c_cut_comm. apply c_cong_cut; auto.
  + assert ((cut (cut P Q) R) ≡ (cut (cut P1 Q1) R1)).
    {
      apply c_cong_cut; auto. apply c_cong_cut; auto.
    }
    subst. eapply c_trans.
    - apply H2.
    - apply c_cut_assoc; auto.
      intro Hfv. apply ((proj1 free_vars_under_struct_cong) _ _ H) in Hfv. congruence.
  + assert ( (cut P (cut Q R)) ≡ (cut P1 (cut Q1 R1)) ).
    { apply c_cong_cut; auto. apply c_cong_cut; auto. }
    eapply c_trans. { apply H2. }
    apply c_comm. eapply c_trans.
    - apply c_cut_assoc; subst; auto. replace 1 with (swap01 0) by reflexivity.
      apply ((proj1 nfv_under_renaming) _ swap01). apply swap01_is_bijective.
      apply nfv_lift_n; lia.
    - autorewrite with up_down_rename_rewrites. apply StructCong.c_refl.
      replace 0 with (swap01 1) by reflexivity.
      apply ((proj1 nfv_under_renaming) _ swap01). apply swap01_is_bijective.
      intro Hfv. apply c_comm in H1.
      apply ((proj1 free_vars_under_struct_cong) _ _ H1) in Hfv. congruence.
  + destruct (proj1 (proj2 struct_cong_d_refl) m).
    eapply (proj1 (proj2 struct_cong_from_struct_cong_d)); eauto.
  + destruct (proj2 (proj2 struct_cong_d_refl) s).
    eapply (proj2 (proj2 struct_cong_from_struct_cong_d)); eauto.
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
  apply directed_cong_ind; intros.
  + apply c_refl.
  + simpl. apply c_link; auto.
  + simpl. apply c_cut_comm.
    - apply (H (up_ren r)). apply shift_preserves_bijection; auto.
    - apply (H0 (up_ren r)). apply shift_preserves_bijection; auto.
  + simpl.
    assert (bijective (up_ren r)) by (repeat apply shift_preserves_bijection; auto).
    assert (bijective (up_ren (up_ren r))) by (repeat apply shift_preserves_bijection; auto).
    subst. eapply c_cut_assoc_l.
    - replace 1 with ((up_ren (up_ren r)) 1) by reflexivity.
      apply ((proj1 nfv_under_renaming) _ (up_ren (up_ren r))); auto.
    - apply H; auto.
    - apply H0; auto.
    - apply H1; auto.
    - assert (
        rename_process (rename_process P1 (up_ren (up_ren r))) swap01 =
        rename_process (rename_process P1 swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H5. unfold down.
      assert (~ 1 ∈ P1).
      {
        intro Hfv. apply directed_cong_in_struct_cong in d. apply c_comm in d.
        apply ((proj1 free_vars_under_struct_cong) _ _ d) in Hfv. congruence.
      }
      rewrite (proj1 down_ren_up_ren_commute); auto.
      { intros. exfalso. lia. }
      apply nfv_01_swap; auto.
    - rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
      rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
      reflexivity. all: intros[|[|]]; auto.
    - assert (
        rename_process (rename_process (up R1) swap01) (up_ren (up_ren r)) =
        rename_process (rename_process (up R1) (up_ren (up_ren r))) swap01
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H5. unfold up.
      rewrite (proj1 ren_up_up_ren_commute); auto.
      intros. exfalso. lia.
  + simpl. subst.
    assert (bijective (up_ren r)) by (repeat apply shift_preserves_bijection; auto).
    assert (bijective (up_ren (up_ren r))) by (repeat apply shift_preserves_bijection; auto).
    eapply c_cut_assoc_r.
    - replace 1 with ((up_ren (up_ren r)) 1) by reflexivity.
      apply ((proj1 nfv_under_renaming) _ (up_ren (up_ren r))); auto.
    - apply H; auto.
    - apply H0; auto.
    - apply H1; auto.
    - assert (
        rename_process (rename_process (up P1) swap01) (up_ren (up_ren r)) =
        rename_process (rename_process (up P1) (up_ren (up_ren r))) swap01
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H5. unfold up.
      rewrite (proj1 ren_up_up_ren_commute); auto.
      intros. exfalso. lia.
    - rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
      rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
      reflexivity. all: intros[|[|]]; auto.
    - assert (
        rename_process (rename_process R1 (up_ren (up_ren r))) swap01 =
        rename_process (rename_process R1 swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H5. unfold down.
      assert (~ 1 ∈ R1).
      {
        intro Hfv. apply directed_cong_in_struct_cong in d1. apply c_comm in d1.
        apply ((proj1 free_vars_under_struct_cong) _ _ d1) in Hfv. congruence.
      }
      rewrite (proj1 down_ren_up_ren_commute); auto.
      { intros. exfalso. lia. }
      apply nfv_01_swap; auto.
  + simpl. apply c_cong_seq; auto. apply (H (up_ren r)); auto. apply shift_preserves_bijection; auto.
  + simpl. apply c_cong_prefix; auto.
  + apply c_cong_reflM.
  + simpl. constructor; auto. apply (H (up_ren r)); auto. apply shift_preserves_bijection; auto.
  + simpl. constructor; auto. apply (H (up_ren r)); auto. apply shift_preserves_bijection; auto.
  + simpl. constructor; auto;
    try apply (H (up_ren r)); try apply (H0 (up_ren r)); auto; apply shift_preserves_bijection; auto.
  + simpl. constructor; auto;
    try apply (H (up_ren r)); try apply (H0 (up_ren r)); auto; apply shift_preserves_bijection; auto.
  + simpl. constructor; auto. apply (H (up_ren (up_ren r))); auto; repeat apply shift_preserves_bijection; auto.
  + simpl; constructor.
  + simpl. constructor; auto.
  + simpl. constructor.
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
  + simpl. subst. eapply c_cut_assoc_l; auto.
    - apply nfv_up_lt; try lia. assumption.
    - unfold down.
      rewrite (proj1 lift_after_down_lt_commute); try lia.
      rewrite (proj1 lift_at_k_rename_id_after_k_commute); auto. apply swap01_is_bijective.
      intros [|[|]] ?; auto; exfalso; lia.
    - rewrite (proj1 lift_at_k_rename_id_after_k_commute); auto. apply swap01_is_bijective.
      intros [|[|]] ?; auto; exfalso; lia.
    - rewrite (proj1 lift_at_k_rename_id_after_k_commute).
      * unfold up. rewrite (proj1 lift_k_lift_Sj_lt_commute); auto. lia.
      * apply swap01_is_bijective.
      * intros [|[|]] ?; auto; exfalso; lia.
  + simpl. subst. eapply c_cut_assoc_r; auto.
    - apply nfv_up_lt; try lia. assumption.
    - rewrite (proj1 lift_at_k_rename_id_after_k_commute).
      * unfold up. rewrite (proj1 lift_k_lift_Sj_lt_commute); auto. lia.
      * apply swap01_is_bijective.
      * intros [|[|]] ?; auto; exfalso; lia.
    - rewrite (proj1 lift_at_k_rename_id_after_k_commute); auto. apply swap01_is_bijective.
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
  + eapply c_cut_assoc_l; subst.
    - apply (proj1 nfv_down_lt); auto. lia.
    - apply H. intro Hfv. apply H2. repeat free_var_econstructor; auto.
    - apply H0. intro Hfv. apply H2. repeat free_var_econstructor; auto.
    - apply H1. intro Hfv. apply H2. repeat free_var_econstructor; auto.
    - unfold down.
      rewrite <- (proj1 down_at_k_rename_id_after_k_commute).
      * rewrite (proj1 down_k_down_Sj_lt_commute); auto. lia.
      * apply swap01_is_bijective.
      * intros [|[|]] ?; auto; exfalso; lia.
    - rewrite <- (proj1 down_at_k_rename_id_after_k_commute); auto.
      apply swap01_is_bijective. intros [|[|]] ?; auto; exfalso; lia.
    - unfold up.
      rewrite (proj1 down_at_k_rename_id_after_k_commute).
      * rewrite (proj1 down_after_down_gt_commute); auto. lia.
      * apply swap01_is_bijective.
      * intros [|[|]] ?; auto; exfalso; lia.
  + eapply c_cut_assoc_r; subst.
    - apply (proj1 nfv_down_lt); auto. lia.
    - apply H. intro Hfv. apply H2. repeat free_var_econstructor; auto.
    - apply H0. intro Hfv. apply H2. apply fv_cut_r. free_var_econstructor; auto.
    - apply H1. intro Hfv. apply H2. apply fv_cut_r. free_var_econstructor; auto.
    - unfold up.
      rewrite (proj1 down_at_k_rename_id_after_k_commute).
      * rewrite (proj1 down_after_down_gt_commute); auto. lia.
      * apply swap01_is_bijective.
      * intros [|[|]] ?; auto; exfalso; lia.
    - rewrite <- (proj1 down_at_k_rename_id_after_k_commute); auto.
      apply swap01_is_bijective. intros [|[|]] ?; auto; exfalso; lia.
    - unfold down.
      rewrite <- (proj1 down_at_k_rename_id_after_k_commute).
      * rewrite (proj1 down_k_down_Sj_lt_commute); auto. lia.
      * apply swap01_is_bijective.
      * intros [|[|]] ?; auto; exfalso; lia.
  + econstructor; try apply (H (S k)); try apply H0; intro Hfv; apply H1; free_var_econstructor; auto.
  + econstructor; apply H; intro Hfv; apply H0; free_var_econstructor; auto.
Qed.

Lemma directed_cong_symm :
  (forall P1 P2, P1 ⇛ P2 -> P2 ⇛ P1) /\
  (forall M1 M2, M1 !⇛ M2 -> M2 !⇛ M1) /\
  (forall s1 s2, s1 $⇛ s2 -> s2 $⇛ s1).
Proof.
  apply directed_cong_ind; intros; try now (econstructor; eauto).
  + assert ((down (rename_process P1 swap01)) ⇛ (down (rename_process P swap01))).
    {
      apply directed_cong_invariant_under_downshifting.
      + apply directed_cong_invariant_under_renaming; auto. apply swap01_is_bijective.
      + apply nfv_01_swap. intro Hfv.
        apply directed_cong_in_struct_cong in d. apply c_comm in d.
        apply (proj1 free_vars_under_struct_cong) with (k := 1) in d. apply n.
        apply d. auto.
    }
    assert ((rename_process Q1 swap01) ⇛ (rename_process Q swap01)).
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
    eapply c_cut_assoc_r; eauto. apply nfv_10_swap. apply nfv_lift_n. lia.
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
    eapply c_cut_assoc_l; eauto. apply nfv_10_swap. apply nfv_lift_n. lia.
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
  apply struct_cong_ind; intros;
  try now (apply t1n_step; repeat econstructor).
  + apply symmetric_clos_trans_1n in H; auto. apply directed_cong_symmetric.
  + apply clos_trans_t1n.
    apply clos_t1n_trans in H.
    apply clos_t1n_trans in H0.
    eapply t_trans; eauto.
  + assert (clos_trans_1n _ directed_congruence (link m1 m2) (link m1' m2)).
    {
      clear s s0 H0. induction H.
      + eapply Relation_Operators.t1n_trans.
        - apply c_link. apply H. apply c_cong_reflM.
        - apply t1n_step. repeat econstructor.
      + eapply Relation_Operators.t1n_trans.
        - apply c_link. apply H. apply c_cong_reflM.
        - eapply Relation_Operators.t1n_trans.
          * apply c_link; apply c_cong_reflM.
          * apply IHclos_trans_1n.
    }
    apply clos_trans_t1n. eapply t_trans; apply clos_t1n_trans. { eassumption. }
    clear s s0 H H1. induction H0.
    - eapply Relation_Operators.t1n_trans.
      * apply c_link. apply c_cong_reflM. apply H.
      * apply t1n_step. apply c_link; apply c_cong_reflM.
    - eapply Relation_Operators.t1n_trans.
      * apply c_link. apply c_cong_reflM. apply H.
      * eapply Relation_Operators.t1n_trans. { apply c_link; apply c_cong_reflM. } auto.
  + assert (clos_trans_1n _ directed_congruence (cut P Q) (cut P' Q)).
    {
      clear s s0 H0. induction H.
      + eapply Relation_Operators.t1n_trans.
        - apply c_cut_comm. apply H. apply c_refl.
        - apply t1n_step. repeat econstructor.
      + eapply Relation_Operators.t1n_trans.
        - apply c_cut_comm. apply H. apply c_refl.
        - eapply Relation_Operators.t1n_trans.
          * apply c_cut_comm; apply c_refl.
          * apply IHclos_trans_1n.
    }
    apply clos_trans_t1n. eapply t_trans; apply clos_t1n_trans. { eassumption. }
    clear s s0 H H1. induction H0.
    - eapply Relation_Operators.t1n_trans.
      * apply c_cut_comm. apply c_refl. apply H.
      * apply t1n_step. apply c_cut_comm; apply c_refl.
    - eapply Relation_Operators.t1n_trans.
      * apply c_cut_comm. apply c_refl. apply H.
      * eapply Relation_Operators.t1n_trans. { apply c_cut_comm; apply c_refl. } auto.
  + assert (clos_trans_1n _ directed_congruence (seq P s) (seq P' s)).
    {
      clear H0 s0 s1 s'. induction H.
      + apply t1n_step. econstructor; eauto. apply c_cong_reflS.
      + eapply Relation_Operators.t1n_trans.
        - econstructor; [apply H | apply c_cong_reflS].
        - apply IHclos_trans_1n.
    }
    apply clos_trans_t1n. eapply t_trans; apply clos_t1n_trans. { eassumption. }
    clear s0 s1 H H1 P. induction H0.
    - apply t1n_step. econstructor; eauto. apply c_refl.
    - eapply Relation_Operators.t1n_trans.
      * econstructor; [apply c_refl | apply H].
      * apply IHclos_trans_1n.
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
      + apply t1n_step. econstructor; eauto. apply c_refl.
      + eapply Relation_Operators.t1n_trans.
        - econstructor; [apply H | apply c_refl].
        - apply IHclos_trans_1n.
    }
    apply clos_trans_t1n. eapply t_trans; apply clos_t1n_trans. { eassumption. }
    clear s s0 H H1. induction H0.
    - apply t1n_step. econstructor; eauto. apply c_refl.
    - eapply Relation_Operators.t1n_trans.
      * econstructor; [apply c_refl | apply H].
      * apply IHclos_trans_1n.
  + assert (clos_trans_1n _ directed_congruence_statement (send P Q) (send P' Q)).
    {
      clear s s0 H0 Q' H0. induction H.
      + apply t1n_step. econstructor; eauto. apply c_refl.
      + eapply Relation_Operators.t1n_trans.
        - econstructor; [apply H | apply c_refl].
        - apply IHclos_trans_1n.
    }
    apply clos_trans_t1n. eapply t_trans; apply clos_t1n_trans. { eassumption. }
    clear s s0 H H1. induction H0.
    - apply t1n_step. econstructor; eauto. apply c_refl.
    - eapply Relation_Operators.t1n_trans.
      * econstructor; [apply c_refl | apply H].
      * apply IHclos_trans_1n.
  + clear s. induction H; intros.
    - repeat econstructor; eauto.
    - eapply Relation_Operators.t1n_trans. { econstructor; eauto. } apply IHclos_trans_1n.
  + clear s. induction H; intros.
    - repeat econstructor; eauto.
    - eapply Relation_Operators.t1n_trans. { econstructor; eauto. } apply IHclos_trans_1n.
Qed.
