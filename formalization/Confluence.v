From FD Require Import Syntax.
From FD Require Import FreeVars.
From FD Require Import Renaming.
From FD Require Import FreeVars.
From FD Require Import StructCong.
From FD Require Import ConfluenceDefs.
From FD Require Import DirectedCong.
From FD Require Import Reduction.
From FD Require Import ParallelReduction.

Lemma diamond_par_red_imp_diamond_multistep :
  diamond_property par_reduces -> diamond_property multi_step_reduction.
Proof.
  intros. apply diamond_R_diamond_clos_trans_R in H.
  eapply diamond_preserved_under_eq; eauto.
  apply par_reds_clos_trans_multi_step_red_coincide.
Qed.

Lemma link_directed_cong_par_red_confluent :
  forall ml mr P Q, (link ml mr) ⇛ P -> (link ml mr) ⊵ Q ->
    exists R, P ⊵ R /\ Q ⊵ R.
Proof.
  intros. inversion H; subst.
  { exists Q; split; auto; econstructor. econstructor. }
  inversion H0; subst;
  (* For reflexivity, we discharge the goal via admissibility of symmetry *)
  try (now (eexists; split; econstructor; apply directed_cong_symm; eauto));
  try match goal with
  | [ H1 : (prefix (send _ _)) !⇛ _,
      H2 : (prefix (receive _)) !⇛ _
      |- _ ] =>
    apply directed_cong_inversion_prefix in H1; destruct H1 as [? [? H1']];
    apply directed_cong_inversion_prefix in H2; destruct H2 as [? [? H2']];
    apply directed_cong_inversion_send in H1'; destruct H1' as [? [? [? [? ?]]]];
    apply directed_cong_inversion_receive in H2'; destruct H2' as [? [? ?]];
    subst; eexists; split; [
      try eapply rp_tensor_par_2; try eapply rp_tensor_par_1; try eapply directed_cong_symm; eauto
    | eapply rp_cong_cut; try (now (econstructor; eapply directed_cong_symm; eauto));
      eapply rp_cong_cut; try (now (econstructor; eapply directed_cong_symm; eauto));
      econstructor; apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective;
      apply directed_cong_invariant_under_upshifting;
      apply directed_cong_symm; auto
    ]
  | [ H1 : (prefix (choose_left _)) !⇛ _,
      H2 : (prefix (offer_choice _ _)) !⇛ _
      |- _ ] =>
    apply directed_cong_inversion_prefix in H1; destruct H1 as [? [? H1']];
    apply directed_cong_inversion_prefix in H2; destruct H2 as [? [? H2']];
    apply directed_cong_inversion_choosel in H1'; destruct H1' as [? [? ?]];
    apply directed_cong_inversion_choice in H2'; destruct H2' as [? [? [? [? ?]]]];
    subst; eexists; split; [
      try eapply rp_plus_with_l1; try eapply rp_plus_with_l2; try eapply directed_cong_symm; eauto
    | eapply rp_cong_cut; try (now (econstructor; eapply directed_cong_symm; eauto));
      eapply rp_cong_cut; try (now (econstructor; eapply directed_cong_symm; eauto));
      econstructor; apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective;
      apply directed_cong_invariant_under_upshifting;
      apply directed_cong_symm; auto
    ]
  | [ H1 : (prefix (choose_right _)) !⇛ _,
      H2 : (prefix (offer_choice _ _)) !⇛ _
      |- _ ] =>
    apply directed_cong_inversion_prefix in H1; destruct H1 as [? [? H1']];
    apply directed_cong_inversion_prefix in H2; destruct H2 as [? [? H2']];
    apply directed_cong_inversion_chooser in H1'; destruct H1' as [? [? ?]];
    apply directed_cong_inversion_choice in H2'; destruct H2' as [? [? [? [? ?]]]];
    subst; eexists; split; [
      try eapply rp_plus_with_r1; try eapply rp_plus_with_r2; try eapply directed_cong_symm; eauto
    | eapply rp_cong_cut; try (now (econstructor; eapply directed_cong_symm; eauto));
      eapply rp_cong_cut; try (now (econstructor; eapply directed_cong_symm; eauto));
      econstructor; apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective;
      apply directed_cong_invariant_under_upshifting;
      apply directed_cong_symm; auto
    ]
  | [ H1 : (prefix close) !⇛ _,
      H2 : (prefix (wait _)) !⇛ _
      |- _ ] =>
    apply directed_cong_inversion_prefix in H1; destruct H1 as [? [? H1']];
    apply directed_cong_inversion_prefix in H2; destruct H2 as [? [? H2']];
    apply directed_cong_inversion_close in H1';
    apply directed_cong_inversion_wait in H2'; destruct H2' as [? [? ?]];
    subst; eexists; split; [
      try eapply rp_one_bot1; try eapply rp_one_bot2; try eapply directed_cong_symm; eauto
    | econstructor; apply directed_cong_symm; auto
    ]
  end.
Qed.

Lemma confluence_directed_cong_par_red :
  forall P Q1 Q2, P ⇛ Q1 -> P ⊵ Q2 -> exists R, Q1 ⊵ R /\ Q2 ⊵ R.
Proof.
  intros. generalize dependent Q2.
  induction H; intros.
  + exists Q2. split; auto. econstructor. apply c_refl.
  + eapply link_directed_cong_par_red_confluent; eauto. econstructor; eauto.
  + inversion H1; subst.
    - admit.
    - (* downM M' requires well-typedness of M to conclude that 0 is not in free vars of M' *)
      admit.
    - admit.
    - inversion H0; subst.
      * (* cut (cut (link (future 1) M) R) P2
           not covered by parallel reduction
           NB: try approach below before adding addtional reduction rules and
               see how far we can go. However, we will likely need all
               rp_cut_assoc rules up to symmetry (see original approach)
               with this addtional premise
        *)
        (* add a premise:
            L ⇛ (cut (link (future 1) M) R)
           to rp_ax_cut_assoc rules so that
           cut P L ⊵ cut (subst_process P'' ((downM M'' ⋅ id_subst))) R''
        *)
        admit.
      * admit.
      * (* congruences allows to perform association more than once !!!!! *)
        admit.
    - inversion H; subst.
      * admit.
      * admit. (* should work easily with new premise *)
      * admit.
    - admit.
  + inversion H6; subst.
    - exists Q2; split; try (now econstructor);
      admit.
    - (* dont bother doing an inversion on H9; try to use invariances instead *)
      (* we need 0 not in M/M' *)
      admit.
    - (* in R1, up results in future 2 but swap01 is also uped ->
         future 1 remains in R1 ->
         via cut_cong, the left side may still reduce via cut assoc
         use H9 and invariances too conclude result
         *)
      admit.
    - admit.
    - admit.
  + admit.
  + inversion H1; subst.
    - exists (seq P s). apply directed_cong_symm in H, H0, H2.
      split; auto; repeat econstructor; auto.
    - eexists. split.
      * eapply rp_seq.
        { apply directed_cong_symm in H. apply H. }
        { apply directed_cong_symm in H0. apply H0. }
      * apply directed_cong_symm in H4, H6. econstructor.
        apply directed_cong_substitution; auto.
        intros i. destruct i; simpl; econstructor; auto.
    - apply directed_cong_symm in H, H0, H6.
      apply IHdirected_congruence in H4. destruct H4 as [? [? ?]].
      eexists. split; eapply rp_cong_seq; eauto.
Admitted.

(* invariance for ⊵ under renaming, shifting, substitution must follow by induction on depth *)
(* for invariance under subst: show that subst compose then argue by extensionality on composition 
   (NB: always remember which variables occur bound/free; after traversing binder
   substitutions may commute (consider M ⋅ id and (up_subst σ))
*)