From FD Require Import Syntax.
From FD Require Import FreeVars.
From FD Require Import Renaming.
From FD Require Import FreeVars.
From FD Require Import StructCong.
From FD Require Import ConfluenceDefs.
From FD Require Import DirectedCong.
From FD Require Import Reduction.
From FD Require Import ParallelReduction.

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

(* ⇛ and ⊵ commute *)
(*
         P
      ⇛    ⊵
    Q1       Q2
      ⊵    ⇛
         R
*)
Lemma directed_cong_equiv_red_commute :
  (* ⇛ in conclusion has to be changed to ≡ for axcut *)
  forall P Q1 Q2, P ⇛ Q1 -> P ⊵ Q2 -> exists R, Q1 ⊵ R /\ Q2 ⇛ R.
Proof.
  intros. generalize dependent Q2.
  induction H; intros.
  (* link *)
  + eapply link_directed_cong_equiv_red_commute; eauto; econstructor; eauto.
  + eapply link_directed_cong_equiv_red_commute; eauto. apply dc_link; auto.

  (* cut *)
  + admit.
  + admit.
  + admit.
  + admit.

  (* + inversion H0; subst.
    - eexists. split. econstructor. apply dc_cut_comm.
    - eexists. split.
      * apply rp_cong_cut_r; eauto.
      * apply dc_cut_comm.
    - eexists. split.
      * apply rp_cong_cut_l; eauto.
      * apply dc_cut_comm.
  + inversion H3; subst.
    - eexists. split.
      * apply rp_refl.
      * eapply dc_cut_assoc_l; auto.
    - inversion H7; subst.
      *  eexists. split. apply rp_refl. apply dc_cut_assoc_l; auto.
      * (* ⊵ is invariant under renaming, shifting *)
        assert ( (down (rename_process P swap01)) ⊵  (down (rename_process P' swap01)) )
         by admit.
        eexists. split. { apply rp_cong_cut_l. apply H0. }
        apply dc_cut_assoc_l; auto.
        (* free variables are preserved under reduction *)
        admit.
      * (* ⊵ is invariant under renaming, shifting *)
        assert ( (rename_process Q swap01) ⊵  (rename_process Q' swap01) )
         by admit.
        eexists. split. { apply rp_cong_cut_r. apply rp_cong_cut_l. apply H0. }
        apply dc_cut_assoc_l; auto.
    - admit.
  + admit.
  + admit. *)

  (* seq *)
  + inversion H1; subst.
    - eexists. split. apply rp_refl. apply dc_cong_seq; auto.
    - eexists. split. apply rp_seq.
      apply directed_cong_invariant_under_substitution; auto.
      intros [|]; simpl. { econstructor; eauto. }
      apply dc_cong_reflM.
    - destruct (IHdirected_congruence _ H5) as [? [? ?]].
      eexists. split.
      * apply rp_cong_seq. apply H2.
      * apply dc_cong_seq; auto.
  + inversion H0; subst. exists stop; split; eauto. apply dc_stop.
Admitted.

(* ≡ and ↠ commute *)
(*
         P
      ≡    ↠
    Q1       Q2
      ↠    ≡
         R
*)
Lemma struct_cong_par_red_commute :
  forall P Q1 Q2, P ≡ Q1 -> P ↠ Q2 -> exists R, Q1 ↠ R /\ Q2 ≡ R.
Proof.
  intros. destruct H0.
  + apply struct_cong_in_trans_directed_cong in H.
    generalize dependent Q2.
    induction H; intros.
    - destruct (directed_cong_equiv_red_commute _ _ _ H H0) as [? [? ?]].
      exists x0. split.
      * left. auto.
      * apply directed_cong_in_struct_cong. auto.
    - destruct (directed_cong_equiv_red_commute _ _ _ H H1) as [? [? ?]].
      destruct (IHclos_trans_1n _ H2) as [? [? ?]].
      exists x1. split; auto.
      apply directed_cong_in_struct_cong in H3. eapply c_trans; eauto.
  + exists P. split.
    - right. apply c_comm; auto.
    - apply c_comm; auto.
Qed.

(* ↠ is confluent *)
Lemma church_rosser_parallel_reduction :
  diamond_property par_reduction.
Proof.
  unfold diamond_property. intros.
  destruct H eqn:E.
  + destruct H0.
    - clear - H0 e.
      admit.
    - destruct (struct_cong_par_red_commute _ _ _ H0 H) as [? [? ?]].
      eexists; split; eauto. right; auto.
  + destruct (struct_cong_par_red_commute _ _ _ s H0) as [? [? ?]].
    eexists; split; eauto. right; auto.
Admitted.

(* ▶ is confluent *)
Lemma church_rosser :
  diamond_property multi_step_reduction.
Proof.
  eapply diamond_preserved_under_eq.
  + apply diamond_R_diamond_clos_trans_R.
    apply church_rosser_parallel_reduction.
  + apply par_reds_clos_trans_multi_step_red_coincide.
Qed.

(* invariance for ⊵ under renaming, shifting, substitution must follow by induction on depth *)
(* for invariance under subst: show that subst compose then argue by extensionality on composition 
   (NB: always remember which variables occur bound/free; after traversing binder
   substitutions may commute (consider M ⋅ id and (up_subst σ))
*)