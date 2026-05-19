From FD Require Import Syntax.
From FD Require Import FreeVars.
From FD Require Import Renaming.
From FD Require Import FreeVars.
From FD Require Import StructCong.
From FD Require Import Contexts.
From FD Require Import Typing.
From FD Require Import ConfluenceDefs.
From FD Require Import DirectedCong.
From FD Require Import Reduction.
From FD Require Import ParallelReduction.
From FD Require Import AxCutCtx.

From Stdlib Require Import Lia.

Local Hint Rewrite
  swap_swap_id
  down_after_up_process_id
  up_after_down_process_id
    : up_down_rename_rewrites.

(* ⇛ and ⊵ commute *)
(*
         P
      ⇛    ⊵
    Q1       Q2
      ⊵    ≡
         R
*)
Lemma directed_cong_equiv_red_commute :
  forall Γ P Q1 Q2, Γ ⊢ P :# -> P ⇛ Q1 -> P ⊵ Q2 -> exists R, Q1 ⊵ R /\ Q2 ≡ R.
Proof.
  intros.
  generalize dependent Γ.
  generalize dependent Q2.
  induction H0; intros.
  (* link *)
  + destruct (link_directed_cong_equiv_red_commute _ _ _ _ (dc_cong_link _ _ _ _  H H0) H1) as [? [? ?]].
    eexists; split; eauto. apply directed_cong_in_struct_cong; auto.
  + destruct (link_directed_cong_equiv_red_commute _ _ _ _ (dc_link _ _ _ _  H H0) H1) as [? [? ?]].
    eexists; split; eauto. apply directed_cong_in_struct_cong; auto.
  (* cut *)
  + inversion H1; subst.
    - eexists; split. apply rp_refl.
      apply directed_cong_in_struct_cong. apply dc_cut_comm; auto.
    - destruct (fill_hole_congruence _ _ _ _ eq_refl H0_) as [E' [M' [? ?]]].
      eexists. split.
      * rewrite H0. eapply rp_ax_cut_r; eauto. eapply edc_preserves_well_formedness; eauto.
      * apply directed_cong_in_struct_cong. subst. apply reduce_axcut_invariant_under_dc; eauto.
    - destruct (fill_hole_congruence _ _ _ _ eq_refl H0_0) as [E' [M' [? ?]]].
      eexists. split.
      * rewrite H0. eapply rp_ax_cut_l; eauto. eapply edc_preserves_well_formedness; eauto.
      * apply directed_cong_in_struct_cong. subst. apply reduce_axcut_invariant_under_dc; eauto.
    - inversion H; subst.
      destruct (IHdirected_congruence1 _ H4 _ H6) as [? [? ?]].
      eexists; split.
      * apply rp_cong_cut_r; eauto.
      * eapply c_trans. apply c_cut_comm. apply c_cong_cut; auto.
        apply directed_cong_in_struct_cong; auto.
    - inversion H; subst.
      destruct (IHdirected_congruence2 _ H4 _ H7) as [? [? ?]].
      eexists; split.
      * apply rp_cong_cut_l; eauto.
      * eapply c_trans. apply c_cut_comm. apply c_cong_cut; auto.
        apply directed_cong_in_struct_cong; auto.
  + inversion H3; subst.
    - eexists. split. apply rp_refl.
      apply directed_cong_in_struct_cong in H0_, H0_0, H0_1.
      apply c_trans with (cut (cut P1 Q1) R1).
      * repeat (apply c_cong_cut; auto).
      * apply c_cut_assoc; auto. intro Hfv.
        apply ((proj1 free_vars_under_struct_cong) _ _ H0_ 1) in Hfv. congruence.
    - destruct E; simpl in H7; try congruence.
      {
        inversion H7; subst.
        destruct (fill_hole_congruence _ _ _ _ eq_refl H0_0) as [E' [M' [? ?]]].
        rewrite H0.
        rewrite (rename_axcut_ctx_over_fill_hole _ _ swap01 swap01_is_bijective).
        eexists; split.
        + apply rp_cong_cut_r. eapply rp_ax_cut_l; auto.
          inversion H8; subst.
          replace swap01 with (up_ren_n 0 swap01) by auto.
          replace 0 with ((up_ren_n 0 swap01) 1) at 1 by auto.
          apply (edc_preserves_well_formedness _ _ _ H1) in H10.
            apply well_formedness_preserved_under_swap01; assumption.
        + rewrite reduce_axcut_equation_3. apply c_cong_cut.
          - apply directed_cong_in_struct_cong.
            apply directed_cong_invariant_under_downshifting.
            apply directed_cong_invariant_under_renaming; auto; try apply swap01_is_bijective.
            apply nfv_01_swap; auto.
          - apply directed_cong_in_struct_cong.
            apply reduce_axcut_invariant_under_dc.
            * apply edc_invariant_under_renaming; auto; apply swap01_is_bijective.
            * apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
              apply directed_cong_invariant_under_upshifting; auto.
            * repeat rewrite <- (rename_axcut_ctx_over_fill_hole _ _ swap01 swap01_is_bijective).
              apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
              rewrite <- H0. auto.
      }
      {
        (* because of well-formedness, 0 must be free in (cons_r E P0)
           in which case 1 ∈ E. However, because of association, ~ 1 ∈ P. *)
        exfalso.
        inversion H7; subst. inversion H8; subst.
        apply well_formed_ctx_fv in H6.
        apply (fv_ctx_fill_hole _ _ M) in H6.
        congruence.
      }
    - admit.
    - admit.
    - inversion H4; subst.
      destruct (IHdirected_congruence3 _ H8 _ H7) as [? [? ?]].
      assert (
        rename_process (up R1) swap01 ⊵ rename_process (up x) swap01
      ).
      {
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply directed_cong_in_struct_cong in H0_1.
        apply ((proj1 struct_cong_preserves_typing) _ _ H0_1 _) in H7.
        eapply equiv_red_invariant_under_swap; eauto.
        + replace (Types.dual A .: Γ2) with (nil ++ (Types.dual A .: Γ2)) in H7; auto.
          apply (proj1 up_shift_sound) in H7; eauto.
        + eapply equiv_red_invariant_under_up; eauto.
      }
      eexists. split.
      * apply rp_cong_cut_r. apply rp_cong_cut_r. apply H5.
      * eapply c_trans with (cut (cut P1 Q1) x).
        {
          apply directed_cong_in_struct_cong in H0_.
          apply directed_cong_in_struct_cong in H0_0.
          apply c_cong_cut; auto. apply c_cong_cut; auto.
        }
        apply c_cut_assoc; auto.
        apply directed_cong_in_struct_cong in H0_.
        pose proof ((proj1 free_vars_under_struct_cong) _ _ H0_ 1).
        intro Hfv. apply H9 in Hfv. congruence.
  + inversion H3; subst.
    - eexists. split. apply rp_refl.
      apply directed_cong_in_struct_cong in H0_, H0_0, H0_1.
      apply c_trans with (cut P1 (cut Q1 R1)).
      * repeat (apply c_cong_cut; auto).
      * eapply c_trans. apply c_cut_comm.
        eapply c_trans. { apply c_cong_cut. apply c_cut_comm. apply c_refl. }
        eapply c_trans. { apply c_cut_assoc; auto. intro Hfv. apply ((proj1 free_vars_under_struct_cong) _ _ H0_1 1) in Hfv. congruence. }
        eapply c_trans. apply c_cut_comm.
        apply c_cong_cut. apply c_cut_comm. apply c_refl.
    - admit.
    - destruct E; simpl in H7; try congruence.
      {
        (* because of well-formedness, 0 must be free in (cons_r E P0)
           in which case 1 ∈ E. However, because of association, ~ 1 ∈ P. *)
        exfalso.
        inversion H7; subst. inversion H8; subst.
        apply well_formed_ctx_fv in H6.
        apply (fv_ctx_fill_hole _ _ M) in H6.
        congruence.
      }
      {
        inversion H7; subst.
        destruct (fill_hole_congruence _ _ _ _ eq_refl H0_0) as [E' [M' [? ?]]].
        rewrite H0.
        rewrite (rename_axcut_ctx_over_fill_hole _ _ swap01 swap01_is_bijective).
        eexists; split.
        + apply rp_cong_cut_l. eapply rp_ax_cut_r; auto.
          inversion H8; subst.
          replace swap01 with (up_ren_n 0 swap01) by auto.
          replace 0 with ((up_ren_n 0 swap01) 1) at 1 by auto.
          apply (edc_preserves_well_formedness _ _ _ H1) in H10.
          apply well_formedness_preserved_under_swap01; assumption.
        + rewrite reduce_axcut_equation_4. apply c_cong_cut.
          - apply directed_cong_in_struct_cong.
            apply reduce_axcut_invariant_under_dc.
            * apply edc_invariant_under_renaming; auto; apply swap01_is_bijective.
            * apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
              apply directed_cong_invariant_under_upshifting; auto.
            * repeat rewrite <- (rename_axcut_ctx_over_fill_hole _ _ swap01 swap01_is_bijective).
              apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
              rewrite <- H0. auto.
          - apply directed_cong_in_struct_cong.
            apply directed_cong_invariant_under_downshifting.
            apply directed_cong_invariant_under_renaming; auto; try apply swap01_is_bijective.
            apply nfv_01_swap; auto.
      }
    - inversion H4; subst.
      destruct (IHdirected_congruence1 _ H8 _ H6) as [? [? ?]].
      assert (
        rename_process (up P1) swap01 ⊵ rename_process (up x) swap01
      ).
      {
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply directed_cong_in_struct_cong in H0_.
        apply ((proj1 struct_cong_preserves_typing) _ _ H0_ _) in H6.
        eapply equiv_red_invariant_under_swap; eauto.
        + replace (A .: Γ1) with (nil ++ (A .: Γ1)) in H6; auto.
          apply (proj1 up_shift_sound) in H6; eauto.
        + eapply equiv_red_invariant_under_up; eauto.
      }
      eexists. split.
      * apply rp_cong_cut_l. apply rp_cong_cut_l. apply H5.
      * eapply c_trans with (cut x (cut Q1 R1)).
        {
          apply directed_cong_in_struct_cong in H0_0.
          apply directed_cong_in_struct_cong in H0_1.
          apply c_cong_cut; auto. apply c_cong_cut; auto.
        }
        eapply c_trans. apply c_cut_comm. eapply c_trans. eapply c_cong_cut. apply c_cut_comm. apply c_refl.
        eapply c_trans. { apply c_cut_assoc; eauto. apply directed_cong_in_struct_cong in H0_1. eapply nfv_under_struct_cong; eauto. }
        eapply c_trans. apply c_cut_comm. apply c_cong_cut. apply c_cut_comm. apply c_refl.
    - admit.
  + inversion H1; subst.
    - eexists; split. apply rp_refl. apply c_cong_cut; apply directed_cong_in_struct_cong; auto.
    - destruct (fill_hole_congruence _ _ _ _ eq_refl H0_) as [E' [M' [? ?]]].
      eexists. split.
      * rewrite H0. eapply rp_ax_cut_l; eauto. eapply edc_preserves_well_formedness; eauto.
      * apply directed_cong_in_struct_cong. subst. apply reduce_axcut_invariant_under_dc; eauto.
    - destruct (fill_hole_congruence _ _ _ _ eq_refl H0_0) as [E' [M' [? ?]]].
      eexists. split.
      * rewrite H0. eapply rp_ax_cut_r; eauto. eapply edc_preserves_well_formedness; eauto.
      * apply directed_cong_in_struct_cong. subst. apply reduce_axcut_invariant_under_dc; eauto.
    - inversion H; subst.
      destruct (IHdirected_congruence1 _ H4 _ H6) as [? [? ?]].
      eexists; split.
      * apply rp_cong_cut_l; eauto.
      * eapply c_cong_cut; auto. apply directed_cong_in_struct_cong; auto.
    - inversion H; subst.
      destruct (IHdirected_congruence2 _ H4 _ H7) as [? [? ?]].
      eexists; split.
      * apply rp_cong_cut_r; eauto.
      * eapply c_cong_cut; auto. apply directed_cong_in_struct_cong; auto.
  (* seq *)
  + inversion H1; subst.
    - eexists. split. apply rp_refl.
      apply directed_cong_in_struct_cong in H, H0.
      apply c_cong_seq; auto.
    - eexists. split. apply rp_seq. eapply directed_cong_in_struct_cong.
      apply directed_cong_invariant_under_substitution; auto.
      intros [|]; simpl. { econstructor; eauto. }
      apply dc_cong_reflM.
    - inversion H2; subst.
      destruct (IHdirected_congruence _ H6 _ H8) as [? [? ?]].
      eexists. split.
      * apply rp_cong_seq. apply H3.
      * apply directed_cong_in_struct_cong in H, H0. apply c_cong_seq; auto.
  + inversion H1; subst. exists stop; split; eauto. apply c_refl.

(* intros. generalize dependent Q2.
  induction H; intros.
  (* link *)
  + destruct (link_directed_cong_equiv_red_commute _ _ _ _ (dc_cong_link _ _ _ _  H H0) H1) as [? [? ?]].
    eexists; split; eauto. apply directed_cong_in_struct_cong; auto.
  + destruct (link_directed_cong_equiv_red_commute _ _ _ _ (dc_link _ _ _ _  H H0) H1) as [? [? ?]].
    eexists; split; eauto. apply directed_cong_in_struct_cong; auto.

  (* cut *)
  + inversion H1; subst.
    - eexists; split. apply rp_refl.
      apply directed_cong_in_struct_cong. apply dc_cut_comm; auto.
    - (* Helpful lemmas:
         i.  If fill_hole E M ⇛ P, then exists E' M', s.t. P = fill_hole E' M'
         ii. If Q ⇛ Q' and fill_hole E M ⇛ fill_hole E' M',
             then reduce_axcut E M Q ⇛ reduce_axcut E' M' Q'

             proof by induction on size of context (in ax cut case, IH holds
             for renamed context)
      *)
      (* Idea: Define ⇛ on contexts, then show
         E[M] ⇛ P, then P = E'[M'] and E ⇛ E' and M ⇛ M'

         Then, show that if E ⇛ E', M ⇛ M', Q ⇛ Q' then
          reduce_axcut E M Q ⇛ reduce_axcut E' M' Q'
      *)
      destruct (fill_hole_congruence _ _ _ _ eq_refl H) as [E' [M' [? [? ?]]]].
      exists (reduce_axcut E' M' Q'). split.
      {
        rewrite H2. eapply rp_ax_cut_r; eauto.
        eapply edc_preserves_well_formedness; eauto.
      }
      apply directed_cong_in_struct_cong.
      apply reduce_axcut_invariant_under_dc; auto.
    - destruct (fill_hole_congruence _ _ _ _ eq_refl H0) as [E' [M' [? [? ?]]]].
      exists (reduce_axcut E' M' P'). split.
      {
        rewrite H2. eapply rp_ax_cut_l; eauto.
        eapply edc_preserves_well_formedness; eauto.
      }
      apply directed_cong_in_struct_cong.
      apply reduce_axcut_invariant_under_dc; auto.
    - specialize IHdirected_congruence1 with P'0.
      apply IHdirected_congruence1 in H5. destruct H5 as [? [? ?]].
      exists (cut Q' x). split.
      * apply rp_cong_cut_r; auto.
      * eapply c_trans. apply c_cut_comm. apply c_cong_cut; auto.
        apply directed_cong_in_struct_cong; auto.
    - specialize IHdirected_congruence2 with Q'0.
      apply IHdirected_congruence2 in H5. destruct H5 as [? [? ?]].
      exists (cut x P'). split.
      * apply rp_cong_cut_l; auto.
      * eapply c_trans. apply c_cut_comm. apply c_cong_cut; auto.
        apply directed_cong_in_struct_cong; auto.
  + inversion H6; subst.
    - eexists. split. apply rp_refl.
      apply directed_cong_in_struct_cong in H0, H1, H2.
      apply c_trans with (cut (cut P1 Q1) R1).
      * repeat (apply c_cong_cut; auto).
      * apply c_cut_assoc; auto. intro Hfv.
        apply ((proj1 free_vars_under_struct_cong) _ _ H0 1) in Hfv. congruence.
    - destruct E; simpl in H9; try congruence.
      {
        inversion H9; subst.
        destruct (fill_hole_congruence _ _ _ _ eq_refl H1) as [E' [M' [? [? ?]]]].
        rewrite H3.
        rewrite rename_axcut_ctx_over_fill_hole.
        eexists. split.
        + apply rp_cong_cut_r. eapply rp_ax_cut_l.
          - reflexivity.
          - replace swap01 with (up_ren_n 0 swap01) by auto.
            inversion H10; subst.
            apply (edc_preserves_well_formedness _ _ _ H4) in H13.
            replace 0 with ((up_ren_n 0 swap01) 1) at 1 by auto.
            apply well_formedness_preserved_under_swap01; assumption.
          - reflexivity.
        + rewrite reduce_axcut_equation_3. apply c_cong_cut.
          - apply directed_cong_in_struct_cong.
            apply directed_cong_invariant_under_downshifting.
            apply directed_cong_invariant_under_renaming; auto; try apply swap01_is_bijective.
            apply nfv_01_swap; auto.
          - apply directed_cong_in_struct_cong.
            apply reduce_axcut_invariant_under_dc.
            * apply edc_invariant_under_renaming; auto; apply swap01_is_bijective.
            * apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
              auto.
            * apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
              apply directed_cong_invariant_under_upshifting; auto.
        + apply swap01_is_bijective.
      }
      {
        (* because of well-formedness, 0 must be free in (cons_r E P0)
           in which case 1 ∈ E. However, because of association, ~ 1 ∈ P. *)
        exfalso.
        inversion H9; subst. inversion H10; subst.
        apply well_formed_ctx_fv in H8.
        apply (fv_ctx_fill_hole _ _ (upM M)) in H8.
        congruence.
      }
    - (* use more difficult reduce_axcut / assoc lemma *)
      (*
        (reduce_axcut E M (cut P Q)) ≡
        (cut (down (swap01 P))
             (reduce_axcut (swap01 up E) (swap01 up M) (swap01 Q)))
        ≡
        (cut (down (swap01 P1))
             (reduce_axcut (swap01 up E') (swap01 up M') (swap01 Q1)))
        Needs invariance of congruence of ctxs under swap01 and shifting
      *)
      admit.
    - inversion H10; subst.
      * eexists. split. apply rp_refl.
        eapply c_trans.
        ** apply directed_cong_in_struct_cong in H0, H1, H2.
           apply c_cong_cut; eauto; apply c_cong_cut; eauto.
        ** apply c_cut_assoc; auto. apply directed_cong_in_struct_cong in H0.
           apply (nfv_under_struct_cong _ _ _ H0); auto.
      * (* use reduce_axcut / assoc lemma *)
        (* cut (reduce_axcut E M Q) R
            ≡ cut (reduce_axcut (down E swap01) (cut Q1' R1')) *)
        (* then use invariance of reduce_axcut under struct cong
        *)
        admit.
      * (* might need well-typedness to conclude that 0 not in M so that down shift possible *)
        
        (* FUCK: definition of fill_hole does not work because in E[M], no free variable 
            can be bound because we are upping at every stage! BAD!
            instead rewrite, so that M is already upshifting accordingly (syntactically identically to what we
            fill in the hole):
            rename E[M] r = (rename E r)[rename M (up_ren_n (size E) r)]
        *)
        destruct (fill_hole_congruence _ _ _ _ eq_refl H1) as [E' [M' [? [? ?]]]].
        assert (
          (* Γ ⊢ E[M] and WF E j -> ~ j ∈ M *)
          ~ (occurs_free_message 0 M')
        ) by admit.
        assert (
          (* generalization :
              ~ (S k) ∈ P
              lift (down P k 1) k 1 = rename P (up_ren_n k swap01)
          *)
          upM (downM (rename_message M' swap01)) = M'
        ).
        {
          admit.
        }
        assert (
          (cut (rename_process Q1 swap01)
               (rename_process (up R1) swap01)) =
          fill_hole (cons_r (rename_axcut_ctx E' swap01) (rename_process (up R1) swap01))
                    (downM (rename_message M' swap01))
        ).
        {
          admit.
        }
        eexists. split.
        ** rewrite H11. eapply rp_ax_cut_r; eauto.
           econstructor.
           { apply nfv_10_swap. apply nfv_lift_n; lia. }
           replace swap01 with (up_ren_n 0 swap01) by auto.
           replace 1 with ((up_ren_n 0 swap01) 0) by auto.
           apply well_formedness_preserved_under_swap01.
           eapply edc_preserves_well_formedness; eauto.
        ** rewrite reduce_axcut_equation_4; simpl.
           rewrite H9. autorewrite with up_down_rename_rewrites.
           {
              apply directed_cong_in_struct_cong in H2.
              apply c_cong_cut; auto.
              apply directed_cong_in_struct_cong.
              rewrite swap_swap_idM.
              rewrite rename_axcut_ctx_compose with (c := id); try (intros [|[|]]; simpl; auto).
              rewrite rename_axcut_ctx_id; auto.
              apply reduce_axcut_invariant_under_dc; auto.
           }
           apply nfv_01_swap. apply directed_cong_in_struct_cong in H0.
           apply (nfv_under_struct_cong _ _ _ H0); auto.
      * destruct (IHdirected_congruence1 _ H7) as [R' [? ?]].
        eexists. split.
        ** apply rp_cong_cut_l.
           assert ( down (rename_process P1 swap01) ⊵ down (rename_process R' swap01) )
            by admit.
           (* show distribution of renaming over subst only for up_subst_n j swap01
              forall n to simplify *)
           apply H5.
        ** eapply c_trans.
           {
            apply c_cong_cut. apply c_cong_cut. apply H4.
            apply directed_cong_in_struct_cong in H1; apply H1.
            apply directed_cong_in_struct_cong in H2; apply H2.
           }
           apply c_cut_assoc; auto.
           apply (nfv_under_struct_cong _ _ _ H4).
           (* set of free variables is preserved under reduction *)
           (* does this need well-typedness? no:
              show that set of free variables decreases during reduction,
              but argument with WT is simpler *)
           admit.
      * admit.
        (* needs invariances for ⊵ w.r.t. renaming/shifting *)
    - destruct (IHdirected_congruence3 Q'0 H10) as [? [? ?]].
      assert (
        rename_process (up R1) swap01 ⊵ rename_process (up x) swap01
      ) by admit.
      eexists. split.
      * apply rp_cong_cut_r. apply rp_cong_cut_r. apply H5.
      * eapply c_trans with (cut (cut P1 Q1) x).
        {
          apply directed_cong_in_struct_cong in H0.
          apply directed_cong_in_struct_cong in H1.
          apply c_cong_cut; auto. apply c_cong_cut; auto.
        }
        apply c_cut_assoc; auto.
        apply directed_cong_in_struct_cong in H0.
        pose proof ((proj1 free_vars_under_struct_cong) _ _ H0 1).
        intro Hfv. apply H7 in Hfv. congruence.
  + admit.
  + inversion H1; subst.
    - eexists; split. apply rp_refl. apply c_cong_cut; apply directed_cong_in_struct_cong; auto.
    - destruct (fill_hole_congruence _ _ _ _ eq_refl H) as [E' [M' [? [? ?]]]].
      exists (reduce_axcut E' M' Q'). split.
      {
        rewrite H2. eapply rp_ax_cut_l; eauto.
        eapply edc_preserves_well_formedness; eauto.
      }
      apply directed_cong_in_struct_cong.
      apply reduce_axcut_invariant_under_dc; auto.
    - destruct (fill_hole_congruence _ _ _ _ eq_refl H0) as [E' [M' [? [? ?]]]].
      exists (reduce_axcut E' M' P'). split.
      {
        rewrite H2. eapply rp_ax_cut_r; eauto.
        eapply edc_preserves_well_formedness; eauto.
      }
      apply directed_cong_in_struct_cong.
      apply reduce_axcut_invariant_under_dc; auto.
    - specialize IHdirected_congruence1 with P'0.
      apply IHdirected_congruence1 in H5. destruct H5 as [? [? ?]].
      exists (cut x Q'). split.
      * apply rp_cong_cut_l; auto.
      * apply c_cong_cut; auto. apply directed_cong_in_struct_cong; auto.
    - specialize IHdirected_congruence2 with Q'0.
      apply IHdirected_congruence2 in H5. destruct H5 as [? [? ?]].
      exists (cut P' x). split.
      * apply rp_cong_cut_r; auto.
      * apply c_cong_cut; auto. apply directed_cong_in_struct_cong; auto.

  (* seq *)
  + inversion H1; subst.
    - eexists. split. apply rp_refl.
      apply directed_cong_in_struct_cong in H, H0.
      apply c_cong_seq; auto.
    - eexists. split. apply rp_seq. eapply directed_cong_in_struct_cong.
      apply directed_cong_invariant_under_substitution; auto.
      intros [|]; simpl. { econstructor; eauto. }
      apply dc_cong_reflM.
    - destruct (IHdirected_congruence _ H5) as [? [? ?]].
      eexists. split.
      * apply rp_cong_seq. apply H2.
      * apply directed_cong_in_struct_cong in H, H0. apply c_cong_seq; auto.
  + inversion H0; subst. exists stop; split; eauto. apply c_refl. *)
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
  forall Γ P Q1 Q2, Γ ⊢ P :# -> P ≡ Q1 -> P ↠ Q2 -> exists R, Q1 ↠ R /\ Q2 ≡ R.
Proof.
  intros. destruct H1.
  + apply struct_cong_in_trans_directed_cong in H0.
    generalize dependent Q2.
    induction H0; intros.
    - destruct (directed_cong_equiv_red_commute _ _ _ _ H H0 H1) as [? [? ?]].
      exists x0. split; auto. left; auto.
    - destruct (directed_cong_equiv_red_commute _ _ _ _ H H0 H2) as [? [? ?]].
      destruct (IHclos_trans_1n (directed_cong_preserves_typing _ _ _ H H0) _ H3) as [? [? ?]].
      exists x1. split; auto. eapply c_trans; eauto.
  + exists P. split.
    - right. apply c_comm; auto.
    - apply c_comm; auto.
Qed.

(* ⊵ can be reconciliated via ↠ *)
Lemma equiv_red_diamond :
  forall Γ P Q1 Q2, Γ ⊢ P :# -> P ⊵ Q1 -> P ⊵ Q2 ->
    exists R, Q1 ↠ R /\ Q2 ↠ R.
Proof.
Admitted.

(* ↠ is confluent *)
(*
         P
      ↠    ↠
    Q1       Q2
      ↠    ↠
         R
*)
Lemma church_rosser_parallel_reduction :
  forall Γ P Q1 Q2, Γ ⊢ P :# -> P ↠ Q1 -> P ↠ Q2 ->
    exists R, Q1 ↠ R /\ Q2 ↠ R.
Proof.
  intros.
  destruct H0 eqn:E.
  + destruct H1.
    - eapply equiv_red_diamond; eauto.
    - destruct (struct_cong_par_red_commute _ _ _ _ H H1 H0) as [? [? ?]].
      eexists; split; eauto. right; auto.
  + destruct (struct_cong_par_red_commute _ _ _ _ H s H1) as [? [? ?]].
    eexists; split; eauto. right; auto.
Qed.

(*
         P
      ↠   ↠*
    Q1       Q2
      ↠*  ↠*
         R
*)
Lemma church_rosser_par_red_clos_trans_1n_par_red :
  forall Γ P Q1 Q2, Γ ⊢ P :# ->
    P ↠ Q1 ->
    Relation_Operators.clos_trans_1n process par_reduction P Q2 ->
    exists R,
      Relation_Operators.clos_trans_1n process par_reduction Q1 R /\
      Relation_Operators.clos_trans_1n process par_reduction Q2 R.
Proof.
  intros.
  generalize dependent Q1.
  induction H1; intros.
  + destruct (church_rosser_parallel_reduction _ _ _ _ H H0 H1) as [? [? ?]].
    eexists; split; econstructor; eauto.
  + destruct (church_rosser_parallel_reduction _ _ _ _ H H0 H2) as [? [? ?]].
    assert (Γ ⊢ y :#) by apply (par_red_preserves_typing _ _ _ H H0).
    destruct (IHclos_trans_1n H5 _ H3) as [? [? ?]].
    exists x1; split; auto.
    eapply Relation_Operators.t1n_trans; eauto.
Qed.

(*
         P
      ↠*  ↠*
    Q1       Q2
      ↠*  ↠*
         R
*)
Lemma church_rosser_par_red_clos_trans :
  forall Γ P Q1 Q2, Γ ⊢ P :# ->
    Relation_Operators.clos_trans process par_reduction P Q1 ->
    Relation_Operators.clos_trans process par_reduction P Q2 ->
    exists R,
      Relation_Operators.clos_trans process par_reduction Q1 R /\
      Relation_Operators.clos_trans process par_reduction Q2 R.
Proof.
  intros.
  apply Operators_Properties.clos_trans_t1n_iff in H0, H1.
  generalize dependent Q2.
  induction H0; intros.
  + destruct (church_rosser_par_red_clos_trans_1n_par_red _ _ _ _ H H0 H1) as [? [? ?]].
    exists x0. apply Operators_Properties.clos_trans_t1n_iff in H2, H3.
    split; auto.
  + destruct (church_rosser_par_red_clos_trans_1n_par_red _ _ _ _ H H0 H2) as [? [? ?]].
    assert (Γ ⊢ y :#) by apply (par_red_preserves_typing _ _ _ H H0).
    destruct (IHclos_trans_1n H5 _ H3) as [? [? ?]].
    exists x1. split; auto.
  apply Operators_Properties.clos_trans_t1n_iff in H4.
  eapply Relation_Operators.t_trans; eauto.
Qed.

(* ▶ is confluent *)
(*
         P
      ▶    ▶
    Q1       Q2
      ▶    ▶
         R
*)
Lemma church_rosser :
  forall Γ P Q1 Q2, Γ ⊢ P :# -> P ▶ Q1 -> P ▶ Q2 ->
    exists R, Q1 ▶ R /\ Q2 ▶ R.
Proof.
  intros.
  apply multi_step_red_in_clos_trans_par_red in H0, H1.
  destruct (church_rosser_par_red_clos_trans _ _ _ _ H H0 H1) as [R [? ?]].
  apply clos_trans_par_red_in_multi_step_red in H2, H3.
  eexists; eauto.
Qed.
