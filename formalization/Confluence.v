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
From FD Require Import EquivRedProperties.

From Stdlib Require Import Lia.

Local Hint Rewrite
  swap_swap_id
  down_after_up_process_id
  up_after_down_process_id
  up_ren_swap_swap_idM
  up_ren_swap_swap_idE
  swap_swap_idE
  down_after_up_idE
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
    - inversion H; subst.
      destruct (reduce_axcut_invariant_under_directed_cong _ _ _ _ _ _ _ eq_refl H6 H4 H0_0 H0_) as [E' [M' [? [? ?]]]].
      eexists; split.
      * rewrite H0. eapply rp_ax_cut_r; eauto. eapply edc_preserves_well_formedness; eauto.
      * apply directed_cong_in_struct_cong. assumption.
    - inversion H; subst.
      destruct (reduce_axcut_invariant_under_directed_cong _ _ _ _ _ _ _ eq_refl H7 H4 H0_ H0_0) as [E' [M' [? [? ?]]]].
      eexists; split.
      * rewrite H0. eapply rp_ax_cut_l; eauto. eapply edc_preserves_well_formedness; eauto.
      * apply directed_cong_in_struct_cong. assumption.
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
        rewrite reduce_axcut_equation_3.
        assert (
          (rename_process (fill_hole E M) swap01)
            ⇛ (rename_process Q1 swap01)
        ). { apply directed_cong_invariant_under_renaming; auto. apply swap01_is_bijective. }
        rewrite rename_axcut_ctx_over_fill_hole in H0; try apply swap01_is_bijective.
        assert (
          (rename_process (up R) swap01) ⇛ (rename_process (up R1) swap01)
        ). { apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective. apply directed_cong_invariant_under_upshifting; auto. }
        assert (
          well_formed_axcut_ctx 0 (rename_axcut_ctx E swap01)
        ).
        {
          replace 0 with (swap01 1) by auto; replace swap01 with (up_ren_n 0 swap01) by auto.
          apply well_formedness_preserved_under_swap01. inversion H8; auto.
        }
        assert (
          exists Γ,
            Γ ⊢ (fill_hole (rename_axcut_ctx E swap01) (rename_message M (up_ren_n (length_axcut_ctx E) swap01))) :#
        ).
        {
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
          inversion H4; subst. inversion H11; subst.
          destruct (swap01_preserves_well_typedness _ _ H15).
          eauto.
        }
        destruct H5.
        destruct (reduce_axcut_invariant_under_directed_cong _ _ _ _ _ _ _ eq_refl H5 H2 H1 H0) as [E' [M' [? [? ?]]]].
        eexists; split.
        + apply rp_cong_cut_r. eapply rp_ax_cut_l; eauto.
          eapply edc_preserves_well_formedness; eauto.
        + apply c_cong_cut.
          - apply directed_cong_in_struct_cong.
            apply directed_cong_invariant_under_downshifting.
            apply directed_cong_invariant_under_renaming; auto; try apply swap01_is_bijective.
            apply nfv_01_swap; auto.
          - apply directed_cong_in_struct_cong. auto.
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
    - assert (
        (cut P Q) ⇛ (cut P1 Q1)
      ). { apply dc_cong_cut; auto. }
      assert (
        exists Γ, Γ ⊢ fill_hole E M :#
      ) as Hwtfh. { inversion H4; subst. eauto. }
      destruct Hwtfh as [Γ' HΓ'].
      destruct (reduce_axcut_invariant_under_directed_cong _ _ _ _ _ _ _ eq_refl HΓ' H8 H0 H0_1) as [E' [M' [? [? ?]]]].
      rewrite H1.
      unfold up. rewrite up_ctx_over_fill_hole; rewrite <- plus_n_O.
      rewrite (rename_axcut_ctx_over_fill_hole _ _ swap01 swap01_is_bijective).
      rewrite lift_ctx_preserves_length.
      eexists. split.
      * apply rp_cong_cut_r.
        eapply rp_ax_cut_r; eauto.
        replace 0 with (swap01 1) at 1 by auto.
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01.
        apply upE_preserves_well_formedness.
        eapply edc_preserves_well_formedness; eauto.
      * subst. eapply c_trans.
        {
          apply directed_cong_in_struct_cong. apply H5.
        }
        {
          eapply c_trans.
          + assert (
              well_formed_axcut_ctx 0 (rename_axcut_ctx (upE E') swap01)
            ).
            {
              replace 0 with (swap01 1) by auto.
              replace swap01 with (up_ren_n 0 swap01) by auto.
              apply well_formedness_preserved_under_swap01.
              apply upE_preserves_well_formedness.
              eapply edc_preserves_well_formedness; eauto.
            }
            pose proof (
              permute_cut_assoc_reduce_axcut
                (down (rename_process P1 swap01))
                (rename_axcut_ctx (upE E') swap01)
                (rename_message (lift_message M' (length_axcut_ctx E') 1) (up_ren_n (length_axcut_ctx E') swap01))
                (rename_process Q1 swap01)
                H1
            ).
            eapply c_comm. eapply c_trans. apply H6; clear H6.
            - apply nfv_ctx_10_swap. unfold upE.
              apply nfv_lift_nE; lia.
            - rewrite <- rename_axcut_ctx_preserves_length.
              unfold upE; rewrite lift_ctx_preserves_length.
              replace (length_axcut_ctx E')
                 with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
                   at 1 by (rewrite up_ren_n_swap_Sn; auto).
              apply nfv_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              intro Hfv.
              apply fv_up_Sn2' in Hfv; try lia.
              inversion H4; subst.
              apply directed_cong_in_struct_cong in H0_1.
              apply ((proj1 struct_cong_preserves_typing) _ _ H0_1) in H12.
              eapply edc_preserves_well_formedness in H8; eauto.
              eapply nfv_well_typed_fill_hole; eauto. rewrite <- plus_n_O.
              assumption.
            - rewrite <- rename_axcut_ctx_preserves_length.
              unfold upE; rewrite lift_ctx_preserves_length.
              replace (S (length_axcut_ctx E'))
                 with (up_ren_n (length_axcut_ctx E') swap01 (length_axcut_ctx E'))
                   by (rewrite up_ren_n_swap_n; auto).
              apply nfv_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              apply nfv_lift_n; lia.
            - rewrite swap_swap_id.
              assert (
                ~ 0 ∈ rename_process P1 swap01
              ).
              {
                apply nfv_01_swap.
                apply directed_cong_in_struct_cong in H0_.
                eapply nfv_under_struct_cong; eauto.
              }
              rewrite <- rename_axcut_ctx_preserves_length with (r := swap01).
              unfold upE, downE; rewrite lift_ctx_preserves_length.
              autorewrite with up_down_rename_rewrites; eauto.
              rewrite (proj1 (proj2 down_after_up_id)).
              apply c_refl.
          + apply c_refl.
        }
    - inversion H8; subst.
      * eexists. split. apply rp_refl.
        eapply c_trans.
        ** apply directed_cong_in_struct_cong in H0_, H0_0, H0_1.
           apply c_cong_cut; eauto; apply c_cong_cut; eauto.
        ** apply c_cut_assoc; auto. apply directed_cong_in_struct_cong in H0_.
           apply (nfv_under_struct_cong _ _ _ H0_); auto.
      * assert (
          (down (rename_process (fill_hole E M) swap01)) ⇛
            (down (rename_process P1 swap01))
        ) as Hcong_ctx.
        {
          apply directed_cong_invariant_under_downshifting.
          + apply directed_cong_invariant_under_renaming; auto.
            apply swap01_is_bijective.
          + apply nfv_01_swap; auto.
        }
        rewrite rename_axcut_ctx_over_fill_hole in Hcong_ctx; try apply swap01_is_bijective.
        unfold down in Hcong_ctx; rewrite down_ctx_over_fill_hole in Hcong_ctx.
        assert (
          (cut (rename_process (up R) swap01) (rename_process Q swap01))
            ⇛ (cut (rename_process Q1 swap01) (rename_process (up R1) swap01))
        ).
        {
          apply dc_cut_comm; apply directed_cong_invariant_under_renaming; auto;
          try apply swap01_is_bijective. apply directed_cong_invariant_under_upshifting; auto.
        }
        assert (
          well_formed_axcut_ctx 0 (down1_ctx (rename_axcut_ctx E swap01) 0)
        ).
        {
          apply downE_preserves_well_formedness_nfv; try lia.
          + apply nfv_ctx_01_swap.
            apply (proj1 (nfv_fill_hole _ _ _ H)).
          + replace 1 with (swap01 0) by auto; replace swap01 with (up_ren_n 0 swap01) by auto.
            apply well_formedness_preserved_under_swap01; auto.
        }
        assert (
          exists Γ,
            Γ ⊢ (fill_hole (down1_ctx (rename_axcut_ctx E swap01) 0)
                  (down1_message (rename_message M (up_ren_n (length_axcut_ctx E) swap01))
                    (length_axcut_ctx (rename_axcut_ctx E swap01) + 0))) :#
        ) as Hwtfh.
        {
          rewrite <- down_ctx_over_fill_hole.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
          inversion H4; subst. inversion H10; subst. destruct Γ3; try now inversion H9.
          apply swap01_preserves_typing in H13.
          assert (
            ~ 0 ∈ rename_process (fill_hole E M) swap01
          ). { apply nfv_01_swap; auto. }
          destruct o.
          + assert (lookup 0 (Some t :: Some A0 :: Γ3) = Some t) by auto.
            pose proof ((proj1 formula_property) _ _ _ _ H13 H6).
            congruence.
          + replace (None :: Some A0 :: Γ3) with (nil ++ None :: Some A0 :: Γ3) in H13 by auto.
            replace 0 with (@length (option Types.type) nil) in H2 by auto.
            eapply ((proj1 down_shift_sound) _ _ _ H2) in H13. eauto.
        }
        destruct Hwtfh as [Γ' HΓ'].
        destruct (reduce_axcut_invariant_under_directed_cong _ _ _ _ _ _ _ eq_refl HΓ' H1 H0 Hcong_ctx) as [E' [M' [? [? ?]]]].
        eexists; split.
        { eapply rp_ax_cut_l; eauto. eapply edc_preserves_well_formedness; eauto. }
        {
          eapply c_trans. apply c_cut_comm.
          eapply c_trans.
          + apply permute_cut_assoc_reduce_axcut; eauto.
            - apply (proj1 (nfv_fill_hole _ _ _ H)).
            - rewrite (plus_n_O (length_axcut_ctx E)).
              inversion H4; subst. inversion H13; subst.
              eapply nfv_well_typed_fill_hole; eauto.
            - replace (S (length_axcut_ctx E)) with (length_axcut_ctx E + 1) by lia.
              apply (proj2 (nfv_fill_hole _ _ _ H)).
          + apply directed_cong_in_struct_cong.
            rewrite <- plus_n_O in H7.
            rewrite <- rename_axcut_ctx_preserves_length in H7.
            apply H7.
        }
      * assert (
          exists Γ, Γ ⊢ fill_hole E M :#
        ) as Hwtfh. { inversion H4; subst. inversion H7; subst. eauto. }
        destruct Hwtfh as [Γ' HΓ'].
        destruct (reduce_axcut_invariant_under_directed_cong _ _ _ _ _ _ _ eq_refl HΓ' H5 H0_ H0_0) as [E' [M' [? [? ?]]]].
        rewrite H0.
        eexists; split.
        ** rewrite rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
           eapply rp_ax_cut_r with
            (E := cons_r (rename_axcut_ctx E' swap01) (rename_process (up R1) swap01))
            (M := rename_message M' (up_ren_n (length_axcut_ctx E') swap01));
           eauto.
           econstructor.
           -- apply nfv_10_swap. apply nfv_lift_n. lia.
           -- replace 1 with (swap01 0) by auto.
              replace swap01 with (up_ren_n 0 swap01) by auto.
              apply well_formedness_preserved_under_swap01.
              eapply edc_preserves_well_formedness; eauto.
        ** remember (length_axcut_ctx E').
           rewrite reduce_axcut_equation_4.
           apply c_cong_cut.
           -- rewrite swap_swap_idE.
              autorewrite with up_down_rename_rewrites.
              {
                apply directed_cong_in_struct_cong.
                rewrite <- rename_axcut_ctx_preserves_length.
                rewrite <- Heqn.
                rewrite up_ren_swap_swap_idM.
                assumption.
              }
              {
                apply nfv_01_swap. eapply nfv_under_struct_cong; eauto.
                apply directed_cong_in_struct_cong; auto.
              }
           -- autorewrite with up_down_rename_rewrites.
              apply directed_cong_in_struct_cong; auto.
      * inversion H4; subst. inversion H7; subst.
        destruct (IHdirected_congruence1 _ H5 _ H11) as [R' [? ?]].
        eexists; split.
        ** apply rp_cong_cut_l.
           apply directed_cong_in_struct_cong in H0_.
           apply ((proj1 struct_cong_preserves_typing) _ _ H0_) in H11.
           destruct Γ3. inversion H6.
           eapply equiv_red_invariant_under_down.
           -- eapply swap01_preserves_typing. apply H11.
           -- replace swap01 with (up_ren_n 0 swap01) by auto.
              eapply equiv_red_invariant_under_swap; eauto.
           -- apply nfv_01_swap. eapply nfv_under_struct_cong; eauto.
        ** eapply c_trans.
           { apply directed_cong_in_struct_cong in H0_0, H0_1.
             apply c_cong_cut. apply c_cong_cut. apply H1. apply H0_0. apply H0_1. }
           eapply c_cut_assoc; eauto. apply directed_cong_in_struct_cong in H0_1.
           apply directed_cong_in_struct_cong in H0_.
           pose proof (proj1 ((proj1 struct_cong_preserves_typing) _ _ H0_ _) H11).
           apply (equiv_red_preserves_typing _ _ _ H10) in H0.
           intro Hfv.
           destruct ((proj1 free_var_in_ctx) _ _ Hfv _ H0) as [? ?].
           apply ((proj1 formula_property) _ _ _ _ H11) in H13.
           congruence.
      * inversion H4; subst. inversion H7; subst.
        destruct (IHdirected_congruence2 _ H5 _ H12) as [R' [? ?]].
        eexists; split.
        ** apply rp_cong_cut_r. apply rp_cong_cut_l.
           replace swap01 with (up_ren_n 0 swap01) by auto.
           eapply equiv_red_invariant_under_swap; eauto.
           apply directed_cong_in_struct_cong in H0_0.
           eapply struct_cong_preserves_typing. apply c_comm in H0_0.
           eauto. eauto.
        ** eapply c_trans.
           { apply directed_cong_in_struct_cong in H0_, H0_1.
             eapply c_cong_cut; eauto. apply c_cong_cut; eauto. }
           simpl. apply c_cut_assoc; eauto.
           apply directed_cong_in_struct_cong in H0_.
           eapply nfv_under_struct_cong; eauto.
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
    - assert (
        (cut Q R) ⇛ (cut R1 Q1)
      ). { apply dc_cut_comm; auto. }
      assert (
          exists Γ, Γ ⊢ fill_hole E M :#
        ) as Hwtfh. { inversion H4; subst. eauto. }
      destruct Hwtfh as [Γ' HΓ'].
      destruct (reduce_axcut_invariant_under_directed_cong _ _ _ _ _ _ _ eq_refl HΓ' H8 H0 H0_) as [E' [M' [? [? ?]]]].
      rewrite H1.
      unfold up. rewrite up_ctx_over_fill_hole; rewrite <- plus_n_O.
      rewrite (rename_axcut_ctx_over_fill_hole _ _ swap01 swap01_is_bijective).
      rewrite lift_ctx_preserves_length.
      eexists. split.
      * apply rp_cong_cut_l.
        eapply rp_ax_cut_l; eauto.
        replace 0 with (swap01 1) at 1 by auto.
        replace swap01 with (up_ren_n 0 swap01) by auto.
        apply well_formedness_preserved_under_swap01.
        apply upE_preserves_well_formedness.
        eapply edc_preserves_well_formedness; eauto.
      * subst. eapply c_trans.
        {
          apply directed_cong_in_struct_cong. apply H5.
        }
        {
          eapply c_trans.
          + assert (
              well_formed_axcut_ctx 0 (rename_axcut_ctx (upE E') swap01)
            ).
            {
              replace 0 with (swap01 1) by auto.
              replace swap01 with (up_ren_n 0 swap01) by auto.
              apply well_formedness_preserved_under_swap01.
              apply upE_preserves_well_formedness.
              eapply edc_preserves_well_formedness; eauto.
            }
            pose proof (
              permute_cut_assoc_reduce_axcut
                (down (rename_process R1 swap01))
                (rename_axcut_ctx (upE E') swap01)
                (rename_message (lift_message M' (length_axcut_ctx E') 1) (up_ren_n (length_axcut_ctx E') swap01))
                (rename_process Q1 swap01)
                H1
            ).
            eapply c_comm. eapply c_trans. apply H6; clear H6.
            - apply nfv_ctx_10_swap. unfold upE.
              apply nfv_lift_nE; lia.
            - rewrite <- rename_axcut_ctx_preserves_length.
              unfold upE; rewrite lift_ctx_preserves_length.
              replace (length_axcut_ctx E')
                 with (up_ren_n (length_axcut_ctx E') swap01 (S (length_axcut_ctx E')))
                   at 1 by (rewrite up_ren_n_swap_Sn; auto).
              apply nfv_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              intro Hfv.
              apply fv_up_Sn2' in Hfv; try lia.
              inversion H4; subst.
              apply directed_cong_in_struct_cong in H0_.
              apply ((proj1 struct_cong_preserves_typing) _ _ H0_) in H11.
              eapply edc_preserves_well_formedness in H8; eauto.
              eapply nfv_well_typed_fill_hole; eauto. rewrite <- plus_n_O.
              assumption.
            - rewrite <- rename_axcut_ctx_preserves_length.
              unfold upE; rewrite lift_ctx_preserves_length.
              replace (S (length_axcut_ctx E'))
                 with (up_ren_n (length_axcut_ctx E') swap01 (length_axcut_ctx E'))
                   by (rewrite up_ren_n_swap_n; auto).
              apply nfv_under_renaming.
              apply up_ren_n_preserves_bijection; apply swap01_is_bijective.
              apply nfv_lift_n; lia.
            - rewrite swap_swap_id.
              assert (
                ~ 0 ∈ rename_process R1 swap01
              ).
              {
                apply nfv_01_swap.
                apply directed_cong_in_struct_cong in H0_1.
                eapply nfv_under_struct_cong; eauto.
              }
              rewrite <- rename_axcut_ctx_preserves_length with (r := swap01).
              unfold upE, downE; rewrite lift_ctx_preserves_length.
              autorewrite with up_down_rename_rewrites; eauto.
              rewrite (proj1 (proj2 down_after_up_id)).
              apply c_refl.
          + apply c_cut_comm.
        }
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
        inversion H7; subst.
        rewrite reduce_axcut_equation_4.
        assert (
          (rename_process (fill_hole E M) swap01)
            ⇛ (rename_process Q1 swap01)
        ). { apply directed_cong_invariant_under_renaming; auto. apply swap01_is_bijective. }
        rewrite rename_axcut_ctx_over_fill_hole in H0; try apply swap01_is_bijective.
        assert (
          (rename_process (up P) swap01) ⇛ (rename_process (up P1) swap01)
        ). { apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective. apply directed_cong_invariant_under_upshifting; auto. }
        assert (
          well_formed_axcut_ctx 0 (rename_axcut_ctx E swap01)
        ).
        {
          replace 0 with (swap01 1) by auto; replace swap01 with (up_ren_n 0 swap01) by auto.
          apply well_formedness_preserved_under_swap01. inversion H8; auto.
        }
        assert (
          exists Γ,
            Γ ⊢ (fill_hole (rename_axcut_ctx E swap01) (rename_message M (up_ren_n (length_axcut_ctx E) swap01))) :#
        ) as Hwtfh.
        {
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
          inversion H4; subst. inversion H12; subst.
          destruct (swap01_preserves_well_typedness _ _ H14).
          eauto.
        }
        destruct Hwtfh as [Γ' HΓ'].
        destruct (reduce_axcut_invariant_under_directed_cong _ _ _ _ _ _ _ eq_refl HΓ' H2 H1 H0) as [E' [M' [? [? ?]]]].
        eexists; split.
        + apply rp_cong_cut_l. eapply rp_ax_cut_r; auto.
          inversion H8; subst.
          replace swap01 with (up_ren_n 0 swap01) by auto. apply H5.
          eapply edc_preserves_well_formedness; eauto.
        + apply c_cong_cut.
          - apply directed_cong_in_struct_cong. assumption.
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
    - inversion H8; subst.
      * eexists. split. apply rp_refl.
        eapply c_trans.
        ** apply directed_cong_in_struct_cong in H0_, H0_0, H0_1.
           apply c_cong_cut; eauto; apply c_cong_cut; eauto.
        ** eapply c_trans. apply c_cut_comm.
           eapply c_trans. apply c_cong_cut. apply c_cut_comm. apply c_refl.
           eapply c_trans. apply c_cut_assoc; auto.
           apply directed_cong_in_struct_cong in H0_1. eapply nfv_under_struct_cong; eauto.
           eapply c_trans. apply c_cut_comm. apply c_cong_cut. apply c_cut_comm. apply c_refl.
      * assert (
          exists Γ, Γ ⊢ fill_hole E M :#
        ) as Hwtfh. { inversion H4; subst. inversion H9; subst. eauto. }
        destruct Hwtfh as [Γ' HΓ'].
        destruct (reduce_axcut_invariant_under_directed_cong _ _ _ _ _ _ _ eq_refl HΓ' H5 H0_1 H0_0) as [E' [M' [? [? ?]]]].
        rewrite H0.
        eexists; split.
        ** rewrite rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
           eapply rp_ax_cut_l with
            (E := cons_l (rename_process (up P1) swap01) (rename_axcut_ctx E' swap01))
            (M := rename_message M' (up_ren_n (length_axcut_ctx E') swap01));
           eauto.
           econstructor.
           -- apply nfv_10_swap. apply nfv_lift_n. lia.
           -- replace 1 with (swap01 0) by auto.
              replace swap01 with (up_ren_n 0 swap01) by auto.
              apply well_formedness_preserved_under_swap01.
              eapply edc_preserves_well_formedness; eauto.
        ** remember (length_axcut_ctx E').
           rewrite reduce_axcut_equation_3.
           apply c_cong_cut.
           -- autorewrite with up_down_rename_rewrites.
              apply directed_cong_in_struct_cong; auto.
           -- rewrite swap_swap_idE.
              autorewrite with up_down_rename_rewrites.
              {
                apply directed_cong_in_struct_cong.
                rewrite <- rename_axcut_ctx_preserves_length.
                rewrite <- Heqn.
                rewrite up_ren_swap_swap_idM.
                assumption.
              }
              {
                apply nfv_01_swap. eapply nfv_under_struct_cong; eauto.
                apply directed_cong_in_struct_cong; auto.
              }
      * assert (
          (down (rename_process (fill_hole E M) swap01)) ⇛
            (down (rename_process R1 swap01))
        ) as Hcong_ctx.
        {
          apply directed_cong_invariant_under_downshifting.
          + apply directed_cong_invariant_under_renaming; auto.
            apply swap01_is_bijective.
          + apply nfv_01_swap; auto.
        }
        rewrite rename_axcut_ctx_over_fill_hole in Hcong_ctx; try apply swap01_is_bijective.
        unfold down in Hcong_ctx; rewrite down_ctx_over_fill_hole in Hcong_ctx.
        assert (
          (cut (rename_process (up P) swap01) (rename_process Q swap01))
            ⇛ (cut (rename_process (up P1) swap01) (rename_process Q1 swap01))
        ).
        {
          apply dc_cong_cut; apply directed_cong_invariant_under_renaming; auto;
          try apply swap01_is_bijective. apply directed_cong_invariant_under_upshifting; auto.
        }
        assert (
          well_formed_axcut_ctx 0 (down1_ctx (rename_axcut_ctx E swap01) 0)
        ).
        {
          apply downE_preserves_well_formedness_nfv; try lia.
          + apply nfv_ctx_01_swap.
            apply (proj1 (nfv_fill_hole _ _ _ H)).
          + replace 1 with (swap01 0) by auto; replace swap01 with (up_ren_n 0 swap01) by auto.
            apply well_formedness_preserved_under_swap01; auto.
        }
        assert (
          exists Γ,
            Γ ⊢ (fill_hole (down1_ctx (rename_axcut_ctx E swap01) 0)
                  (down1_message (rename_message M (up_ren_n (length_axcut_ctx E) swap01))
                    (length_axcut_ctx (rename_axcut_ctx E swap01) + 0))) :#
        ) as Hwtfh.
        {
          rewrite <- down_ctx_over_fill_hole.
          rewrite <- rename_axcut_ctx_over_fill_hole; try apply swap01_is_bijective.
          inversion H4; subst. inversion H11; subst. destruct Γ4; try now inversion H9.
          apply swap01_preserves_typing in H14.
          assert (
            ~ 0 ∈ rename_process (fill_hole E M) swap01
          ). { apply nfv_01_swap; auto. }
          destruct o.
          + assert (lookup 0 (Some t :: Some (Types.dual A0) :: Γ4) = Some t) by auto.
            pose proof ((proj1 formula_property) _ _ _ _ H14 H6).
            congruence.
          + replace (None :: Some (Types.dual A0) :: Γ4) with (nil ++ None :: Some (Types.dual A0) :: Γ4) in H14 by auto.
            replace 0 with (@length (option Types.type) nil) in H2 by auto.
            eapply ((proj1 down_shift_sound) _ _ _ H2) in H14. eauto.
        }
        destruct Hwtfh as [Γ' HΓ'].
        destruct (reduce_axcut_invariant_under_directed_cong _ _ _ _ _ _ _ eq_refl HΓ' H1 H0 Hcong_ctx) as [E' [M' [? [? ?]]]].
        eexists; split.
        { eapply rp_ax_cut_r; eauto. eapply edc_preserves_well_formedness; eauto. }
        {
          eapply c_trans. apply c_cut_comm.
          eapply c_trans.
          + eapply c_trans. apply c_cut_comm.
            apply permute_cut_assoc_reduce_axcut; eauto.
            - apply (proj1 (nfv_fill_hole _ _ _ H)).
            - rewrite (plus_n_O (length_axcut_ctx E)).
              inversion H4; subst. inversion H14; subst.
              eapply nfv_well_typed_fill_hole; eauto.
            - replace (S (length_axcut_ctx E)) with (length_axcut_ctx E + 1) by lia.
              apply (proj2 (nfv_fill_hole _ _ _ H)).
          + apply directed_cong_in_struct_cong.
            rewrite <- plus_n_O in H7.
            rewrite <- rename_axcut_ctx_preserves_length in H7.
            apply H7.
        }
      * inversion H4; subst. inversion H9; subst.
        destruct (IHdirected_congruence2 _ H5 _ H11) as [R' [? ?]].
        eexists; split.
        ** apply rp_cong_cut_l. apply rp_cong_cut_r.
           replace swap01 with (up_ren_n 0 swap01) by auto.
           eapply equiv_red_invariant_under_swap; eauto.
           apply directed_cong_in_struct_cong in H0_0.
           eapply struct_cong_preserves_typing. apply c_comm in H0_0.
           eauto. eauto.
        ** eapply c_trans.
           { apply directed_cong_in_struct_cong in H0_, H0_1.
             eapply c_cong_cut; eauto. apply c_cong_cut; eauto. }
           simpl.
           eapply c_trans. apply c_cut_comm. eapply c_trans. eapply c_cong_cut. apply c_cut_comm. apply c_refl.
           eapply c_trans. apply c_cut_assoc; eauto.
           apply directed_cong_in_struct_cong in H0_1.
           eapply nfv_under_struct_cong; eauto.
           eapply c_trans. apply c_cut_comm. apply c_cong_cut. apply c_cut_comm. apply c_refl.
      * inversion H4; subst. inversion H9; subst.
        destruct (IHdirected_congruence3 _ H5 _ H12) as [R' [? ?]].
        eexists; split.
        ** apply rp_cong_cut_r.
           apply directed_cong_in_struct_cong in H0_1.
           apply ((proj1 struct_cong_preserves_typing) _ _ H0_1) in H12.
           destruct Γ4. inversion H6.
           eapply equiv_red_invariant_under_down.
           -- eapply swap01_preserves_typing; eauto.
           -- replace swap01 with (up_ren_n 0 swap01) by auto.
              eapply equiv_red_invariant_under_swap; eauto.
           -- apply nfv_01_swap. eapply nfv_under_struct_cong; eauto.
        ** eapply c_trans.
           { apply directed_cong_in_struct_cong in H0_, H0_0.
             apply c_cong_cut. apply H0_. apply c_cong_cut. apply H0_0. apply H1. }
           eapply c_trans. apply c_cut_comm.
           eapply c_trans. apply c_cong_cut. apply c_cut_comm. apply c_refl.
           eapply c_trans. apply c_cut_assoc; auto.
           -- apply directed_cong_in_struct_cong in H0_1.
              pose proof (proj1 ((proj1 struct_cong_preserves_typing) _ _ H0_1 _) H12).
              apply (equiv_red_preserves_typing _ _ _ H10) in H0.
              intro Hfv.
              destruct ((proj1 free_var_in_ctx) _ _ Hfv _ H0) as [? ?].
              apply ((proj1 formula_property) _ _ _ _ H12) in H13.
              congruence.
           -- eapply c_trans. apply c_cut_comm. apply c_cong_cut.
              apply c_cut_comm. apply c_refl.
  + inversion H1; subst.
    - eexists; split. apply rp_refl. apply c_cong_cut; apply directed_cong_in_struct_cong; auto.
    - inversion H; subst.
      destruct (reduce_axcut_invariant_under_directed_cong _ _ _ _ _ _ _ eq_refl H6 H4 H0_0 H0_) as [E' [M' [? [? ?]]]].
      eexists. split.
      * rewrite H0. eapply rp_ax_cut_l; eauto. eapply edc_preserves_well_formedness; eauto.
      * apply directed_cong_in_struct_cong. subst. auto.
    - inversion H; subst.
      destruct (reduce_axcut_invariant_under_directed_cong _ _ _ _ _ _ _ eq_refl H7 H4 H0_ H0_0) as [E' [M' [? [? ?]]]].
      eexists. split.
      * rewrite H0. eapply rp_ax_cut_r; eauto. eapply edc_preserves_well_formedness; eauto.
      * apply directed_cong_in_struct_cong. subst. auto.
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
Qed.

Print Assumptions directed_cong_equiv_red_commute.

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
  intros.
  generalize dependent Q2.
  generalize dependent Γ.
  induction H0; intros.
  (* refl *)
  + eexists; split; econstructor; eauto. apply rp_refl.
  (* link *)
  + inversion H1; subst; eexists; (split; econstructor; [apply rp_refl | econstructor; eauto]).
  + inversion H1; subst; eexists; (split; econstructor; [apply rp_refl | econstructor; eauto]).
  + inversion H1; subst; eexists; (split; econstructor; [apply rp_refl | econstructor; eauto]).
  + inversion H1; subst; eexists; (split; econstructor; [apply rp_refl | econstructor; eauto]).
  + inversion H1; subst; eexists; (split; econstructor; [apply rp_refl | econstructor; eauto]).
  + inversion H1; subst; eexists; (split; econstructor; [apply rp_refl | econstructor; eauto]).
  + inversion H1; subst; eexists; (split; econstructor; [apply rp_refl | econstructor; eauto]).
  + inversion H1; subst; eexists; (split; econstructor; [apply rp_refl | econstructor; eauto]).
  (* axcut *)
  + inversion H3; subst; admit.
  + inversion H3; subst; admit.
  (* seq *)
  + inversion H1; subst.
    - eexists; split; econstructor.
      * apply rp_refl.
      * econstructor.
    - eexists; split; econstructor; apply rp_refl.
    - eexists; split.
      * econstructor. inversion H; eapply equiv_red_invariant_under_substitution; eassumption.
      * repeat econstructor.
  (* cut cong *)
  + inversion H1; subst; admit.
  + inversion H1; subst; admit.
  (* seq cong *)
  + inversion H1; subst.
    - eexists; split; econstructor.
      * apply rp_refl.
      * apply rp_cong_seq; eauto.
    - eexists; split.
      * econstructor. apply rp_seq.
      * econstructor. inversion H; eapply equiv_red_invariant_under_substitution; eassumption.
    - inversion H; subst.
      destruct (IHequiv_reduces _ H7 _ H5) as [R [? ?]].
      eexists; split.
      * inversion H2;
        [apply or_introl; eapply rp_cong_seq | apply or_intror; apply c_cong_seq];
        eauto. apply struct_cong_reflS.
      * inversion H3;
        [apply or_introl; eapply rp_cong_seq | apply or_intror; apply c_cong_seq];
        eauto. apply struct_cong_reflS.
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
