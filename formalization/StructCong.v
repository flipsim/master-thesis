From FD Require Import Syntax.
From FD Require Import Types.
From FD Require Import Typing.
From FD Require Import Contexts.
From FD Require Import Renaming.
From FD Require Import FreeVars.

Import List.ListNotations.
Open Scope list_scope.

Reserved Notation "P '≡' Q" (no associativity, at level 1).
Reserved Notation "M '!≡' N" (no associativity, at level 1).
Reserved Notation "s '$≡' r" (no associativity, at level 1).

(*
  Note: Conceptually, structural congruence is a relation on typing derivation,
  not on terms. We represent structural congruence as a relation on terms.
  Thus, in order for congruence to preserve typing, c_cut_assoc has to
  make additional assumptions.

  One option would be to explicitly require the following judgements:
    None :: A      .: Γ ⊢ P :#
    B    .: dual A .: Δ ⊢ Q :#
    dual B         .: Ξ ⊢ R :#
  For Free Deduction, is suffices to assume that 0 and 1 are free in Q.
  (0 has to be free in Q, otherwise (cut P' (cut Q' R')) may be well-typed
   if 0 is free in R' instead but (cut (cut P Q) R) wouldn't be well-typed
   in this case. This is exactly the case that the judgements above avoid,
   since otherwise there wouldn't be a proper context split)
  (This is an important property of Free Deduction: the formula property:
   every occurence of a variable can be traced back to an axiom, even in
   the presence of substructural rules)
*)
Inductive structural_congruence : process -> process -> Prop :=
  (* axioms for equivalence of processes *)
  | c_link : forall x y,
              (link (future x) (future y)) ≡ (link (future y) (future x))
  | c_cut_comm : forall P Q,
                  (cut P Q) ≡ (cut Q P)
  | c_cut_assoc : forall P Q R P' Q' R',
                    ~ (1 ∈ P) /\ ~ (1 ∈ R') -> (* these premises guarantee that the typing judgements have the proper form *)
                    P' = down (rename_process P swap01) ->
                    Q' = rename_process Q swap01 ->
                    R' = rename_process (up R) swap01 ->
                    (cut (cut P Q) R) ≡ (cut P' (cut Q' R'))

  (* rules to make the relation an equivalence *)
  | c_refl : forall P, P ≡ P
  | c_comm : forall P Q, P ≡ Q -> Q ≡ P
  | c_trans : forall P Q R, P ≡ Q -> Q ≡ R -> P ≡ R

  (* rules to make the relation a congruence *)
  | c_cong_link : forall m1 m1' m2 m2',
                    m1 !≡ m1' -> m2 !≡ m2' -> (link m1 m2) ≡ (link m1' m2')
  | c_cong_cut : forall P P' Q Q',
                  P ≡ P' -> Q ≡ Q' -> (cut P Q) ≡ (cut P' Q')
  | c_cong_seq : forall P P' s s',
                  P ≡ P' -> s $≡ s' -> (seq P s) ≡ (seq P' s')
where
  "P '≡' Q" := (structural_congruence P Q)

with structural_congruence_message : message -> message -> Prop :=
  | c_cong_fut : forall n, (future n) !≡ (future n)
  | c_cong_prefix : forall s s', s $≡ s' -> (prefix s) !≡ (prefix s')
where
  "M '!≡' N" := (structural_congruence_message M N)

with structural_congruence_statement : statement -> statement -> Prop :=
  | c_cong_choose_l : forall P P',
                        P ≡ P' ->
                        (choose_left P) $≡ (choose_left P')
  | c_cong_choose_r : forall P P',
                        P ≡ P' ->
                        (choose_right P) $≡ (choose_right P')
  | c_cong_choice : forall P P' Q Q',
                      P ≡ P' -> Q ≡ Q' -> (offer_choice P Q) $≡ (offer_choice P' Q')
  | c_cong_send : forall P P' Q Q',
                    P ≡ P' -> Q ≡ Q' -> (send P Q) $≡ (send P' Q')
  | c_cong_receive : forall P P', P ≡ P' -> (receive P) $≡ (receive P')
  | c_cong_close : close $≡ close
  | c_cong_wait : forall P P', P ≡ P' -> (wait P) $≡ (wait P')
where
  "s '$≡' r" := (structural_congruence_statement s r).

(* Mutual induction principle for strucutral congruence *)
Scheme struct_congP_ind := Induction for structural_congruence Sort Prop
  with struct_congM_ind := Induction for structural_congruence_message Sort Prop
  with struct_congS_ind := Induction for structural_congruence_statement Sort Prop.
Combined Scheme struct_cong_ind from struct_congP_ind, struct_congM_ind, struct_congS_ind.

(* Typing is invariant under structural congruence *)
Lemma struct_cong_preserves_typing :
  (forall (p p' : process), p ≡ p' ->
    forall Γ, Γ ⊢ p :# <-> Γ ⊢ p' :#)
  /\
  (forall (m m' : message), m !≡ m' ->
    forall Γ A, Γ ⊢ m :! A <-> Γ ⊢ m' :! A)
  /\
  (forall (s s' : statement), s $≡ s' ->
    forall Γ A, Γ ⊢ s :$ A <-> Γ ⊢ s' :$ A).
Proof.
  apply struct_cong_ind; intros;
  (* Immediately finish congruence cases by applying the induction hypothesis *)
  try now (
    split; intros H_wellty; inversion H_wellty; subst; econstructor; eauto;
    try apply H; try apply H0; eauto
  ).
  (* c_link *)
  + split; intros;
    inversion H; subst;
    apply ctx_comm in H2;
    rewrite <- dual_involutive in H4;
    econstructor; eauto.
  (* c_cut_comm *)
  + split; intros;
    inversion H; subst;
    apply ctx_comm in H2;
    rewrite <- dual_involutive in H4 at 1;
    econstructor; eauto.
  (* c_cut_assoc *)
  + split; intros.
    {
      subst.
      inversion H. inversion H4; subst.
      destruct Γ4.
      + inversion H8.
      + (* 1 is None in Γ4 *)
        destruct o.
        { exfalso.
          eapply ((proj1 formula_property) _ _ 1) in H10.
          + destruct a; contradiction.
          + simpl. reflexivity.
        }
        (* destruct free_var_in_ctx as [? [_ _]].
        destruct a as [H_fv0 [H_fv1 H_nfv1]].
        destruct (H0 1 Q H_fv1 _ H11).
        simpl in H1. destruct Γ5; inversion H1; subst. *)
        inversion H8; subst.
        inversion H9; subst.

        (* show that P' is well-typed *)
        assert ( None :: (A0 .: Γ4) ⊢ rename_process P swap01 :# ) as H_swap_P.
        { eapply swap01_preserves_typing. assumption. }
        assert ( A0 .: Γ4 ⊢ down (rename_process P swap01) :# ) as H_P'.
        {
          assert (~ (0 ∈ rename_process P swap01)).
          { eapply (proj1 ctx_none_not_free); eauto. }
          replace (0) with (@length (option type) nil) in H0; auto.
          eapply ((proj1 down_shift_sound) _ _ _ H0); auto.
        }

        (* show that Q' is well-typed *)
        assert ( A .: (dual A0 .: Γ6) ⊢ rename_process Q swap01 :# ) as H_Q'.
        { eapply swap01_preserves_typing. assumption. }

        (* show that R' is well-typed *)
        assert (None :: ((dual A ) .: Γ2) ⊢ up R :# ) as H_upR.
        { eapply ((proj1 up_shift_sound) R nil ((dual A ) .: Γ2)). auto. }
        assert ( dual A .: (None :: Γ2) ⊢ rename_process (up R) swap01 :# ) as H_R'.
        { eapply swap01_preserves_typing. assumption. }

        (* determine new context splits *)
        assert ( exists Γ', Γ' ≜ Γ6 ∘ Γ2 /\ Γ ≜ Γ4 ∘ Γ' ) as H_new_split.
        { eapply ctx_assoc; eauto. }
        destruct H_new_split as [Γ' [? ?]].

        econstructor.
        - apply H1.
        - apply H_P'.
        - econstructor.
          * assert ( (dual A0 .: Γ') ≜ (dual A0 .: Γ6) ∘ (None :: Γ2)).
            { repeat econstructor; eauto. }
            apply H3.
          * apply H_Q'.
          * apply H_R'.
    }
    {
      subst.
      inversion H; subst.

      (* P is well-typed *)
      assert ( A .: None :: Γ1 ⊢ P :# ) as H_P.
      {
        assert (~ (0 ∈ rename_process P swap01)).
        {
          change 0 with (swap01 1).
          eapply (proj1 nfv_renaming).
          + apply swap01_is_bijective.
          + apply (proj1 a).
        }

        assert (None :: (A .: Γ1) ⊢ rename_process P swap01 :#).
        { eapply (proj2 ((proj1 down_shift_sound) _ nil _ H0)); auto. }

        apply swap01_preserves_typing in H1.
          rewrite ((proj1 renamings_compose) P swap01 swap01 id) in H1.
          - rewrite (proj1 rename_id) in H1; auto.
          - intros; unfold Basics.compose.
            destruct x; auto. simpl. destruct x; auto.
      }

      (* Q is well-typed *)
      inversion H5; subst.
      (* show that Γ3 = dual A .: Γ3' *)
      inversion H3; subst. inversion H6; subst.
      + assert ((dual A .: (A0 .: Γ5)) ⊢ Q :#) as H_Q.
        {
          apply swap01_preserves_typing in H7.
          rewrite ((proj1 renamings_compose) Q swap01 swap01 id) in H7.
          - rewrite (proj1 rename_id) in H7; auto.
          - intros; unfold Basics.compose.
            destruct x; auto. simpl. destruct x; auto.
        }

        assert ((None :: (dual A0 .: Γ6)) ⊢ up R :#) as H_upR.
        {
          apply swap01_preserves_typing in H8.
          rewrite ((proj1 renamings_compose) (up R) swap01 swap01 id) in H8.
          - rewrite (proj1 rename_id) in H8; auto.
          - intros; unfold Basics.compose.
            destruct x; auto. simpl. destruct x; auto.
        }
        assert ((dual A0 .: Γ6) ⊢ R :#) as H_R.
        {
          eapply ((proj1 up_shift_sound) R nil _) in H_upR; auto.
        }

        (* new context split Γ = (Γ1 ∘ Γ5) ∘ Γ6 *)
        assert (exists Γ1', Γ1' ≜ Γ1 ∘ Γ5 /\ Γ ≜ Γ1' ∘ Γ6) as H_new_split.
        {
          clear - H2 H11.
          apply ctx_comm in H2.
          apply ctx_comm in H11.
          destruct (ctx_assoc _ _ _ _ _ H2 H11) as [Γ' [? ?]].
          exists Γ'; split.
          - apply ctx_comm in H. assumption.
          - apply ctx_comm in H0. assumption.
        }
        destruct H_new_split as [Γ1' [? ?]].

        econstructor.
        - apply H1.
        - econstructor.
          * assert ( A0 .: Γ1' ≜ None :: Γ1 ∘ (A0 .: Γ5)).
            { econstructor; auto. econstructor. }
            apply H9.
          * eapply H_P.
          * assumption.
        - eapply H_R.
      + exfalso.
        destruct a.
        apply H1.
        eapply (proj1 formula_property); eauto.
        reflexivity.
    }
  (* Commutativity *)
  + split; apply H.
  (* Transitivity *)
  + apply iff_trans with (Γ ⊢ Q :#); auto.
Qed.
