From FD Require Import Syntax.
From FD Require Import Types.
From FD Require Import Typing.
From FD Require Import Contexts.
From FD Require Import Renaming.
From FD Require Import FreeVars.

Import List.ListNotations.
Open Scope list_scope.

From Stdlib Require Import Lia.

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
  | c_link : forall ml mr,
              (link ml mr) ≡ (link mr ml)
  | c_cut_comm : forall P Q,
                  (cut P Q) ≡ (cut Q P)
  | c_cut_assoc : forall P Q R P' Q' R',
                    ~ (1 ∈ P) -> (* this premise guarantee that the typing judgements have the proper form *)
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
  + split; intros; inversion H; subst; apply ctx_comm in H2;
    econstructor; eauto;
    rewrite dual_involutive; eauto.
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
          + contradiction.
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
          eapply (proj1 nfv_renaming); auto. apply swap01_is_bijective.
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
        assert (~ 1 ∈ rename_process (up R) swap01).
        {
          replace 1 with (swap01 0) by auto.
          apply nfv_under_renaming. apply swap01_is_bijective.
          apply nfv_lift_n. lia.
        }
        assert (1 ∈ rename_process (up R) swap01).
        {
          eapply ((proj1 formula_property) _ _ 1 _ H8).
          reflexivity.
        }
        congruence.
    }
  (* Commutativity *)
  + split; apply H.
  (* Transitivity *)
  + apply iff_trans with (Γ ⊢ Q :#); auto.
Qed.

(******************************************************************************)
(* Structural Congruence (Depth Indexed)                                      *)
(******************************************************************************)
Inductive struct_cong_d : nat -> process -> process -> Prop :=
  (* axioms for equivalence of processes *)
  | c_link_d : forall ml mr,
              struct_cong_d 0 (link ml mr) (link mr ml)
  | c_cut_comm_d : forall P Q,
                  struct_cong_d 0 (cut P Q) (cut Q P)
  | c_cut_assoc_d : forall P Q R P' Q' R',
                    ~ (1 ∈ P) ->
                    P' = down (rename_process P swap01) ->
                    Q' = rename_process Q swap01 ->
                    R' = rename_process (up R) swap01 ->
                    struct_cong_d 0 (cut (cut P Q) R) (cut P' (cut Q' R'))

  (* rules to make the relation an equivalence *)
  | c_refl_d : forall P, struct_cong_d 0 P P
  | c_comm_d : forall n P Q, struct_cong_d n P Q -> struct_cong_d (S n) Q P
  | c_trans_d : forall n1 n2 P Q R,
                struct_cong_d n1 P Q ->
                struct_cong_d n2 Q R ->
                struct_cong_d (S (Nat.max n1 n2)) P R

  (* rules to make the relation a congruence *)
  | c_cong_link_d : forall n1 m1 m1' n2 m2 m2',
                      struct_congM_d n1 m1 m1' ->
                                          struct_congM_d n2 m2 m2' ->
                                                              struct_cong_d (S (Nat.max n1 n2)) (link m1 m2) (link m1' m2')
                                                                | c_cong_cut_d : forall n1 P P' n2 Q Q',
                                                                                  struct_cong_d n1 P P' ->
                                                                                                    struct_cong_d n2 Q Q' ->
                                                                                                                      struct_cong_d (S (Nat.max n1 n2)) (cut P Q) (cut P' Q')
  | c_cong_seq_d : forall n1 P P' n2 s s',
                  struct_cong_d n1 P P' ->
                  struct_congS_d n2 s s' ->
                  struct_cong_d (S (Nat.max n1 n2)) (seq P s) (seq P' s')

with struct_congM_d : nat -> message -> message -> Prop :=
  | c_cong_fut_d : forall n, struct_congM_d 0 (future n) (future n)
  | c_cong_prefix_d : forall n s s', struct_congS_d n s s' -> struct_congM_d (S n) (prefix s) (prefix s')

with struct_congS_d : nat -> statement -> statement -> Prop :=
  | c_cong_choose_l_d : forall n P P',
                        struct_cong_d n P P' ->
                        struct_congS_d (S n) (choose_left P) (choose_left P')
  | c_cong_choose_r_d : forall n P P',
                        struct_cong_d n P P' ->
                        struct_congS_d (S n) (choose_right P) (choose_right P')
  | c_cong_choice_d : forall n1 P P' n2 Q Q',
                      struct_cong_d n1 P P' ->
                      struct_cong_d n2 Q Q' ->
                      struct_congS_d (S (Nat.max n1 n2)) (offer_choice P Q) (offer_choice P' Q')
  | c_cong_send_d : forall n1 P P' n2 Q Q',
                    struct_cong_d n1 P P' ->
                    struct_cong_d n2 Q Q' ->
                    struct_congS_d (S (Nat.max n1 n2)) (send P Q) (send P' Q')
  | c_cong_receive_d : forall n P P', struct_cong_d n P P' -> struct_congS_d (S n) (receive P) (receive P')
  | c_cong_close_d : struct_congS_d 0 close close
  | c_cong_wait_d : forall n P P', struct_cong_d n P P' -> struct_congS_d (S n) (wait P) (wait P').

Scheme struct_congP_depth_ind := Induction for struct_cong_d Sort Prop
  with struct_congM_depth_ind := Induction for struct_congM_d Sort Prop
  with struct_congS_depth_ind := Induction for struct_congS_d Sort Prop.
Combined Scheme struct_cong_depth_ind from struct_congP_depth_ind, struct_congM_depth_ind, struct_congS_depth_ind.

Lemma struct_cong_d_from_struct_cong :
  (forall P P', P ≡ P' -> exists k, struct_cong_d k P P') /\
  (forall M M', M !≡ M' -> exists k, struct_congM_d k M M') /\
  (forall s s', s $≡ s' -> exists k, struct_congS_d k s s').
Proof.
  apply struct_cong_ind; intros;
    try (now (exists 0; econstructor; eauto));
    try (now (destruct H; exists (S x); econstructor; eauto)).
  + destruct H; destruct H0. exists (S (Nat.max x x0)).
    eapply c_trans_d; eauto.
  + destruct H; destruct H0. exists (S (Nat.max x x0)).
    eapply c_cong_link_d; eauto.
  + destruct H; destruct H0. exists (S (Nat.max x x0)).
    eapply c_cong_cut_d; eauto.
  + destruct H; destruct H0. exists (S (Nat.max x x0)).
    eapply c_cong_seq_d; eauto.
  + destruct H; destruct H0. exists (S (Nat.max x x0)).
    eapply c_cong_choice_d; eauto.
  + destruct H; destruct H0. exists (S (Nat.max x x0)).
    eapply c_cong_send_d; eauto.
Qed.

Lemma struct_cong_from_struct_cong_d :
  (forall k P P', struct_cong_d k P P'  -> P ≡ P') /\
  (forall k M M', struct_congM_d k M M' -> M !≡ M') /\
  (forall k s s', struct_congS_d k s s' -> s $≡ s').
Proof.
  apply struct_cong_depth_ind; intros; try econstructor; eauto.
  + apply c_comm in H0. apply c_comm in H. eapply c_trans; eauto.
  + apply c_comm. apply c_cong_link; auto.
  + apply c_comm. apply c_cong_cut; auto.
  + apply c_comm. apply c_cong_seq; auto.
Qed.

(* reflexivitiy is derivable for messages and statements *)
Lemma struct_cong_d_refl :
  (forall P, exists k, struct_cong_d k P P) /\
  (forall M, exists k, struct_congM_d k M M) /\
  (forall s, exists k, struct_congS_d k s s).
Proof.
  apply syntax_ind; intros;
  try destruct H; try destruct H0; eexists; econstructor; eauto.
Qed.

Lemma struct_cong_reflM :
  forall M, M !≡ M.
Proof.
  intros. destruct ((proj1 (proj2 struct_cong_d_refl)) M).
  eapply (proj1 (proj2 struct_cong_from_struct_cong_d)); eauto.
Qed.

Lemma struct_cong_reflS :
  forall s, s $≡ s.
Proof.
  intros. destruct ((proj2 (proj2 struct_cong_d_refl)) s).
  eapply (proj2 (proj2 struct_cong_from_struct_cong_d)); eauto.
Qed.

(* transitivity is derivable for messages and statements *)
Lemma struct_cong_d_trans :
  forall n1 n2,
    forall k1 k2,
      k1 <= n1 -> k2 <= n2 ->
        (forall M1 M M2,
          struct_congM_d k1 M1 M -> struct_congM_d k2 M M2 ->
            exists k, struct_congM_d k M1 M2) /\
        (forall s1 s s2,
          struct_congS_d k1 s1 s -> struct_congS_d k2 s s2 ->
            exists k, struct_congS_d k s1 s2).
Proof.
  induction n1; induction n2; intros.
  + assert (k1 = 0) by lia; assert (k2 = 0) by lia; subst.
    split; intros.
    - inversion H0; subst. inversion H1; subst. eexists; eauto.
    - inversion H0; subst. inversion H1; subst. eexists; eauto.
  + assert (k1 = 0) by lia; subst. split; intros.
    - inversion H1; subst; eauto.
    - inversion H1; subst; eauto.
  + assert (k2 = 0) by lia; subst. split; intros.
    - inversion H2; subst; eauto.
    - inversion H2; subst; eauto.
  + split; intros.
    - inversion H1; subst; inversion H2; subst; eauto.
      assert (n <= n1) by lia; assert (n0 <= n2) by lia.
      destruct ((proj2 (IHn1 _ _ _ H4 H5)) s s' s'0 H3 H6).
      eexists. econstructor; eauto.
    - inversion H1; subst; inversion H2; subst; eauto;
      eexists; econstructor; eapply c_trans_d; eauto.
Qed.

Lemma struct_congM_d_trans :
  forall M1 M M2 n1 n2,
    struct_congM_d n1 M1 M -> struct_congM_d n2 M M2 ->
    exists k, struct_congM_d k M1 M2.
Proof.
  intros.
  apply ((proj1 (struct_cong_d_trans n1 n2 n1 n2 (PeanoNat.Nat.le_refl n1) (PeanoNat.Nat.le_refl n2))) M1 M M2);
  auto.
Qed.

(* Symmetry is derivable for messages and statements *)
Lemma struct_cong_d_symm :
  forall n,
    forall k,
      k <= n ->
        (forall M1 M2,
          struct_congM_d k M1 M2 -> exists k', struct_congM_d k' M2 M1) /\
        (forall s1 s2,
          struct_congS_d k s1 s2 -> exists k', struct_congS_d k' s2 s1).
Proof.
  induction n; intros.
  + assert (k = 0) by lia; subst; repeat split; intros; inversion H0; subst; eexists; eauto.
  + split; intros; inversion H0; subst;
    try (eexists; econstructor; eapply c_comm_d; eassumption).
    assert (n0 <= n) by lia. destruct ((proj2 (IHn _ H2)) _ _ H1).
    eexists. econstructor; eauto.
Qed.

Lemma struct_congM_d_symm :
  forall M1 M2 n,
    struct_congM_d n M1 M2 -> exists k, struct_congM_d k M2 M1.
Proof. intros. apply (proj1 (struct_cong_d_symm n n (PeanoNat.Nat.le_refl n))); auto. Qed.

(* A future is only congruent to itself *)
Lemma future_equiv_future :
  forall i n M,
    (struct_congM_d n (future i) M) \/ (struct_congM_d n M (future i))
      -> M = future i.
Proof. intros. destruct H; inversion H; auto. Qed.

Corollary future_equiv_future1 :
  forall M n, (future n) !≡ M -> M = future n.
Proof.
  intros.
  apply struct_cong_d_from_struct_cong in H. destruct H.
  pose proof (future_equiv_future _ _ _ (or_introl H)). auto.
Qed.

(******************************************************************************)
(* Inversions on Congruence                                                   *)
(******************************************************************************)
Lemma stop_equiv_stop_d :
  forall P n, (forall k, k <= n -> struct_cong_d k stop P \/ struct_cong_d k P stop -> P = stop).
Proof.
  intros.
  generalize dependent k.
  generalize dependent P.
  induction n; intros.
  + inversion H; subst. destruct H0; inversion H0; auto.
  + destruct H0.
    - inversion H0; subst; auto.
      * assert (n0 <= n) by lia.
        apply (IHn _ _ H2).
        right; auto.
      * assert (Q = stop).
        {
          assert (n1 <= n) by lia.
          apply (IHn _ _ H3).
          left; auto.
        }
        subst.
        assert (n2 <= n) by lia.
        apply (IHn _ _ H3).
        left; auto.
    - inversion H0; subst; auto.
      * assert (n0 <= n) by lia.
        apply (IHn _ _ H2).
        left; auto.
      * assert (Q = stop).
        {
          assert (n2 <= n) by lia.
          apply (IHn _ _ H3).
          right; auto.
        }
        subst.
        assert (n1 <= n) by lia.
        apply (IHn _ _ H3).
        right; auto.
Qed.

Lemma stop_equiv_stop : forall P, stop ≡ P -> P = stop.
Proof.
  intros. apply struct_cong_d_from_struct_cong in H.
  destruct H.
  apply (stop_equiv_stop_d P x x (PeanoNat.Nat.le_refl x)); left; auto.
Qed.

Lemma link_future_equiv_link_future_d :
  forall n,
    forall k i M P,
    k <= n ->
    struct_cong_d k (link (future i) M) P \/ struct_cong_d k P (link (future i) M) \/
    struct_cong_d k (link M (future i)) P \/ struct_cong_d k P (link M (future i)) ->
    exists M' n', struct_congM_d n' M' M /\ (P = (link (future i) M') \/ P = (link M' (future i))).
Proof.
  induction n; intros.
  + assert (k = 0) by lia; subst. destruct H0 as [|[|[|]]];
    inversion H0; subst; destruct ((proj1 (proj2 struct_cong_d_refl)) M);
    eexists; eexists; split; eauto.
  + destruct H0 as [|[|[|]]]; inversion H0; subst;
    try (now (destruct ((proj1 (proj2 struct_cong_d_refl)) M); eexists; eexists; split; eauto)).
    - assert (n0 <= n) by lia. apply (IHn n0 i M P H2); eauto.
    - assert (n1 <= n) by lia.
      destruct (IHn _ _ _ _ H3 (or_introl H1)) as [M' [n' [? [|]]]]; subst.
      * assert (n2 <= n) by lia.
        destruct (IHn _ _ _ _ H5 (or_introl H2)) as [M'' [n'' [? [|]]]]; subst.
        ** destruct (struct_congM_d_trans _ _ _ _ _ H6 H4); eauto.
        ** destruct (struct_congM_d_trans _ _ _ _ _ H6 H4); eauto.
      * assert (n2 <= n) by lia.
        assert (struct_cong_d n2 (link (future i) M') P \/ struct_cong_d n2 P (link (future i) M') \/ struct_cong_d n2 (link M' (future i)) P \/ struct_cong_d n2 P (link M' (future i))) by eauto.
        destruct (IHn n2 i M' P H5 H6) as [M'' [n'' [? [|]]]]; subst.
        ** destruct (struct_congM_d_trans _ _ _ _ _ H7 H4); eauto.
        ** destruct (struct_congM_d_trans _ _ _ _ _ H7 H4); eauto.
    - rewrite (future_equiv_future _ _ _ (or_introl H4)).
      destruct (struct_congM_d_symm _ _ _ H6).
      eexists; eexists; split; eauto.
    - assert (n0 <= n) by lia. apply (IHn n0 i M P H2 (or_introl H1)).
    - assert (n2 <= n) by lia.
      assert (struct_cong_d n2 (link (future i) M) Q \/ struct_cong_d n2 Q (link (future i) M) \/ struct_cong_d n2 (link M (future i)) Q \/ struct_cong_d n2 Q (link M (future i))) by eauto.
      destruct (IHn _ _ _ _ H3 H4) as [M' [n' [? [|]]]]; subst.
      * assert (n1 <= n) by lia.
        assert (struct_cong_d n1 (link (future i) M') P \/ struct_cong_d n1 P (link (future i) M') \/ struct_cong_d n1 (link M' (future i)) P \/ struct_cong_d n1 P (link M' (future i))) by eauto.
        destruct (IHn _ _ _ _ H6 H7) as [M'' [n'' [? [|]]]]; subst.
        ** destruct (struct_congM_d_trans _ _ _ _ _ H8 H5); eauto.
        ** destruct (struct_congM_d_trans _ _ _ _ _ H8 H5); eauto.
      * assert (n1 <= n) by lia.
        assert (struct_cong_d n1 (link (future i) M') P \/ struct_cong_d n1 P (link (future i) M') \/ struct_cong_d n1 (link M' (future i)) P \/ struct_cong_d n1 P (link M' (future i))) by eauto.
        destruct (IHn _ _ _ _ H6 H7) as [M'' [n'' [? [|]]]]; subst.
        ** destruct (struct_congM_d_trans _ _ _ _ _ H8 H5); eauto.
        ** destruct (struct_congM_d_trans _ _ _ _ _ H8 H5); eauto.
    - rewrite (future_equiv_future _ _ _ (or_intror H5)).
      eexists; eexists; split; eauto.
    - assert (n0 <= n) by lia.
      assert (struct_cong_d n0 (link (future i) M) P \/ struct_cong_d n0 P (link (future i) M) \/ struct_cong_d n0 (link M (future i)) P \/ struct_cong_d n0 P (link M (future i))) by eauto.
      apply (IHn n0 i M P H2 H3).
    - assert (n1 <= n) by lia.
      assert (struct_cong_d n1 (link (future i) M) Q \/ struct_cong_d n1 Q (link (future i) M) \/ struct_cong_d n1 (link M (future i)) Q \/ struct_cong_d n1 Q (link M (future i))) by eauto.
      destruct (IHn _ _ _ _ H3 H4) as [M' [n' [? [|]]]]; subst.
      * assert (n2 <= n) by lia.
        assert (struct_cong_d n2 (link (future i) M') P \/ struct_cong_d n2 P (link (future i) M') \/ struct_cong_d n2 (link M' (future i)) P \/ struct_cong_d n2 P (link M' (future i))) by eauto.
        destruct (IHn _ _ _ _ H6 H7) as [M'' [n'' [? [|]]]]; subst.
        ** destruct (struct_congM_d_trans _ _ _ _ _ H8 H5); eauto.
        ** destruct (struct_congM_d_trans _ _ _ _ _ H8 H5); eauto.
      * assert (n2 <= n) by lia.
        assert (struct_cong_d n2 (link (future i) M') P \/ struct_cong_d n2 P (link (future i) M') \/ struct_cong_d n2 (link M' (future i)) P \/ struct_cong_d n2 P (link M' (future i))) by eauto.
        destruct (IHn _ _ _ _ H6 H7) as [M'' [n'' [? [|]]]]; subst.
        ** destruct (struct_congM_d_trans _ _ _ _ _ H8 H5); eauto.
        ** destruct (struct_congM_d_trans _ _ _ _ _ H8 H5); eauto.
    - rewrite (future_equiv_future _ _ _ (or_introl H6)).
      destruct (struct_congM_d_symm _ _ _ H4);
      eexists; eexists; split; eauto.
    - assert (n0 <= n) by lia.
      assert (struct_cong_d n0 (link (future i) M) P \/ struct_cong_d n0 P (link (future i) M) \/ struct_cong_d n0 (link M (future i)) P \/ struct_cong_d n0 P (link M (future i))) by eauto.
      apply (IHn n0 i M P H2 H3).
    - assert (n2 <= n) by lia.
      assert (struct_cong_d n2 (link (future i) M) Q \/ struct_cong_d n2 Q (link (future i) M) \/ struct_cong_d n2 (link M (future i)) Q \/ struct_cong_d n2 Q (link M (future i))) by eauto.
      destruct (IHn _ _ _ _ H3 H4) as [M' [n' [? [|]]]]; subst.
      * assert (n1 <= n) by lia.
        assert (struct_cong_d n1 (link (future i) M') P \/ struct_cong_d n1 P (link (future i) M') \/ struct_cong_d n1 (link M' (future i)) P \/ struct_cong_d n1 P (link M' (future i))) by eauto.
        destruct (IHn _ _ _ _ H6 H7) as [M'' [n'' [? [|]]]]; subst.
        ** destruct (struct_congM_d_trans _ _ _ _ _ H8 H5); eauto.
        ** destruct (struct_congM_d_trans _ _ _ _ _ H8 H5); eauto.
      * assert (n1 <= n) by lia.
        assert (struct_cong_d n1 (link (future i) M') P \/ struct_cong_d n1 P (link (future i) M') \/ struct_cong_d n1 (link M' (future i)) P \/ struct_cong_d n1 P (link M' (future i))) by eauto.
        destruct (IHn _ _ _ _ H6 H7) as [M'' [n'' [? [|]]]]; subst.
        ** destruct (struct_congM_d_trans _ _ _ _ _ H8 H5); eauto.
        ** destruct (struct_congM_d_trans _ _ _ _ _ H8 H5); eauto.
    - rewrite (future_equiv_future _ _ _ (or_intror H6)).
      eexists; eexists; split; eauto.
Qed.

Lemma link_future_equiv_link_future :
  forall i M P,
    (link (future i) M) ≡ P \/ P ≡ (link (future i) M) ->
    exists M' n', struct_congM_d n' M' M /\ (P = (link (future i) M') \/ P = (link M' (future i))).
Proof.
  intros. destruct H.
  + apply (proj1 struct_cong_d_from_struct_cong) in H. destruct H.
    apply (link_future_equiv_link_future_d x _ _ _ _ (PeanoNat.Nat.le_refl x) (or_introl H)).
  + apply (proj1 struct_cong_d_from_struct_cong) in H. destruct H.
    assert (struct_cong_d x (link (future i) M) P \/ struct_cong_d x P (link (future i) M) \/ struct_cong_d x (link M (future i)) P \/ struct_cong_d x P (link M (future i))) by eauto.
    apply (link_future_equiv_link_future_d x _ _ _ _ (PeanoNat.Nat.le_refl x) H0).
Qed.

(* Free variables are preserved under structural congruence *)
Lemma free_vars_under_struct_cong :
  (forall P Q, P ≡ Q -> forall k, (k ∈ P) <-> (k ∈ Q)) /\
  (forall M1 M2, M1 !≡ M2 -> forall k, (occurs_free_message k M1) <-> (occurs_free_message k M2)) /\
  (forall s1 s2, s1 $≡ s2 -> forall k, (occurs_free_statement k s1) <-> (occurs_free_statement k s2)).
Proof.
  apply struct_cong_ind; intros.
  + split; intros; inversion H; subst; free_var_econstructor; auto.
  + split; intros; inversion H; subst; free_var_econstructor; auto.
  + split; intros.
    - inversion H; subst.
      * inversion H2; subst.
        {
          apply fv_cut_l.
          destruct ((proj1 free_vars_decidable) (down (rename_process P swap01)) (S k)); auto.
          apply (proj1 n_fv_down_Sn2); try lia.
          apply ((proj1 fv_under_renaming) _ swap01). apply swap01_is_bijective.
          simpl. rewrite swap_swap_id; auto.
        }
        {
          apply fv_cut_r. apply fv_cut_l.
          apply ((proj1 fv_under_renaming) _ swap01). apply swap01_is_bijective.
          simpl. rewrite swap_swap_id; auto.
        }
      * apply fv_cut_r. apply fv_cut_r.
        apply ((proj1 fv_under_renaming) _ swap01). apply swap01_is_bijective.
        simpl. rewrite swap_swap_id; auto.
        apply (proj1 fv_up_Sn); try lia. auto.
    - inversion H; subst.
      * apply fv_cut_l. apply fv_cut_l.
        unfold down in H2.
        apply ((proj1 n_fv_down_Sn) _ (S k) 0) in H2; try lia.
        apply ((proj1 fv_under_renaming) _ swap01) in H2.
        rewrite swap_swap_id in H2. simpl in H2; auto.
        apply swap01_is_bijective.
      * inversion H2; subst.
        {
          apply fv_cut_l. apply fv_cut_r. apply ((proj1 fv_under_renaming) _ swap01) in H3.
          simpl in H3. rewrite swap_swap_id in H3; auto. apply swap01_is_bijective.
        }
        {
          apply fv_cut_r. apply ((proj1 fv_under_renaming) _ swap01) in H3; try apply swap01_is_bijective.
          simpl in H3. rewrite swap_swap_id in H3.
          apply ((proj1 fv_up_Sn2) _ _ 0); try lia.
          unfold up in H3. assumption.
        }
  + split; auto.
  + split; intros; apply H; auto.
  + split; intros.
    - apply H0. apply H. assumption.
    - apply H. apply H0. assumption.
  + split; intros; inversion H1; subst;
    try apply H in H4; try apply H0 in H4; free_var_econstructor; auto.
  + split; intros; inversion H1; subst;
    try apply H in H4; try apply H0 in H4; free_var_econstructor; auto.
  + split; intros; inversion H1; subst;
    try apply H in H4; try apply H0 in H4; free_var_econstructor; auto.
  + split; intros; inversion H; free_var_econstructor.
  + split; intros; inversion H0; subst; apply H in H3; free_var_econstructor; auto.
  + split; intros; inversion H0; subst; apply H in H3; free_var_econstructor; auto.
  + split; intros; inversion H0; subst; apply H in H3; free_var_econstructor; auto.
  + split; intros; inversion H1; subst;
    try apply H in H4; try apply H0 in H4; free_var_econstructor; auto.
  + split; intros; inversion H1; subst;
    try apply H in H4; try apply H0 in H4; free_var_econstructor; auto.
  + split; intros; inversion H0; subst; apply H in H3; free_var_econstructor; auto.
  + split; intros; inversion H.
  + split; intros; inversion H0; subst; apply H in H3; free_var_econstructor; auto.
Qed.

Corollary nfv_under_struct_cong :
  forall P Q n, P ≡ Q -> ~ n ∈ P -> ~ n ∈ Q.
Proof.
  intros. intro Hfv.
  pose proof ((proj1 free_vars_under_struct_cong) _ _ H n).
  apply H0. apply H1. auto.
Qed.

Corollary nfv_under_struct_congM :
  forall M N n, M !≡ N -> ~ (occurs_free_message n M) -> ~ (occurs_free_message n N).
Proof.
  intros. intro Hfv.
  pose proof ((proj1 (proj2 free_vars_under_struct_cong)) _ _ H n).
  apply H0. apply H1. auto.
Qed.
