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

(* Inductive directed_congruence : process -> process -> Prop :=
  (* links *)
  | dc_cong_link : forall ml1 ml2 mr1 mr2,
      ml1 !⇛ ml2 -> mr1 !⇛ mr2 -> (link ml1 mr1) ⇛ (link ml2 mr2)
  | dc_link : forall ml1 ml2 mr1 mr2,
      ml1 !⇛ ml2 -> mr1 !⇛ mr2 -> (link ml1 mr1) ⇛ (link mr2 ml2)

  (* cuts *)
  | dc_cut_comm : forall P P' Q Q', 
      P ⇛ P' -> Q ⇛ Q' -> (cut P Q) ⇛ (cut Q' P')
  | dc_cut_assoc_l : forall P (* P' *) P'' Q Q' R R' L L',
      L ⇛ (cut P Q) (* (cut P Q) *) (* -> ~ (1 ∈ P) -> P' ⇛ P *) (* P ⇛ P' *) ->
      P'' = down (rename_process P swap01) (* down (rename_process P' swap01) *) ->
      Q' = rename_process Q swap01 ->
      R' = rename_process (up R) swap01 ->
      (cut Q' R') ⇛ L' ->
      (cut L R) ⇛ (cut P'' L')
  | dc_cut_assoc_l_comm : forall P P' P'' Q Q' R R' L L',
      L ⇛ (cut P Q) -> ~ (1 ∈ P) -> P ⇛ P' ->
      P'' = down (rename_process P' swap01) ->
      Q' = rename_process Q swap01 ->
      R' = rename_process (up R) swap01 ->
      (cut Q' R') ⇛ L' ->
      (cut L R) ⇛ (cut L' P'')
  (* these rules are necessary to ensure admissibility of symmetry *)
  | dc_cut_assoc_r : forall P P' Q Q' R R' R'' L L',
      L ⇛ (cut Q R) -> ~ (1 ∈ R) -> R ⇛ R' ->
      P' = rename_process (up P) swap01 ->
      Q' = rename_process Q swap01 ->
      R'' = down (rename_process R' swap01) ->
      (cut P' Q') ⇛ L' ->
      (cut P L) ⇛ (cut L' R'')
  | dc_cut_assoc_r_comm : forall P P' Q Q' R R' R'' L L',
      L ⇛ (cut Q R) -> ~ (1 ∈ R) -> R ⇛ R' ->
      P' = rename_process (up P) swap01 ->
      Q' = rename_process Q swap01 ->
      R'' = down (rename_process R' swap01) ->
      (cut P' Q') ⇛ L' ->
      (cut P L) ⇛ (cut R'' L')
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
  "s '$⇛' r" := (directed_congruence_statement s r). *)

Inductive directed_congruence : process -> process -> Prop :=
  (* links *)
  | dc_cong_link : forall ml1 ml2 mr1 mr2,
      ml1 !⇛ ml2 -> mr1 !⇛ mr2 -> (link ml1 mr1) ⇛ (link ml2 mr2)
  | dc_link : forall ml1 ml2 mr1 mr2,
      ml1 !⇛ ml2 -> mr1 !⇛ mr2 -> (link ml1 mr1) ⇛ (link mr2 ml2)

  (* cuts *)
  | dc_cut_comm : forall P P' Q Q', 
      P ⇛ P' -> Q ⇛ Q' -> (cut P Q) ⇛ (cut Q' P')
  | dc_cut_assoc_l1 : forall P P' P'' Q Q' R R' R'' L L',
      (* i don't like the L ⇛ (cut P Q) premise, can we cut it? *)
      L ⇛ (cut P Q) -> ~ (1 ∈ P) -> P ⇛ P' -> R ⇛ R' ->
      P'' = down (rename_process P' swap01) ->
      Q' = rename_process Q swap01 ->
      R'' = rename_process (up R') swap01 ->
      (cut Q' R'') ⇛ L' ->
      (cut L R) ⇛ (cut P'' L')
  | dc_cut_assoc_l2 : forall P P' P'' Q Q' R R' R'' L L',
      L ⇛ (cut Q P) -> ~ (1 ∈ P) -> P ⇛ P' -> R ⇛ R' ->
      P'' = down (rename_process P' swap01) ->
      Q' = rename_process Q swap01 ->
      R'' = rename_process (up R') swap01 ->
      (cut R'' Q') ⇛ L' ->
      (cut L R) ⇛ (cut P'' L')
  | dc_cut_assoc_l1_comm : forall P P' P'' Q Q' R R' R'' L L',
      L ⇛ (cut P Q) -> ~ (1 ∈ P) -> P ⇛ P' -> R ⇛ R' ->
      P'' = down (rename_process P' swap01) ->
      Q' = rename_process Q swap01 ->
      R'' = rename_process (up R') swap01 ->
      (cut Q' R'') ⇛ L' ->
      (cut L R) ⇛ (cut L' P'')
  | dc_cut_assoc_l2_comm : forall P P' P'' Q Q' R R' R'' L L',
      L ⇛ (cut Q P) -> ~ (1 ∈ P) -> P ⇛ P' -> R ⇛ R' ->
      P'' = down (rename_process P' swap01) ->
      Q' = rename_process Q swap01 ->
      R'' = rename_process (up R') swap01 ->
      (cut R'' Q') ⇛ L' ->
      (cut L R) ⇛ (cut L' P'')
  (* these rules are necessary to ensure admissibility of symmetry *)
  | dc_cut_assoc_r1 : forall P P' P'' Q Q' R R' R'' L L',
      L ⇛ (cut Q R) -> ~ (1 ∈ R) -> P ⇛ P' -> R ⇛ R' ->
      P'' = rename_process (up P') swap01 ->
      Q' = rename_process Q swap01 ->
      R'' = down (rename_process R' swap01) ->
      (cut P'' Q') ⇛ L' ->
      (cut P L) ⇛ (cut L' R'')
  | dc_cut_assoc_r2 : forall P P' P'' Q Q' R R' R'' L L',
      L ⇛ (cut R Q) -> ~ (1 ∈ R) -> P ⇛ P' -> R ⇛ R' ->
      P'' = rename_process (up P') swap01 ->
      Q' = rename_process Q swap01 ->
      R'' = down (rename_process R' swap01) ->
      (cut Q' P'') ⇛ L' ->
      (cut P L) ⇛ (cut L' R'')
  | dc_cut_assoc_r1_comm : forall P P' P'' Q Q' R R' R'' L L',
      L ⇛ (cut Q R) -> ~ (1 ∈ R) -> P ⇛ P' -> R ⇛ R' ->
      P'' = rename_process (up P') swap01 ->
      Q' = rename_process Q swap01 ->
      R'' = down (rename_process R' swap01) ->
      (cut P'' Q') ⇛ L' ->
      (cut P L) ⇛ (cut R'' L')
  | dc_cut_assoc_r2_comm : forall P P' P'' Q Q' R R' R'' L L',
      L ⇛ (cut R Q) -> ~ (1 ∈ R) -> P ⇛ P' -> R ⇛ R' ->
      P'' = rename_process (up P') swap01 ->
      Q' = rename_process Q swap01 ->
      R'' = down (rename_process R' swap01) ->
      (cut Q' P'') ⇛ L' ->
      (cut P L) ⇛ (cut R'' L')
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

(* test *)
Lemma directed_cong_triangle :
  (forall P1 P2, P1 ⇛ P2 -> forall P3, P1 ⇛ P3 -> P2 ⇛ P3) /\
  (forall M1 M2, M1 !⇛ M2 -> forall M3, M1 !⇛ M3 -> M2 !⇛ M3) /\
  (forall s1 s2, s1 $⇛ s2 -> forall s3, s1 $⇛ s3 -> s2 $⇛ s3).
Proof.
  apply directed_cong_ind; intros.
  + inversion H1; subst.
    - apply dc_cong_link; try apply H; try apply H0; auto.
    - apply dc_link; try apply H; try apply H0; auto.
  + inversion H1; subst.
    - apply dc_link; try apply H; try apply H0; auto.
    - apply dc_cong_link; try apply H; try apply H0; auto.
  + admit.
  + inversion H3; subst.
    - assert ( L' ⇛ (cut (rename_process Q swap01) (rename_process (up R) swap01)))
        by admit.
      eapply dc_cut_assoc_r1_comm.
      * apply H4.
      * admit.
      * assert (
          (down (rename_process P' swap01)) ⇛ (down (rename_process P swap01))
        ) by admit.
        apply H5.
      * assert (
          (rename_process (up R) swap01) ⇛ (rename_process (up Q'0) swap01)
        ) by admit.
        apply H5.
      * autorewrite with up_down_rename_rewrites; auto.
        admit.
      * autorewrite with up_down_rename_rewrites. auto.
      * autorewrite with up_down_rename_rewrites. auto.
      * apply (H _ H6).
    - admit.
    - admit.
    - 
Admitted.
(* test end *)

(******************************************************************************)
(* Directed congruence is invariant under substitution                        *)
(******************************************************************************)
(* Lemma directed_cong_substitution :
  (forall P Q, P ⇛ Q -> forall σ1 σ2, (forall i, (σ1 i) !⇛ (σ2 i))
    -> (subst_process P σ1) ⇛ (subst_process Q σ2)) /\
  (forall M N, M !⇛ N -> forall σ1 σ2, (forall i, (σ1 i) !⇛ (σ2 i))
    -> (subst_message M σ1) !⇛ (subst_message N σ2)) /\
  (forall s t, s $⇛ t -> forall σ1 σ2, (forall i, (σ1 i) !⇛ (σ2 i))
    -> (subst_statement s σ1) $⇛ (subst_statement t σ2)).
Proof.
  apply directed_cong_ind; intros; simpl.
  + admit.
  + econstructor; try apply H; try apply H0; auto.
  + admit.
  + (* up_subst twice results in up in every σ1 i -> ~ 1 ∈ P ...
       since (up_subst (up_subst σ1)) is id up to index 2, at swap01 is
       id starting at 2 we can swap rename and subst
       what remains:
        down (subst P (up_subst (up_subst σ1)))
        =  subst (down P) (up_subst σ1)
        I think the IH is the same as in down_ren_up_ren_commute!?

        We need similar lemmas as below, just with substitution
       *)
    admit.
  + admit.
  + admit.
  + admit.
  + admit.
Admitted. *)

(* Notes: For ⇛ to be invariant under substitution, we require
   the congruences from ≡. In this case, reflexivity is derivable so we can drop it.

   Also, the additional premises in the what used to be axiom in ≡ seem
   redundant now. But idk, we migt still need them later.

   The diamond property immemdiately follows from symmetry but is too weak
   for parallel reduction: What we need is the following property (pictorally):

        Q                          Q
     ⇛    ⇛       then         ⇛   ⇛
    Q1     Q2                  Q1  ⇛  Q2

   With symmetry, this means that we can always convert between diverging
   congruences in a single step (but now we need additional premises in the axioms).
   We also need more cut_assoc rules to deal with communication in order to
   reconciliate in triangle-shape. Note: This also increases the amount of
   rp_cut_assoc rules (since the link may now occurs in every position).

   Switch back confluence_directed_cong_par_red to
   forall P Q1 Q2, P ⇛ Q1 -> P ⊵ Q2 -> exists R, Q1 ⊵ R /\ Q2 ⇛ R.
*)

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
  (* apply directed_cong_ind; intros; try (now (econstructor; eauto)).
  + eapply c_trans. { eapply c_link. }
    eapply c_cong_link; eauto.
  + eapply c_trans. { eapply c_cut_comm. }
    eapply c_cong_cut; eauto.
  + eapply c_trans. { eapply c_cong_cut. apply H. apply c_refl. }
    eapply c_trans. { eapply c_cong_cut. eapply c_cong_cut. apply H0. apply c_refl. apply c_refl. }
    subst. eapply c_trans.
    - eapply c_cut_assoc; auto. intro Hfv.
      apply (proj2 ((proj1 free_vars_under_struct_cong) _ _ H0 _)) in Hfv.
      congruence.
    - eapply c_cong_cut. apply c_refl. auto.
      admit.
  + eapply c_trans. { eapply c_cong_cut. apply H. apply c_refl. }
    eapply c_trans. { eapply c_cong_cut. eapply c_cong_cut. apply H0. apply c_refl. apply c_refl. }
    subst. eapply c_trans.
    - eapply c_cut_assoc; auto. intro Hfv.
      apply (proj2 ((proj1 free_vars_under_struct_cong) _ _ H0 _)) in Hfv.
      congruence.
    - eapply c_trans. apply c_cut_comm. eapply c_cong_cut; try apply c_refl.
      auto.
      admit.
  + eapply c_trans. { eapply c_cong_cut. apply c_refl. apply H. }
    eapply c_trans. { eapply c_cong_cut. apply c_refl. apply c_cong_cut. apply c_refl. apply H0. }
    eapply c_comm. eapply c_trans. { eapply c_cong_cut. apply c_comm in H1. apply H1. apply c_refl. }
    eapply c_trans.
    - apply c_cut_assoc; auto.
      assert (~ (0 ∈ (up P))). { apply nfv_lift_n; lia. }
      replace 1 with (swap01 0) by auto. subst.
      apply ((proj1 nfv_under_renaming) _ swap01); auto. apply swap01_is_bijective.
    - subst. autorewrite with up_down_rename_rewrites.
      * apply c_cong_cut; apply c_refl.
      * replace 0 with (swap01 1) by auto.
        apply ((proj1 nfv_under_renaming) _ swap01). apply swap01_is_bijective.
        intro Hfv. apply (proj2 ((proj1 free_vars_under_struct_cong) _ _ H0 _)) in Hfv.
        congruence.
  + eapply c_trans. { eapply c_cong_cut. apply c_refl. apply H. }
    eapply c_trans. { eapply c_cong_cut. apply c_refl. apply c_cong_cut. apply c_refl. apply H0. }
    assert ((cut P (cut Q R')) ≡ (cut L' R'')).
    {
      eapply c_comm. eapply c_trans. { eapply c_cong_cut. apply c_comm in H1. apply H1. apply c_refl. }
      eapply c_trans.
      - apply c_cut_assoc; auto.
        assert (~ (0 ∈ (up P))). { apply nfv_lift_n; lia. }
        replace 1 with (swap01 0) by auto. subst.
        apply ((proj1 nfv_under_renaming) _ swap01); auto. apply swap01_is_bijective.
      - subst. autorewrite with up_down_rename_rewrites.
        * apply c_cong_cut; apply c_refl.
        * replace 0 with (swap01 1) by auto.
          apply ((proj1 nfv_under_renaming) _ swap01). apply swap01_is_bijective.
          intro Hfv. apply (proj2 ((proj1 free_vars_under_struct_cong) _ _ H0 _)) in Hfv.
          congruence.
    }
    eapply c_trans. apply H2. apply c_cut_comm.
  + destruct (proj1 (proj2 struct_cong_d_refl) m).
    eapply (proj1 (proj2 struct_cong_from_struct_cong_d)); eauto.
  + destruct (proj2 (proj2 struct_cong_d_refl) s).
    eapply (proj2 (proj2 struct_cong_from_struct_cong_d)); eauto. *)
Admitted.

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
  (* apply directed_cong_ind; intros; try (now (simpl; econstructor; eauto));
  try (now (simpl; econstructor; try apply H; try apply H0; auto;
       try apply shift_preserves_bijection;try apply shift_preserves_bijection;  auto)).
  + simpl. eapply dc_cut_assoc_l.
    - apply H. apply shift_preserves_bijection. auto.
    - fold rename_process.
      replace 1 with (up_ren (up_ren r) 1) by auto.
      apply ((proj1 nfv_under_renaming) _ (up_ren (up_ren r)) _) in n;
      try (repeat apply shift_preserves_bijection; auto).
    - fold rename_process. apply H0.
      repeat apply shift_preserves_bijection. auto.
    - rewrite e. unfold down.
      assert (
        rename_process (rename_process P' (up_ren (up_ren r))) swap01 =
        rename_process (rename_process P' swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H3.
      assert (~ 1 ∈ P').
      {
        intro Hfv. apply directed_cong_in_struct_cong in d0. apply c_comm in d0.
        apply ((proj1 free_vars_under_struct_cong) _ _ d0) in Hfv. congruence.
      }
      rewrite (proj1 down_ren_up_ren_commute); auto.
      * apply shift_preserves_bijection; auto.
      * intros. exfalso; lia.
      * replace 0 with (swap01 1) by auto. apply nfv_under_renaming; auto.
        apply swap01_is_bijective.
    - fold rename_process. auto.
    - auto.
    - assert (
        rename_process (rename_process Q (up_ren (up_ren r))) swap01 =
        rename_process (rename_process Q swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H3. rewrite <- e0.
      assert (
        rename_process (rename_process (up R) swap01) (up_ren (up_ren r)) =
        rename_process (rename_process (up R) (up_ren (up_ren r))) swap01
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      assert (
        up (rename_process R (up_ren r)) =
        rename_process (up R) (up_ren (up_ren r))
      ).
      {
        unfold up.
        rewrite (proj1 ren_up_up_ren_commute); auto.
        + apply shift_preserves_bijection; auto.
        + intros. exfalso; lia.
      }
      rewrite H5. rewrite <- H4. rewrite <- e1.
      replace
        (cut (rename_process Q' (up_ren (up_ren r))) (rename_process R' (up_ren (up_ren r))))
        with
        (rename_process (cut Q' R') (up_ren r))
        by auto.
      apply H1. apply shift_preserves_bijection; auto.
  + simpl. eapply dc_cut_assoc_l_comm.
    - apply H. apply shift_preserves_bijection. auto.
    - fold rename_process.
      replace 1 with (up_ren (up_ren r) 1) by auto.
      apply ((proj1 nfv_under_renaming) _ (up_ren (up_ren r)) _) in n;
      try (repeat apply shift_preserves_bijection; auto).
    - fold rename_process. apply H0.
      repeat apply shift_preserves_bijection. auto.
    - rewrite e. unfold down.
      assert (
        rename_process (rename_process P' (up_ren (up_ren r))) swap01 =
        rename_process (rename_process P' swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H3.
      assert (~ 1 ∈ P').
      {
        intro Hfv. apply directed_cong_in_struct_cong in d0. apply c_comm in d0.
        apply ((proj1 free_vars_under_struct_cong) _ _ d0) in Hfv. congruence.
      }
      rewrite (proj1 down_ren_up_ren_commute); auto.
      * apply shift_preserves_bijection; auto.
      * intros. exfalso; lia.
      * replace 0 with (swap01 1) by auto. apply nfv_under_renaming; auto.
        apply swap01_is_bijective.
    - fold rename_process. auto.
    - auto.
    - assert (
        rename_process (rename_process Q (up_ren (up_ren r))) swap01 =
        rename_process (rename_process Q swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H3. rewrite <- e0.
      assert (
        rename_process (rename_process (up R) swap01) (up_ren (up_ren r)) =
        rename_process (rename_process (up R) (up_ren (up_ren r))) swap01
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      assert (
        up (rename_process R (up_ren r)) =
        rename_process (up R) (up_ren (up_ren r))
      ).
      {
        unfold up.
        rewrite (proj1 ren_up_up_ren_commute); auto.
        + apply shift_preserves_bijection; auto.
        + intros. exfalso; lia.
      }
      rewrite H5. rewrite <- H4. rewrite <- e1.
      replace
        (cut (rename_process Q' (up_ren (up_ren r))) (rename_process R' (up_ren (up_ren r))))
        with
        (rename_process (cut Q' R') (up_ren r))
        by auto.
      apply H1. apply shift_preserves_bijection; auto.
  + simpl. eapply dc_cut_assoc_r.
    - apply H. apply shift_preserves_bijection. auto.
    - fold rename_process.
      replace 1 with (up_ren (up_ren r) 1) by auto.
      apply ((proj1 nfv_under_renaming) _ (up_ren (up_ren r)) _) in n;
      try (repeat apply shift_preserves_bijection; auto).
    - fold rename_process. apply H0.
      repeat apply shift_preserves_bijection. auto.
    - auto.
    - fold rename_process. auto.
    - rewrite e1. unfold down.
      assert (
        rename_process (rename_process R' (up_ren (up_ren r))) swap01 =
        rename_process (rename_process R' swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H3.
      assert (~ 1 ∈ R').
      {
        intro Hfv. apply directed_cong_in_struct_cong in d0. apply c_comm in d0.
        apply ((proj1 free_vars_under_struct_cong) _ _ d0) in Hfv. congruence.
      }
      rewrite (proj1 down_ren_up_ren_commute); auto.
      * apply shift_preserves_bijection; auto.
      * intros. exfalso; lia.
      * replace 0 with (swap01 1) by auto. apply nfv_under_renaming; auto.
        apply swap01_is_bijective.
    - assert (
        rename_process (rename_process Q (up_ren (up_ren r))) swap01 =
        rename_process (rename_process Q swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H3. rewrite <- e0.
      assert (
        rename_process (rename_process (up P) swap01) (up_ren (up_ren r)) =
        rename_process (rename_process (up P) (up_ren (up_ren r))) swap01
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      assert (
        up (rename_process P (up_ren r)) =
        rename_process (up P) (up_ren (up_ren r))
      ).
      {
        unfold up.
        rewrite (proj1 ren_up_up_ren_commute); auto.
        + apply shift_preserves_bijection; auto.
        + intros. exfalso; lia.
      }
      rewrite H5. rewrite <- H4. rewrite <- e.
      replace
        (cut (rename_process P' (up_ren (up_ren r))) (rename_process Q' (up_ren (up_ren r))))
        with
        (rename_process (cut P' Q') (up_ren r))
        by auto.
      apply H1. apply shift_preserves_bijection; auto.
  + simpl. eapply dc_cut_assoc_r_comm.
    - apply H. apply shift_preserves_bijection. auto.
    - fold rename_process.
      replace 1 with (up_ren (up_ren r) 1) by auto.
      apply ((proj1 nfv_under_renaming) _ (up_ren (up_ren r)) _) in n;
      try (repeat apply shift_preserves_bijection; auto).
    - fold rename_process. apply H0.
      repeat apply shift_preserves_bijection. auto.
    - auto.
    - fold rename_process. auto.
    - rewrite e1. unfold down.
      assert (
        rename_process (rename_process R' (up_ren (up_ren r))) swap01 =
        rename_process (rename_process R' swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H3.
      assert (~ 1 ∈ R').
      {
        intro Hfv. apply directed_cong_in_struct_cong in d0. apply c_comm in d0.
        apply ((proj1 free_vars_under_struct_cong) _ _ d0) in Hfv. congruence.
      }
      rewrite (proj1 down_ren_up_ren_commute); auto.
      * apply shift_preserves_bijection; auto.
      * intros. exfalso; lia.
      * replace 0 with (swap01 1) by auto. apply nfv_under_renaming; auto.
        apply swap01_is_bijective.
    - assert (
        rename_process (rename_process Q (up_ren (up_ren r))) swap01 =
        rename_process (rename_process Q swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H3. rewrite <- e0.
      assert (
        rename_process (rename_process (up P) swap01) (up_ren (up_ren r)) =
        rename_process (rename_process (up P) (up_ren (up_ren r))) swap01
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      assert (
        up (rename_process P (up_ren r)) =
        rename_process (up P) (up_ren (up_ren r))
      ).
      {
        unfold up.
        rewrite (proj1 ren_up_up_ren_commute); auto.
        + apply shift_preserves_bijection; auto.
        + intros. exfalso; lia.
      }
      rewrite H5. rewrite <- H4. rewrite <- e.
      replace
        (cut (rename_process P' (up_ren (up_ren r))) (rename_process Q' (up_ren (up_ren r))))
        with
        (rename_process (cut P' Q') (up_ren r))
        by auto.
      apply H1. apply shift_preserves_bijection; auto. *)
Admitted.

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
  (* apply directed_cong_ind; intros; try now (econstructor; eauto).
  + simpl. subst. eapply dc_cut_assoc_l.
    - apply H.
    - fold lift_process. apply nfv_up_lt; try lia. auto.
    - fold lift_process. apply H0.
    - unfold down.
      rewrite (proj1 lift_after_down_lt_commute); try lia.
      rewrite (proj1 lift_at_k_rename_id_after_k_commute); auto. apply swap01_is_bijective.
      intros [|[|]] ?; auto; exfalso; lia.
    - auto.
    - auto.
    - fold lift_process.
      rewrite <- (proj1 lift_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      unfold up. rewrite <- (proj1 lift_k_lift_Sj_lt_commute); try lia.
      rewrite <- (proj1 lift_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      replace (
        (cut (lift_process (rename_process Q swap01) (S (S k)) 1)
             (lift_process (rename_process (lift_process R 0 1) swap01) (S (S k)) 1))
      ) with (
        (lift_process (cut (rename_process Q swap01) (rename_process (up R) swap01)) (S k) 1)
      ) by auto.
      apply H1.
      all: intros [|[|]] ?; auto; exfalso; lia.
  + simpl. subst. eapply dc_cut_assoc_l_comm.
    - apply H.
    - fold lift_process. apply nfv_up_lt; try lia. auto.
    - fold lift_process. apply H0.
    - unfold down.
      rewrite (proj1 lift_after_down_lt_commute); try lia.
      rewrite (proj1 lift_at_k_rename_id_after_k_commute); auto. apply swap01_is_bijective.
      intros [|[|]] ?; auto; exfalso; lia.
    - auto.
    - auto.
    - fold lift_process.
      rewrite <- (proj1 lift_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      unfold up. rewrite <- (proj1 lift_k_lift_Sj_lt_commute); try lia.
      rewrite <- (proj1 lift_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      replace (
        (cut (lift_process (rename_process Q swap01) (S (S k)) 1)
             (lift_process (rename_process (lift_process R 0 1) swap01) (S (S k)) 1))
      ) with (
        (lift_process (cut (rename_process Q swap01) (rename_process (up R) swap01)) (S k) 1)
      ) by auto.
      apply H1.
      all: intros [|[|]] ?; auto; exfalso; lia.
  + simpl. subst. eapply dc_cut_assoc_r.
    - apply H.
    - apply nfv_up_lt; try lia. auto.
    - apply H0.
    - auto.
    - fold lift_process. auto.
    - unfold down.
      rewrite (proj1 lift_after_down_lt_commute); try lia.
      rewrite (proj1 lift_at_k_rename_id_after_k_commute); auto. apply swap01_is_bijective.
      intros [|[|]] ?; auto; exfalso; lia.
    - fold lift_process.
      rewrite <- (proj1 lift_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      unfold up. rewrite <- (proj1 lift_k_lift_Sj_lt_commute); try lia.
      rewrite <- (proj1 lift_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      replace (
        (cut (lift_process (rename_process Q swap01) (S (S k)) 1)
             (lift_process (rename_process (lift_process R 0 1) swap01) (S (S k)) 1))
      ) with (
        (lift_process (cut (rename_process Q swap01) (rename_process (up R) swap01)) (S k) 1)
      ) by auto.
      apply H1.
      all: intros [|[|]] ?; auto; exfalso; lia.
  + simpl. subst. eapply dc_cut_assoc_r_comm.
    - apply H.
    - apply nfv_up_lt; try lia. auto.
    - apply H0.
    - auto.
    - fold lift_process. auto.
    - unfold down.
      rewrite (proj1 lift_after_down_lt_commute); try lia.
      rewrite (proj1 lift_at_k_rename_id_after_k_commute); auto. apply swap01_is_bijective.
      intros [|[|]] ?; auto; exfalso; lia.
    - fold lift_process.
      rewrite <- (proj1 lift_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      unfold up. rewrite <- (proj1 lift_k_lift_Sj_lt_commute); try lia.
      rewrite <- (proj1 lift_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      replace (
        (cut (lift_process (rename_process Q swap01) (S (S k)) 1)
             (lift_process (rename_process (lift_process R 0 1) swap01) (S (S k)) 1))
      ) with (
        (lift_process (cut (rename_process Q swap01) (rename_process (up R) swap01)) (S k) 1)
      ) by auto.
      apply H1.
      all: intros [|[|]] ?; auto; exfalso; lia. *)
Admitted.

Lemma directed_cong_invariant_under_downshifting :
  (forall P Q, P ⇛ Q -> forall k,
    (~ k ∈ P) -> ((down1_process P k) ⇛ (down1_process Q k))) /\
  (forall M N, M !⇛ N -> forall k,
    (~ (occurs_free_message k M)) -> ((down1_message M k) !⇛ (down1_message N k))) /\
  (forall s t, s $⇛ t -> forall k,
    (~ (occurs_free_statement k s)) -> ((down1_statement s k) $⇛ (down1_statement t k))).
Proof.
  (* apply directed_cong_ind; intros; simpl; try (now (econstructor));
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
  + eapply dc_cut_assoc_l.
    - apply H. intros Hfv. apply H2. repeat free_var_econstructor; eauto.
    - fold down1_process. apply (proj1 nfv_down_lt); auto. lia.
    - fold down1_process. apply H0.
      intro Hfv. apply H2. apply fv_cut_l.
      apply directed_cong_in_struct_cong in d.
      assert ((S k) ∈ (cut P Q)) by (repeat free_var_econstructor; eauto).
      apply ((proj1 free_vars_under_struct_cong) _ _ d) in H3. auto.
    - subst. unfold down.
      rewrite <- (proj1 down_at_k_rename_id_after_k_commute).
      * rewrite (proj1 down_k_down_Sj_lt_commute); auto. lia.
      * apply swap01_is_bijective.
      * intros [|[|]] ?; auto; exfalso; lia.
    - fold down1_process. auto.
    - auto.
    - fold lift_process.
      rewrite <- (proj1 down_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      rewrite <- e0.
      unfold up.
      rewrite <- (proj1 down_after_down_gt_commute); try lia.
      rewrite <- (proj1 down_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      replace (lift_process R 0 1) with (up R) by auto. rewrite <- e1.
      apply H1.
      * intro Hfv. inversion Hfv; subst.
        ++ replace (S (S k)) with (swap01 (S (S k))) in H5 by auto.
           apply fv_under_renaming in H5; try apply swap01_is_bijective.
           apply H2. apply fv_cut_l.
           apply directed_cong_in_struct_cong in d.
           assert ((S k) ∈ (cut P Q)) by (repeat free_var_econstructor; eauto).
           apply ((proj1 free_vars_under_struct_cong) _ _ d) in H3. auto.
        ++ apply H2. apply fv_cut_r.
           replace (S (S k)) with (swap01 (S (S k))) in H5 by auto.
           apply fv_under_renaming in H5; try apply swap01_is_bijective.
           apply fv_up_Sn2 in H5; auto; lia.
      * intros [|[|]] ?; auto; exfalso; lia.
      * intros [|[|]] ?; auto; exfalso; lia.
  + eapply dc_cut_assoc_l_comm.
    - apply H. intros Hfv. apply H2. repeat free_var_econstructor; eauto.
    - fold down1_process. apply (proj1 nfv_down_lt); auto. lia.
    - fold down1_process. apply H0.
      intro Hfv. apply H2. apply fv_cut_l.
      apply directed_cong_in_struct_cong in d.
      assert ((S k) ∈ (cut P Q)) by (repeat free_var_econstructor; eauto).
      apply ((proj1 free_vars_under_struct_cong) _ _ d) in H3. auto.
    - subst. unfold down.
      rewrite <- (proj1 down_at_k_rename_id_after_k_commute).
      * rewrite (proj1 down_k_down_Sj_lt_commute); auto. lia.
      * apply swap01_is_bijective.
      * intros [|[|]] ?; auto; exfalso; lia.
    - fold down1_process. auto.
    - auto.
    - fold lift_process.
      rewrite <- (proj1 down_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      rewrite <- e0.
      unfold up.
      rewrite <- (proj1 down_after_down_gt_commute); try lia.
      rewrite <- (proj1 down_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      replace (lift_process R 0 1) with (up R) by auto. rewrite <- e1.
      apply H1.
      * intro Hfv. inversion Hfv; subst.
        ++ replace (S (S k)) with (swap01 (S (S k))) in H5 by auto.
           apply fv_under_renaming in H5; try apply swap01_is_bijective.
           apply H2. apply fv_cut_l.
           apply directed_cong_in_struct_cong in d.
           assert ((S k) ∈ (cut P Q)) by (repeat free_var_econstructor; eauto).
           apply ((proj1 free_vars_under_struct_cong) _ _ d) in H3. auto.
        ++ apply H2. apply fv_cut_r.
           replace (S (S k)) with (swap01 (S (S k))) in H5 by auto.
           apply fv_under_renaming in H5; try apply swap01_is_bijective.
           apply fv_up_Sn2 in H5; auto; lia.
      * intros [|[|]] ?; auto; exfalso; lia.
      * intros [|[|]] ?; auto; exfalso; lia.
  + eapply dc_cut_assoc_r.
    - apply H. intros Hfv. apply H2. repeat free_var_econstructor; eauto.
    - fold down1_process. apply (proj1 nfv_down_lt); auto. lia.
    - fold down1_process. apply H0.
      intro Hfv. apply H2. apply fv_cut_r.
      apply directed_cong_in_struct_cong in d.
      assert ((S k) ∈ (cut Q R)) by (repeat free_var_econstructor; eauto).
      apply ((proj1 free_vars_under_struct_cong) _ _ d) in H3. auto.
    - auto.
    - fold down1_process. auto.
    - subst. unfold down.
      rewrite <- (proj1 down_at_k_rename_id_after_k_commute).
      * rewrite (proj1 down_k_down_Sj_lt_commute); auto. lia.
      * apply swap01_is_bijective.
      * intros [|[|]] ?; auto; exfalso; lia.
    - fold lift_process.
      rewrite <- (proj1 down_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      rewrite <- e0.
      unfold up.
      rewrite <- (proj1 down_after_down_gt_commute); try lia.
      rewrite <- (proj1 down_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      replace (lift_process P 0 1) with (up P) by auto. rewrite <- e.
      apply H1.
      * intro Hfv. inversion Hfv; subst.
        ++ replace (S (S k)) with (swap01 (S (S k))) in H5 by auto.
           apply fv_under_renaming in H5; try apply swap01_is_bijective.
           apply H2. apply fv_cut_l.
           apply fv_up_Sn2 in H5; auto; lia.
        ++ apply H2. apply fv_cut_r.
           replace (S (S k)) with (swap01 (S (S k))) in H5 by auto.
           apply fv_under_renaming in H5; try apply swap01_is_bijective.
           apply directed_cong_in_struct_cong in d.
           assert ((S k) ∈ (cut Q R)) by (repeat free_var_econstructor; eauto).
           apply ((proj1 free_vars_under_struct_cong) _ _ d) in H3. auto.
      * intros [|[|]] ?; auto; exfalso; lia.
      * intros [|[|]] ?; auto; exfalso; lia.
  + eapply dc_cut_assoc_r_comm.
    - apply H. intros Hfv. apply H2. repeat free_var_econstructor; eauto.
    - fold down1_process. apply (proj1 nfv_down_lt); auto. lia.
    - fold down1_process. apply H0.
      intro Hfv. apply H2. apply fv_cut_r.
      apply directed_cong_in_struct_cong in d.
      assert ((S k) ∈ (cut Q R)) by (repeat free_var_econstructor; eauto).
      apply ((proj1 free_vars_under_struct_cong) _ _ d) in H3. auto.
    - auto.
    - fold down1_process. auto.
    - subst. unfold down.
      rewrite <- (proj1 down_at_k_rename_id_after_k_commute).
      * rewrite (proj1 down_k_down_Sj_lt_commute); auto. lia.
      * apply swap01_is_bijective.
      * intros [|[|]] ?; auto; exfalso; lia.
    - fold lift_process.
      rewrite <- (proj1 down_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      rewrite <- e0.
      unfold up.
      rewrite <- (proj1 down_after_down_gt_commute); try lia.
      rewrite <- (proj1 down_at_k_rename_id_after_k_commute); try apply swap01_is_bijective.
      replace (lift_process P 0 1) with (up P) by auto. rewrite <- e.
      apply H1.
      * intro Hfv. inversion Hfv; subst.
        ++ replace (S (S k)) with (swap01 (S (S k))) in H5 by auto.
           apply fv_under_renaming in H5; try apply swap01_is_bijective.
           apply H2. apply fv_cut_l.
           apply fv_up_Sn2 in H5; auto; lia.
        ++ apply H2. apply fv_cut_r.
           replace (S (S k)) with (swap01 (S (S k))) in H5 by auto.
           apply fv_under_renaming in H5; try apply swap01_is_bijective.
           apply directed_cong_in_struct_cong in d.
           assert ((S k) ∈ (cut Q R)) by (repeat free_var_econstructor; eauto).
           apply ((proj1 free_vars_under_struct_cong) _ _ d) in H3. auto.
      * intros [|[|]] ?; auto; exfalso; lia.
      * intros [|[|]] ?; auto; exfalso; lia.
  + econstructor; try apply (H (S k)); try apply H0; intro Hfv; apply H1; free_var_econstructor; auto.
  + econstructor; apply H; intro Hfv; apply H0; free_var_econstructor; auto. *)
Admitted.

(******************************************************************************)
(* Transitivity is admissible                                                 *)
(******************************************************************************)
Lemma directed_cong_triangle :
  (forall P1 P2, P1 ⇛ P2 -> forall P3, P1 ⇛ P3 -> P2 ⇛ P3) /\
  (forall M1 M2, M1 !⇛ M2 -> forall M3, M1 !⇛ M3 -> M2 !⇛ M3) /\
  (forall s1 s2, s1 $⇛ s2 -> forall s3, s1 $⇛ s3 -> s2 $⇛ s3).
Proof.
  (* apply directed_cong_ind; intros.
  + inversion H1; subst.
    - apply dc_cong_link; try apply H; try apply H0; auto.
    - apply dc_link; try apply H; try apply H0; auto.
  + inversion H1; subst.
    - apply dc_link; try apply H; try apply H0; auto.
    - apply dc_cong_link; try apply H; try apply H0; auto.
  + admit.
  (* + inversion H1; subst.
    - apply dc_cong_cut; try apply H; try apply H0; eauto.
    - assert ( P' ⇛ (cut P0 Q0) ) by apply (H _ H4).
      (* show that if P ⇛ cut P0 Q0, then also P ⇛ cut Q0 P0 *)
      (* and other direction as well since we haven't proven symmetry yet *)
      assert ( P' ⇛ (cut Q0 P0) )
        by admit.
      eapply dc_cut_assoc_r_comm.
      * apply H3.
      * assumption.
      * admit.
      * auto.
      * auto.
      * auto.
      * admit.
    - admit.
    - admit.
    - admit.
    - apply dc_cut_comm; try apply H; try apply H0; eauto. *)
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + inversion H1; subst; econstructor; eauto.
  + inversion H; econstructor.
  + inversion H0; econstructor; eauto. apply H. apply dc_cong_reflS.
  + auto.
  + inversion H0; econstructor; eauto. apply H. apply directed_cong_reflexive.
  + inversion H0; econstructor; eauto. apply H. apply directed_cong_reflexive.
  + inversion H1; econstructor; eauto; try apply H; try apply H0; apply directed_cong_reflexive.
  + inversion H1; econstructor; eauto; try apply H; try apply H0; apply directed_cong_reflexive.
  + inversion H0; econstructor; eauto. apply H. apply directed_cong_reflexive.
  + inversion H; econstructor.
  + inversion H0; econstructor; eauto. apply H. apply directed_cong_reflexive.
  + auto. *)
Admitted.

(******************************************************************************)
(* Symmetry is admissible                                                     *)
(******************************************************************************)
(* Lemma directed_cong_cut_comm_common_reduct :
  forall P1 P2 Q, (cut P1 P2) ⇛ Q -> (cut P2 P1) ⇛ Q.
Proof.
  intros.
  generalize dependent P1.
  generalize dependent P2.
  induction Q; intros; try (now (inversion H)).
  inversion H; subst.
  + apply dc_cong_cut; auto.
  + 
    admit.
  + admit.
  + admit.
  + admit.
  + apply dc_cut_comm; auto.
Admitted. *)

Lemma directed_cong_symm :
  (forall P1 P2, P1 ⇛ P2 -> P2 ⇛ P1) /\
  (forall M1 M2, M1 !⇛ M2 -> M2 !⇛ M1) /\
  (forall s1 s2, s1 $⇛ s2 -> s2 $⇛ s1).
Proof.
  apply directed_cong_ind; intros; try now (econstructor; eauto).
  + assert ((down (rename_process P' swap01)) ⇛ (down (rename_process P swap01))).
    {
      apply directed_cong_invariant_under_downshifting.
      + apply directed_cong_invariant_under_renaming; auto. apply swap01_is_bijective.
      + apply nfv_01_swap. intro Hfv.
        apply directed_cong_in_struct_cong in d0. apply c_comm in d0.
        apply (proj1 free_vars_under_struct_cong) with (k := 1) in d0. apply n.
        apply d0. auto.
    }
    eapply dc_cut_assoc_r1.
    - apply H2.
    - rewrite e1. apply nfv_10_swap. apply nfv_lift_n; lia.
    - rewrite e. apply H3.
    - assert (
        (rename_process (up R') swap01) ⇛ (rename_process (up R) swap01)
      ).
      {
        apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
        apply directed_cong_invariant_under_upshifting; auto.
      }
      rewrite e1. apply H4.
    - autorewrite with up_down_rename_rewrites. reflexivity.
      apply nfv_01_swap; auto.
    - rewrite e0. autorewrite with up_down_rename_rewrites; auto.
    - subst; autorewrite with up_down_rename_rewrites; auto.
    - apply H.
  + assert ((down (rename_process P' swap01)) ⇛ (down (rename_process P swap01))).
    {
      apply directed_cong_invariant_under_downshifting.
      + apply directed_cong_invariant_under_renaming; auto. apply swap01_is_bijective.
      + apply nfv_01_swap. intro Hfv.
        apply directed_cong_in_struct_cong in d0. apply c_comm in d0.
        apply (proj1 free_vars_under_struct_cong) with (k := 1) in d0. apply n.
        apply d0. auto.
    }
    eapply dc_cut_assoc_r2.
    - apply H2.
    - rewrite e1. apply nfv_10_swap. apply nfv_lift_n; lia.
    - rewrite e. apply H3.
    - assert (
        (rename_process (up R') swap01) ⇛ (rename_process (up R) swap01)
      ).
      {
        apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
        apply directed_cong_invariant_under_upshifting; auto.
      }
      rewrite e1. apply H4.
    - autorewrite with up_down_rename_rewrites. reflexivity.
      apply nfv_01_swap. auto.
    - rewrite e0. autorewrite with up_down_rename_rewrites; auto.
    - subst; autorewrite with up_down_rename_rewrites; auto.
    - auto.
  + admit.
  + admit.

    (* assert ((rename_process Q1 swap01) ⇛ (rename_process Q swap01)).
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
    eapply c_cut_assoc_l; eauto. apply nfv_10_swap. apply nfv_lift_n. lia. *)
Admitted.

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
