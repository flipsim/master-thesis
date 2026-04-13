From FD Require Import Syntax.
From FD Require Import Reduction.
From FD Require Import FreeVars.
From FD Require Import Renaming.
From FD Require Import FreeVars.
From FD Require Import StructCong.
From FD Require Import ConfluenceDefs.
From FD Require Import DirectedCong.

From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Relations.Operators_Properties.
From Stdlib Require Import Relation_Definitions.

(* Definition link_future (P : process) (x : nat) (M : message) : Prop :=
  P = (link (future x) M) \/ P = (link M (future x)). *)

(* ⊵ trianglerighteq *)
(* Reserved Notation "P ⊵ Q" (no associativity, at level 61).

Inductive par_reduces : process -> process -> Prop :=
  (* embed ⇛ into ⊵ *)
  | rp_directed_cong : forall P Q, P ⇛ Q -> P ⊵ Q

  (* duplicate β-redexes up to symmetry of links *)
  | rp_tensor_par_1 : forall P P' Q Q' R R' P'',
      P ⇛ P' -> Q ⇛ Q' -> R ⇛ R' -> P'' = rename_process (up P') swap01 ->
      link (prefix (send P Q)) (prefix (receive R)) ⊵ (cut (cut R' P'')) Q'
  | rp_tensor_par_2 : forall P P' Q Q' R R' P'',
      P ⇛ P' -> Q ⇛ Q' -> R ⇛ R' -> P'' = rename_process (up P') swap01 ->
      link (prefix (receive R)) (prefix (send P Q)) ⊵ (cut (cut R' P'')) Q'
  | rp_plus_with_l1 : forall P P' Q Q' R R',
      P ⇛ P' -> Q ⇛ Q' -> R ⇛ R' ->
      link (prefix (choose_left P)) (prefix (offer_choice Q R)) ⊵ cut P' Q'
  | rp_plus_with_l2 : forall P P' Q Q' R R',
      P ⇛ P' -> Q ⇛ Q' -> R ⇛ R' ->
      link (prefix (offer_choice Q R)) (prefix (choose_left P)) ⊵ cut P' Q'
  | rp_plus_with_r1 : forall (P P' Q R R' : process),
      P ⇛ P' -> R ⇛ R' ->
      link (prefix (choose_right P)) (prefix (offer_choice Q R)) ⊵ cut P' R'
  | rp_plus_with_r2 : forall (P P' Q R R' : process),
      P ⇛ P' -> R ⇛ R' ->
      link (prefix (offer_choice Q R)) (prefix (choose_right P)) ⊵ cut P' R'
  | rp_one_bot1 : forall P P', P ⇛ P' -> link (prefix close) (prefix (wait P)) ⊵ P'
  | rp_one_bot2 : forall P P', P ⇛ P' -> link (prefix (wait P)) (prefix close) ⊵ P'

  (* duplicate AxCut up to commutation of cuts (and links) *)
  | rp_ax_cut1 : forall Q M M' P P',
      P ⇛ P' -> M !⇛ M' -> link_future Q 0 M ->
      cut Q P ⊵ subst_process P' ((downM M') ⋅ id_subst)
  | rp_ax_cut2 : forall Q M M' P P',
      P ⇛ P' -> M !⇛ M' -> link_future Q 0 M ->
      cut P Q ⊵ subst_process P' ((downM M') ⋅ id_subst)

  (* duplicate AxCut up to association of cuts (and symmetry links) *)
  | rp_ax_cut_assoc_1 : forall P P' P'' M M' M'' R R' R'' Q,
      link_future Q 1 M -> P ⊵ P' -> M !⇛ M' -> R ⊵ R' ->
      P'' = rename_process (up P') swap01 ->
      M'' = rename_message M' swap01 ->
      R'' = down (rename_process R' swap01) ->
      cut P (cut Q R) ⊵ cut (subst_process P'' ((downM M'' ⋅ id_subst))) R''
  | rp_ax_cut_assoc_2 : forall P P' P'' M M' M'' R R' R'' Q,
      link_future Q 1 M -> P ⊵ P' -> M !⇛ M' -> R ⊵ R' ->
      P'' = rename_process (up P') swap01 ->
      M'' = rename_message M' swap01 ->
      R'' = down (rename_process R' swap01) ->
      cut P (cut R Q) ⊵ cut (subst_process P'' ((downM M'' ⋅ id_subst))) R''
  | rp_ax_cut_assoc_3 : forall P P' P'' M M' M'' R R' R'' Q,
      link_future Q 1 M -> P ⊵ P' -> M !⇛ M' -> R ⊵ R' ->
      P'' = rename_process (up P') swap01 ->
      M'' = rename_message M' swap01 ->
      R'' = down (rename_process R' swap01) ->
      cut (cut Q R) P ⊵ cut (subst_process P'' ((downM M'' ⋅ id_subst))) R''
  | rp_ax_cut_assoc_4 : forall P P' P'' M M' M'' R R' R'' Q,
      link_future Q 1 M -> P ⊵ P' -> M !⇛ M' -> R ⊵ R' ->
      P'' = rename_process (up P') swap01 ->
      M'' = rename_message M' swap01 ->
      R'' = down (rename_process R' swap01) ->
      cut (cut R Q) P ⊵ cut (subst_process P'' ((downM M'' ⋅ id_subst))) R''

  (* seq *)
  | rp_seq : forall P P' s s', P ⇛ P' -> s $⇛ s' ->
      seq P s ⊵ subst_process P' ((prefix s') ⋅ id_subst)

  (* congruences *)
  | rp_cong_cut : forall P P' Q Q', P ⊵ P' -> Q ⊵ Q' -> cut P Q ⊵ cut P' Q'
  | rp_cong_seq : forall P P' s s', P ⊵ P' -> s $⇛ s' -> seq P s ⊵ seq P' s'
where
  "P ⊵ Q" := (par_reduces P Q). *)

Reserved Notation "P ⊵ Q" (no associativity, at level 61).

Inductive par_reduces : process -> process -> Prop :=
  (* embed ⇛ into ⊵ *)
  | rp_directed_cong : forall P Q, P ⇛ Q -> P ⊵ Q

  (* duplicate β-redexes up to symmetry of links *)
  | rp_tensor_par_1 : forall P P' Q Q' R R' P'',
      P ⇛ P' -> Q ⇛ Q' -> R ⇛ R' -> P'' = rename_process (up P') swap01 ->
      link (prefix (send P Q)) (prefix (receive R)) ⊵ (cut (cut R' P'')) Q'
  | rp_tensor_par_2 : forall P P' Q Q' R R' P'',
      P ⇛ P' -> Q ⇛ Q' -> R ⇛ R' -> P'' = rename_process (up P') swap01 ->
      link (prefix (receive R)) (prefix (send P Q)) ⊵ (cut (cut R' P'')) Q'
  | rp_plus_with_l1 : forall P P' Q Q' R R',
      P ⇛ P' -> Q ⇛ Q' -> R ⇛ R' ->
      link (prefix (choose_left P)) (prefix (offer_choice Q R)) ⊵ cut P' Q'
  | rp_plus_with_l2 : forall P P' Q Q' R R',
      P ⇛ P' -> Q ⇛ Q' -> R ⇛ R' ->
      link (prefix (offer_choice Q R)) (prefix (choose_left P)) ⊵ cut P' Q'
  | rp_plus_with_r1 : forall (P P' Q R R' : process),
      P ⇛ P' -> R ⇛ R' ->
      link (prefix (choose_right P)) (prefix (offer_choice Q R)) ⊵ cut P' R'
  | rp_plus_with_r2 : forall (P P' Q R R' : process),
      P ⇛ P' -> R ⇛ R' ->
      link (prefix (offer_choice Q R)) (prefix (choose_right P)) ⊵ cut P' R'
  | rp_one_bot1 : forall P P', P ⇛ P' -> link (prefix close) (prefix (wait P)) ⊵ P'
  | rp_one_bot2 : forall P P', P ⇛ P' -> link (prefix (wait P)) (prefix close) ⊵ P'

  (* duplicate AxCut up to commutation and association of cuts *)
  | rp_ax_cut : forall M M' P P',
      P ⇛ P' -> M !⇛ M' -> (* !!!!!!!! this should be P ⊵ P' ??? or can we get away with ⇛ (I think this is the way, less effort ;) 
                                not sure though if this work because of rp_cong_cut (but since redexes do not overlap, i.e.
                                we dont really need a simultaneous reduction, this should be fine and if there are multiple
                                redexes, it should be possible to use rp_cong_cut) *)
      cut (link (future 0) M) P ⊵ subst_process P' ((downM M') ⋅ id_subst)
  | rp_ax_cut_comm : forall M M' P P',
      P ⇛ P' -> M !⇛ M' -> (* !!!!!!!! this should be P ⊵ P' *)
      cut P (link (future 0) M) ⊵ subst_process P' ((downM M') ⋅ id_subst)
  (* this rules allows contraction if reduction diverges because of c_cut_assoc_l *)
  | rp_ax_cut_assoc_l : forall P P' P'' M M' M'' R R' R'',
      P ⊵ P' -> M !⇛ M' -> R ⊵ R' -> ~ (1 ∈ R') -> (* can we get away with ⇛ instead of ⊵ *)
      P'' = rename_process (up P') swap01 ->
      M'' = rename_message M' swap01 ->
      R'' = down (rename_process R' swap01) -> (* if ~ 1 ∈ R' then down (ren R' swap01) = down R' *)
      cut P (cut (link (future 1) M) R) ⊵ cut (subst_process P'' ((downM M'' ⋅ id_subst))) R''
  (* this rules allows contraction if reduction diverges because of c_cut_assoc_r *)
  | rp_ax_cut_assoc_r : forall P P' P'' M M' M'' R R' R'',
      P ⊵ P' -> M !⇛ M' -> R ⊵ R' -> ~ (1 ∈ P') ->
      P'' = down (rename_process P' swap01) ->
      M'' = rename_message M' swap01 ->
      R'' = rename_process (up R') swap01 ->
      cut (cut P (link (future 1) M)) R ⊵ cut P'' (subst_process R'' ((downM M'' ⋅ id_subst)))

  (* seq *)
  | rp_seq : forall P P' s s', P ⇛ P' -> s $⇛ s' ->
      seq P s ⊵ subst_process P' ((prefix s') ⋅ id_subst)

  (* congruences *)
  | rp_cong_cut : forall P P' Q Q', P ⊵ P' -> Q ⊵ Q' -> cut P Q ⊵ cut P' Q'
  | rp_cong_seq : forall P P' s s', P ⊵ P' -> s $⇛ s' -> seq P s ⊵ seq P' s'
where
  "P ⊵ Q" := (par_reduces P Q).

Lemma clos_trans_1n_directed_cong_in_clos_trans_1n_par_reduces :
  forall P Q, (clos_trans_1n _ directed_congruence) P Q -> (clos_trans_1n _ par_reduces) P Q.
Proof.
  intros. induction H.
  + econstructor. econstructor. assumption.
  + eapply Relation_Operators.t1n_trans.
    - econstructor; eauto.
    - auto.
Qed.

Lemma single_step_struct_cong_in_clos_trans_par_red :
  forall P Q, (union _ reduces structural_congruence) P Q -> (clos_trans _ par_reduces) P Q.
Proof.
  intros. destruct H.
  + induction H.
    - econstructor. eapply rp_tensor_par_1; eauto; apply c_refl.
    - econstructor. eapply rp_plus_with_l1; eauto; apply c_refl.
    - econstructor. eapply rp_plus_with_r1; eauto; apply c_refl.
    - econstructor. eapply rp_one_bot1. apply c_refl.
    - econstructor. eapply rp_ax_cut; try eapply c_refl; try apply c_cong_reflM.
    - econstructor. eapply rp_seq. apply c_refl. apply c_cong_reflS.
    - clear H. induction IHreduces.
      * econstructor. apply rp_cong_cut; eauto. econstructor. apply c_refl.
      * eapply t_trans; eauto.
    - clear H. induction IHreduces.
      * econstructor. apply rp_cong_seq; eauto. econstructor.
      * eapply t_trans; eauto.
    - apply struct_cong_in_trans_directed_cong in H.
      apply struct_cong_in_trans_directed_cong in H1.
      apply clos_trans_1n_directed_cong_in_clos_trans_1n_par_reduces in H.
      apply clos_trans_1n_directed_cong_in_clos_trans_1n_par_reduces in H1.
      apply clos_trans_t1n_iff in H.
      apply clos_trans_t1n_iff in H1.
      eapply t_trans; eauto. eapply t_trans; eauto.
  + apply (proj1 struct_cong_in_trans_directed_cong) in H.
    apply clos_trans_t1n_iff.
    apply clos_trans_1n_directed_cong_in_clos_trans_1n_par_reduces. auto.
Qed.

Lemma multi_step_red_in_clos_trans_par_red :
  forall P Q, P ▶ Q -> (clos_trans _ par_reduces) P Q.
Proof.
  intros. induction H.
  + apply single_step_struct_cong_in_clos_trans_par_red in H. auto.
  + eapply Relation_Operators.t_trans; eauto.
Qed.

Ltac directed_cong_to_struct_cong :=
  match goal with
  | [ H : _  ⇛ _ |- _ ] => apply directed_cong_in_struct_cong in H
  | [ H : _ !⇛ _ |- _ ] => apply directed_cong_in_struct_cong in H
  | [ H : _ $⇛ _ |- _ ] => apply directed_cong_in_struct_cong in H
  end.

Lemma par_reduces_in_union_single_step_red_struct_cong :
  forall P Q, P ⊵ Q -> clos_trans _ (union _ reduces structural_congruence) P Q.
Proof.
  intros. induction H.
  + econstructor. apply directed_cong_in_struct_cong in H. right. auto.
  + econstructor. left; repeat directed_cong_to_struct_cong. eapply r_struct.
    - eapply StructCong.c_cong_link; eapply StructCong.c_cong_prefix; econstructor; eauto.
    - econstructor; eauto.
    - apply StructCong.c_refl.
  + econstructor. left; repeat directed_cong_to_struct_cong. eapply r_struct.
    - eapply StructCong.c_trans. apply StructCong.c_link.
      eapply StructCong.c_cong_link; eapply StructCong.c_cong_prefix; econstructor; eauto.
    - econstructor; eauto.
    - apply StructCong.c_refl.
  + econstructor. left; repeat directed_cong_to_struct_cong. eapply r_struct.
    - eapply StructCong.c_cong_link; eapply StructCong.c_cong_prefix; econstructor; eauto.
    - econstructor; eauto.
    - apply StructCong.c_refl.
  + econstructor. left; repeat directed_cong_to_struct_cong. eapply r_struct.
    - eapply StructCong.c_trans. apply StructCong.c_link.
      eapply StructCong.c_cong_link; eapply StructCong.c_cong_prefix; econstructor; eauto.
    - econstructor; eauto.
    - apply StructCong.c_refl.
  + econstructor. left; repeat directed_cong_to_struct_cong. eapply r_struct.
    - eapply StructCong.c_cong_link; eapply StructCong.c_cong_prefix; econstructor; eauto. apply StructCong.c_refl.
    - econstructor; eauto.
    - apply StructCong.c_refl.
  + econstructor. left; repeat directed_cong_to_struct_cong. eapply r_struct.
    - eapply StructCong.c_trans. apply StructCong.c_link.
      eapply StructCong.c_cong_link; eapply StructCong.c_cong_prefix; econstructor; eauto. apply StructCong.c_refl.
    - econstructor; eauto.
    - apply StructCong.c_refl.
  + econstructor. left; repeat directed_cong_to_struct_cong. eapply r_struct.
    - eapply StructCong.c_cong_link; eapply StructCong.c_cong_prefix; econstructor; eauto.
    - econstructor; eauto.
    - apply StructCong.c_refl.
  + econstructor. left; repeat directed_cong_to_struct_cong. eapply r_struct.
    - eapply StructCong.c_trans. apply StructCong.c_link.
      eapply StructCong.c_cong_link; eapply StructCong.c_cong_prefix; econstructor; eauto.
    - econstructor; eauto.
    - apply StructCong.c_refl.
  + econstructor. left; repeat directed_cong_to_struct_cong. eapply r_struct.
    - apply c_cong_cut; eauto. apply c_cong_link; eauto. econstructor.
    - econstructor.
    - apply StructCong.c_refl.
  + econstructor. left; repeat directed_cong_to_struct_cong. eapply r_struct.
    - eapply c_trans. apply StructCong.c_cut_comm.
      apply c_cong_cut; eauto. apply c_cong_link; eauto. econstructor.
    - econstructor.
    - apply StructCong.c_refl.
  + directed_cong_to_struct_cong.
    assert (
      clos_trans _ (union _ reduces structural_congruence)
        (cut P (cut (link (future 1) M) R))
        (cut P (cut (link (future 1) M') R))
    ).
    {
      econstructor. right. apply StructCong.c_cong_cut.
      apply StructCong.c_refl. apply StructCong.c_cong_cut; try apply StructCong.c_refl.
      apply c_cong_link; auto. econstructor.
    }
    eapply t_trans. apply H6. clear H0 H6 M.
    assert (
      clos_trans _ (union _ reduces structural_congruence)
        (cut P (cut (link (future 1) M') R))
        (cut P' (cut (link (future 1) M') R))
    ).
    {
      clear - IHpar_reduces1. induction IHpar_reduces1.
      + econstructor. destruct H.
        - left. apply r_cong_cut. assumption.
        - right. apply StructCong.c_cong_cut; auto. apply StructCong.c_refl.
      + eapply t_trans; eauto.
    }
    eapply t_trans. apply H0. clear IHpar_reduces1 H0 H P.
    assert (
      clos_trans _ (union _ reduces structural_congruence)
        (cut P' (cut (link (future 1) M') R))
        (cut P' (cut (link (future 1) M') R'))
    ).
    {
      clear - IHpar_reduces2. induction IHpar_reduces2.
      + econstructor. destruct H.
        - left. eapply r_struct.
          * apply StructCong.c_cut_comm.
          * apply r_cong_cut. eapply r_struct. apply StructCong.c_cut_comm.
            apply r_cong_cut; eauto. apply StructCong.c_cut_comm.
          * apply StructCong.c_cut_comm.
        - right. apply StructCong.c_cong_cut. apply StructCong.c_refl.
          apply StructCong.c_cong_cut. apply StructCong.c_refl. auto.
      + eapply t_trans; eauto.
    }
    eapply t_trans. apply H. clear H IHpar_reduces2 H1 R.
    assert (
      clos_trans process (union process reduces structural_congruence)
        (cut P' (cut (link (future 1) M') R'))
        (cut (cut (link (future 0) M'') P'') R'')
    ).
    {
      econstructor. right. subst.
      eapply c_trans.
      + eapply c_trans.
        * apply StructCong.c_cut_comm.
        * eapply c_cong_cut. apply StructCong.c_cut_comm.
          apply StructCong.c_refl.
      + eapply c_trans.
        * eapply c_cut_assoc; auto.
        * eapply c_trans.
          - eapply StructCong.c_cut_comm.
          - eapply c_cong_cut; apply StructCong.c_refl.
    }
    eapply t_trans. apply H. subst. clear H H2.
    econstructor. left. simpl. apply r_cong_cut. econstructor.
  + directed_cong_to_struct_cong.
    assert (
      clos_trans _ (union _ reduces structural_congruence)
        (cut (cut P (link (future 1) M)) R)
        (cut (cut P (link (future 1) M')) R)
    ).
    {
      econstructor. right. apply StructCong.c_cong_cut.
      apply StructCong.c_cong_cut; try apply StructCong.c_refl.
      apply c_cong_link; auto. econstructor. apply StructCong.c_refl.
    }
    eapply t_trans. apply H6. clear H0 H6 M.
    assert (
      clos_trans _ (union _ reduces structural_congruence)
        (cut (cut P (link (future 1) M')) R)
        (cut (cut P (link (future 1) M')) R')
    ).
    {
      clear - IHpar_reduces2. induction IHpar_reduces2.
      + econstructor. destruct H.
        - left. eapply r_struct.
          * apply StructCong.c_cut_comm.
          * apply r_cong_cut; eauto.
          * apply StructCong.c_cut_comm.
        - right. apply StructCong.c_cong_cut; auto.
          apply StructCong.c_cong_cut; apply StructCong.c_refl.
      + eapply t_trans; eauto.
    }
    eapply t_trans. apply H0. clear IHpar_reduces2 H0 H1 R.
    assert (
      clos_trans _ (union _ reduces structural_congruence)
        (cut (cut P (link (future 1) M')) R')
        (cut (cut P' (link (future 1) M')) R')
    ).
    {
      clear - IHpar_reduces1. induction IHpar_reduces1.
      + econstructor. destruct H.
        - left. apply r_cong_cut. apply r_cong_cut. auto.
        - right. apply StructCong.c_cong_cut. apply StructCong.c_cong_cut. auto.
          all: apply StructCong.c_refl.
      + eapply t_trans; eauto.
    }
    eapply t_trans. apply H0. clear H IHpar_reduces1 H0 P.
    assert (
      clos_trans process (union process reduces structural_congruence)
        (cut (cut P' (link (future 1) M')) R')
        (cut P'' (cut (link (future 0) M'') R''))
    ).
    { econstructor. right. subst. apply c_cut_assoc; auto. }
    eapply t_trans. apply H. subst. clear H H2.
    econstructor. left. eapply r_struct.
    - apply StructCong.c_cut_comm.
    - apply r_cong_cut. econstructor.
    - apply StructCong.c_cut_comm.
  + econstructor. left; repeat directed_cong_to_struct_cong. eapply r_struct.
    - eapply StructCong.c_cong_seq; eauto.
    - econstructor.
    - apply StructCong.c_refl.
  + clear H H0.
    assert (
      clos_trans _ (union _ reduces structural_congruence) (cut P Q) (cut P' Q)
    ).
    {
      clear IHpar_reduces2 Q'. induction IHpar_reduces1.
      + econstructor. destruct H.
        - left. econstructor. auto.
        - right. apply StructCong.c_cong_cut; auto. apply StructCong.c_refl.
      + eapply t_trans; eauto.
    }
    eapply t_trans. apply H. clear H IHpar_reduces1 P.
    induction IHpar_reduces2.
    - econstructor. destruct H.
      * left. eapply r_struct; [apply StructCong.c_cut_comm | econstructor; eauto | apply StructCong.c_cut_comm].
      * right. apply StructCong.c_cong_cut; auto. apply StructCong.c_refl.
    - eapply t_trans; eauto.
  + repeat directed_cong_to_struct_cong. clear H.
    eapply t_trans. { apply t_step. right. apply StructCong.c_cong_seq. apply StructCong.c_refl. eauto. }
    clear H0 s. induction IHpar_reduces.
    - econstructor. destruct H.
      * left. econstructor; auto.
      * right. apply StructCong.c_cong_seq; eauto.
        destruct ((proj2 (proj2 struct_cong_d_refl)) s').
        eapply (proj2 (proj2 struct_cong_from_struct_cong_d)); eauto.
    - eapply t_trans; eauto.
Qed.

Corollary clos_trans_par_red_in_multi_step_red :
  forall P Q, clos_trans process par_reduces P Q -> P ▶ Q.
Proof.
  intros. induction H.
  + apply par_reduces_in_union_single_step_red_struct_cong in H; auto.
  + eapply t_trans; eauto.
Qed.

Corollary par_reds_clos_trans_multi_step_red_coincide :
  forall P Q, (clos_trans _ par_reduces) P Q <-> P ▶ Q.
Proof.
  intros; split.
  + apply clos_trans_par_red_in_multi_step_red.
  + apply multi_step_red_in_clos_trans_par_red.
Qed.

(* TODO:
  (1) P ⇛ P' -> (forall x, σ_1 x !⇛ σ_2 x) -> P[σ_1] ⊵ P'[σ_2]
  (2) P ⊵ P' -> (forall x, σ_1 x !⇛ σ_2 x) -> P[σ_1] ⊵ P'[σ_2]
  (not sure if induction suffices or induction on depth)
*)
