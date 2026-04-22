From FD Require Import Syntax.
From FD Require Import Reduction.
From FD Require Import FreeVars.
From FD Require Import Renaming.
From FD Require Import FreeVars.
From FD Require Import StructCong.
From FD Require Import ConfluenceDefs.
From FD Require Import DirectedCong.

From Stdlib Require Import Program.Tactics.
From Stdlib Require Import Program.Wf.
From Stdlib Require Import FunInd.
From Stdlib Require Import Recdef.
From Stdlib Require Import Wf_nat.
From Stdlib Require Import Lia.

From Equations Require Import Equations.
Unset Equations With Funext. (* forces Equations not to use functional_extensionality_dep *)

(* Evaluation Contexts for AxCuts to allow reduction in the presence of
   cut association
*)
Inductive axcut_ctx (n : nat) : Type :=
  (* n ↔ ▢ *)
  | nil_l : axcut_ctx n
  (* ▢ ↔ n *)
  | nil_r : axcut_ctx n
  (* cut P E *)
  | cons_l : forall (P : process) (E : axcut_ctx (S n)), axcut_ctx n
  (* cut E P *)
  | cons_r : forall (E : axcut_ctx (S n)) (P : process), axcut_ctx n.

(* Well-formedness of evaluation contexts *)
(* Inductive well_formed_axcut_ctx (n : nat) : axcut_ctx n -> Prop :=
  | wf_nil_l : well_formed_axcut_ctx n (nil_l n)
  | wf_nil_r : well_formed_axcut_ctx n (nil_r n)
  | wf_cons_l : forall P (E : axcut_ctx (S n)),
                  ~ (1 ∈ P) -> well_formed_axcut_ctx (S n) E ->
                  well_formed_axcut_ctx n (cons_l n P E)
  | wf_cons_r : forall P (E : axcut_ctx (S n)),
                  ~ (1 ∈ P) -> well_formed_axcut_ctx (S n) E ->
                  well_formed_axcut_ctx n (cons_r n E P). *)

(* I think this should be: *)
Inductive well_formed_axcut_ctx (n : nat) : axcut_ctx n -> Prop :=
  | wf_nil_l : well_formed_axcut_ctx n (nil_l n)
  | wf_nil_r : well_formed_axcut_ctx n (nil_r n)
  | wf_cons_l : forall P (E : axcut_ctx (S n)),
                  ~ ((S n) ∈ P) -> well_formed_axcut_ctx (S n) E ->
                  well_formed_axcut_ctx n (cons_l n P E)
  | wf_cons_r : forall P (E : axcut_ctx (S n)),
                  ~ ((S n) ∈ P) -> well_formed_axcut_ctx (S n) E ->
                  well_formed_axcut_ctx n (cons_r n E P).

Fixpoint fill_hole {n : nat} (E : axcut_ctx n) (M : message) : process :=
  match E with
  | nil_l _ => link (future n) M
  | nil_r _ => link M (future n)
  | cons_l _ P E' => cut P (fill_hole E' (upM M))
  | cons_r _ E' P => cut (fill_hole E' (upM M)) P
  end.

Fixpoint rename_axcut_ctx {n : nat} (E : axcut_ctx n) (r : renaming) : (axcut_ctx (r n)) :=
  match E with
  | nil_l _ => nil_l (r n)
  | nil_r _ => nil_r (r n)
  | cons_l _ P E' => cons_l (r n) (rename_process P (up_ren r))
                                  (@rename_axcut_ctx (S n) E' (up_ren r))
  | cons_r _ E' P => cons_r (r n) (@rename_axcut_ctx (S n) E' (up_ren r))
                                  (rename_process P (up_ren r))
  end.

(* Length of an evaluation context *)
Fixpoint length_axcut_ctx {n : nat} (E : axcut_ctx n) : nat :=
  match E with
  | nil_l _ => 0
  | nil_r _ => 0
  | cons_l _ _ E' => S (length_axcut_ctx E')
  | cons_r _ E' _ => S (length_axcut_ctx E')
  end.

Lemma rename_axcut_ctx_preserves_length :
  forall {n : nat} (r : renaming) (E : axcut_ctx n),
    length_axcut_ctx E = length_axcut_ctx (rename_axcut_ctx E r).
Proof.
  intros. generalize dependent r. induction E; intros; simpl; auto;
  rewrite (IHE (up_ren r)); auto.
Qed.

(* reduce_axcut computes the reduct of an AxCut, i.e. the process
   cut P E_0[M] (or (cut E_0[M] P)) reduces to (reduce_axcut E M P)
*)
Definition lt_axcut_ctx n (E1 E2 : axcut_ctx n) : Prop :=
  (length_axcut_ctx E1) < (length_axcut_ctx E2).

Lemma lt_axcut_ctx_well_founded : forall n, well_founded (lt_axcut_ctx n).
Proof. intro n. apply well_founded_ltof. Qed.

Instance lt_axcut0_wf : WellFounded (lt_axcut_ctx 0).
Proof. apply lt_axcut_ctx_well_founded. Qed.

(* Definition reduce_axcut : (axcut_ctx 0) -> message -> process -> process.
  refine ( Fix (lt_axcut_ctx_well_founded 0) (fun _ => message -> process -> process)
    (fun (E : (axcut_ctx 0))
         (reduce_axcut : forall E' : axcut_ctx 0, lt_axcut_ctx 0 E' E -> message -> process -> process) =>
     (fun M P =>
        (match E as E1 return (E = E1 -> process) with
        (* cut P (link (future 0) M) *)
        | nil_l _ => fun Heq => subst_process P ((downM M) ⋅ id_subst)
        (* cut P (link M (future 0)) ≡ cut P (link (future 0) M) *)
        | nil_r _ => fun Heq => subst_process P ((downM M) ⋅ id_subst)
        (* If E WF, then ~ (1 ∈ Q). Thus,
            cut P (cut Q E'[upM M])
          ≡ cut (cut Q E'[upM M]) P
          ≡ cut (down (rename_process Q swap01))
                cut (rename_process E'[upM M] swap01) (* show that ren E'[upM M] = ren E' [ren (upM M)] *)
                    (rename_process (up P) swap01)
          ≡ cut (down (rename_process Q swap01))
                cut (rename_process (up P) swap01)
                    (rename_process E'[upM M] swap01)
        *)
        | cons_l _ Q E' => fun Heq =>
            cut (down (rename_process Q swap01))
                (reduce_axcut
                   (rename_axcut_ctx E' swap01)
                   _
                   (rename_message (upM M) swap01)
                   (rename_process (up P) swap01))
        (* If E WF, then ~ (1 ∈ Q). Thus,
            cut P (cut E'[upM M] Q)
          ≡ cut P (cut Q E'[upM M])
          ≡ cut (cut Q E'[upM M]) P
          ≡ cut (down (rename_process Q swap01))
                cut (rename_process E'[upM M] swap01) (* show that ren E'[upM M] = ren E' [ren (upM M)] *)
                    (rename_process (up P) swap01)
          ≡ cut (down (rename_process Q swap01))
                cut (rename_process (up P) swap01)
                    (rename_process E'[upM M] swap01)
        *)
        | cons_r _ E' Q => fun Heq =>
            cut (down (rename_process Q swap01))
                (reduce_axcut
                   (rename_axcut_ctx E' swap01)
                   _
                   (rename_message (upM M) swap01)
                   (rename_process (up P) swap01))
        end) (eq_refl E)))
  ).
  + intros; unfold lt_axcut_ctx. rewrite Heq. simpl. rewrite (rename_axcut_ctx_preserves_length swap01 E').
    apply PeanoNat.Nat.lt_succ_diag_r.
  + intros; unfold lt_axcut_ctx. rewrite Heq. simpl. rewrite (rename_axcut_ctx_preserves_length swap01 E').
    apply PeanoNat.Nat.lt_succ_diag_r.
Defined. *)

Equations? reduce_axcut (E : axcut_ctx 0) (M : message) (P : process) : process by wf E (lt_axcut_ctx 0) :=
  reduce_axcut (nil_l _) M P := subst_process P ((downM M) ⋅ id_subst);
  reduce_axcut (nil_r _) M P := subst_process P ((downM M) ⋅ id_subst);
  reduce_axcut (cons_l _ Q E') M P := cut (down (rename_process Q swap01))
                                          (reduce_axcut
                                             (rename_axcut_ctx E' swap01)
                                             (rename_message (upM M) swap01)
                                             (rename_process (up P) swap01));
  reduce_axcut (cons_r _ E' Q) M P := cut (down (rename_process Q swap01))
                                          (reduce_axcut
                                             (rename_axcut_ctx E' swap01)
                                             (rename_message (upM M) swap01)
                                             (rename_process (up P) swap01)).
  + intros; unfold lt_axcut_ctx. simpl. rewrite (rename_axcut_ctx_preserves_length swap01 E').
    apply PeanoNat.Nat.lt_succ_diag_r.
  + intros; unfold lt_axcut_ctx. simpl. rewrite (rename_axcut_ctx_preserves_length swap01 E').
    apply PeanoNat.Nat.lt_succ_diag_r.
Defined.
(* Next Obligation.
  intros; unfold lt_axcut_ctx. simpl. rewrite (rename_axcut_ctx_preserves_length swap01 E').
  apply PeanoNat.Nat.lt_succ_diag_r.
Qed.
Next Obligation.
  intros; unfold lt_axcut_ctx. simpl. rewrite (rename_axcut_ctx_preserves_length swap01 E').
  apply PeanoNat.Nat.lt_succ_diag_r.
Qed. *)

(* renaming distributes over fill_hole *)
Lemma rename_axcut_ctx_over_fill_hole :
  forall {n : nat} (E : axcut_ctx n) M r,
    bijective r ->
    rename_process (fill_hole E M) r
      = fill_hole (rename_axcut_ctx E r) (rename_message M r).
Proof.
  intros.
  generalize dependent M.
  generalize dependent r.
  induction E; intros; auto.
  + simpl. f_equal.
    unfold upM. rewrite <- (proj1 (proj2 ren_up_up_ren_commute)); auto.
    rewrite IHE; auto. apply shift_preserves_bijection; auto.
    intros [|] ?; exfalso; lia.
  + simpl. f_equal.
    unfold upM. rewrite <- (proj1 (proj2 ren_up_up_ren_commute)); auto.
    rewrite IHE; auto. apply shift_preserves_bijection; auto.
    intros [|] ?; exfalso; lia.
Qed.

Fixpoint up_ren_n (n : nat) (r : renaming) : renaming :=
  match n with
  | O    => r
  | S n' => up_ren (up_ren_n n' r)
  end.

Lemma well_formedness_preserved_under_swap01 :
  forall {n : nat} (E : axcut_ctx n),
    well_formed_axcut_ctx n E ->
      forall j,
        well_formed_axcut_ctx (up_ren_n j swap01 n) (rename_axcut_ctx E (up_ren_n j swap01)).
Proof.
  intros.
  generalize dependent j.
  induction H; intros.
  + simpl. econstructor.
  + simpl. econstructor.
  + simpl. econstructor.
    - replace (up_ren (up_ren_n j swap01)) with
      (up_ren_n (S j) swap01) by auto.
      assert (S (up_ren_n j swap01 n) = up_ren_n (S j) swap01 (S n)) by auto.
      rewrite H1. apply nfv_under_renaming; auto.
      clear.
      induction j; simpl.
      * apply shift_preserves_bijection. apply swap01_is_bijective.
      * apply shift_preserves_bijection. auto.
    - specialize IHwell_formed_axcut_ctx with (S j). auto.
  + simpl. econstructor.
    - replace (up_ren (up_ren_n j swap01)) with
      (up_ren_n (S j) swap01) by auto.
      assert (S (up_ren_n j swap01 n) = up_ren_n (S j) swap01 (S n)) by auto.
      rewrite H1. apply nfv_under_renaming; auto.
      clear.
      induction j; simpl.
      * apply shift_preserves_bijection. apply swap01_is_bijective.
      * apply shift_preserves_bijection. auto.
    - specialize IHwell_formed_axcut_ctx with (S j). auto.
Qed.

(* A reduction of an AxCut evaluation context can be simulated in ⊳
  using ≡ and an application of AxCut *)
Lemma equiv_red_axcut_in_reduces_axcut' :
  forall n (E : axcut_ctx 0) P M Q R,
    n = length_axcut_ctx E ->
    well_formed_axcut_ctx 0 E ->
    Q = fill_hole E M ->
    R = reduce_axcut E M P ->
    exists L, (cut Q P) ≡ L /\ L ⊳ R.
Proof.
  intros n. induction n; intros.
  + destruct E; simpl in H; try (exfalso; lia); eexists; split; try apply c_refl.
    - rewrite H1, H2. simpl.
      rewrite reduce_axcut_equation_1. econstructor.
    - rewrite H1, H2. simpl. rewrite reduce_axcut_equation_2. eapply r_struct.
      * apply c_cong_cut. apply c_link. apply c_refl.
      * econstructor.
      * apply c_refl.
  + destruct E; simpl in H; try (exfalso; lia).
    - simpl in H1. rewrite reduce_axcut_equation_3 in H2.
      specialize IHn with (E := rename_axcut_ctx E swap01).
      specialize IHn with (P := rename_process (up P) swap01).
      specialize IHn with (M := rename_message (upM M) swap01).
      specialize IHn with (Q := rename_process (fill_hole E (upM M)) swap01).
      assert (
        exists L,
          (cut (rename_process (fill_hole E (upM M)) swap01) (rename_process (up P) swap01)) ≡ L
          /\
          L ⊳ reduce_axcut (rename_axcut_ctx E swap01) (rename_message (upM M) swap01) (rename_process (up P) swap01)
      ).
      {
        eapply IHn; auto.
        + inversion H. rewrite (rename_axcut_ctx_preserves_length swap01 E). auto.
        + inversion H0; subst.
          apply well_formedness_preserved_under_swap01 with (j := 0) in H6.
          auto.
        + rewrite (rename_axcut_ctx_over_fill_hole); auto. apply swap01_is_bijective.
      }
      destruct H3 as [? [? ?]].
      eexists. split.
      * rewrite H1. eapply c_cut_assoc; auto. inversion H0; auto.
      * rewrite H2. eapply r_struct.
        ** eapply c_trans. apply c_cut_comm. apply c_cong_cut.
           apply H3. apply c_refl.
        ** apply r_cong_cut. apply H4.
        ** apply c_cut_comm.
    - simpl in H1. rewrite reduce_axcut_equation_4 in H2.
      specialize IHn with (E := rename_axcut_ctx E swap01).
      specialize IHn with (P := rename_process (up P) swap01).
      specialize IHn with (M := rename_message (upM M) swap01).
      specialize IHn with (Q := rename_process (fill_hole E (upM M)) swap01).
      assert (
        exists L,
          (cut (rename_process (fill_hole E (upM M)) swap01) (rename_process (up P) swap01)) ≡ L
          /\
          L ⊳ reduce_axcut (rename_axcut_ctx E swap01) (rename_message (upM M) swap01) (rename_process (up P) swap01)
      ).
      {
        eapply IHn; auto.
        + inversion H. rewrite (rename_axcut_ctx_preserves_length swap01 E). auto.
        + inversion H0; subst.
          apply well_formedness_preserved_under_swap01 with (j := 0) in H6.
          auto.
        + rewrite (rename_axcut_ctx_over_fill_hole); auto. apply swap01_is_bijective.
      }
      destruct H3 as [? [? ?]].
      eexists. split.
      * rewrite H1. eapply c_trans.
        ** apply c_cong_cut. apply c_cut_comm. apply c_refl.
        ** eapply c_cut_assoc; auto. inversion H0; auto.
      * rewrite H2. eapply r_struct.
        ** eapply c_trans. apply c_cut_comm. apply c_cong_cut.
           apply H3. apply c_refl.
        ** apply r_cong_cut. apply H4.
        ** apply c_cut_comm.
Qed.

Lemma equiv_red_axcut_in_reduces_axcut :
  forall (E : axcut_ctx 0) P M Q R,
    well_formed_axcut_ctx 0 E ->
    Q = fill_hole E M ->
    R = reduce_axcut E M P ->
    exists L, (cut Q P) ≡ L /\ L ⊳ R.
Proof.
  intros. eapply (equiv_red_axcut_in_reduces_axcut' (length_axcut_ctx E)); eauto.
Qed.
