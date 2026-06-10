From FD Require Import Syntax.
From FD Require Import Reduction.
From FD Require Import FreeVars.
From FD Require Import Renaming.
From FD Require Import FreeVars.
From FD Require Import StructCong.
From FD Require Import Contexts.
From FD Require Import Typing.
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

(******************************************************************************)
(* AxCut Evaluation Contexts                                                  *)
(******************************************************************************)

(* AxCut evaluation context generalize the axcut redex (cut (link 0 M) P)
   to arbitrarily nested link process allowing reduction in the presence of
   cut association. It serves as the primary device for proving confluence.
*)

Inductive axcut_ctx : Type :=
  (* n ↔ ▢ *)
  | nil_l : nat -> axcut_ctx
  (* ▢ ↔ n *)
  | nil_r : nat -> axcut_ctx
  (* cut P E *)
  | cons_l : forall (P : process) (E : axcut_ctx), axcut_ctx
  (* cut E P *)
  | cons_r : forall (E : axcut_ctx) (P : process), axcut_ctx.

(* Well-formedness of evaluation contexts *)
(* The index corresponds to the future in the contexts leaf, i.e.
   we will only allow reduction on zero-indexed contexts.
   Processes of the contexts added via cons must satisfy a condition on
   free variables. This condition ensures that cut association is possible. *)
Inductive well_formed_axcut_ctx : nat -> axcut_ctx -> Prop :=
  | wf_nil_l : forall n, well_formed_axcut_ctx n (nil_l n)
  | wf_nil_r : forall n, well_formed_axcut_ctx n (nil_r n)
  | wf_cons_l : forall n P (E : axcut_ctx),
                  ~ ((S n) ∈ P) ->
                  well_formed_axcut_ctx (S n) E ->
                  well_formed_axcut_ctx n (cons_l P E)
  | wf_cons_r : forall n P (E : axcut_ctx),
                  ~ ((S n) ∈ P) ->
                  well_formed_axcut_ctx (S n) E ->
                  well_formed_axcut_ctx n (cons_r E P).

(* fill_hole E M ≏ E[M] *)
Fixpoint fill_hole (E : axcut_ctx) (M : message) : process :=
  match E with
  | nil_l n => link (future n) M
  | nil_r n => link M (future n)
  | cons_l P E' => cut P (fill_hole E' M)
  | cons_r E' P => cut (fill_hole E' M) P
  end.

(******************************************************************************)
(* Renaming, Up- and down-shifting for AxCut Contexts                         *)
(******************************************************************************)
Fixpoint rename_axcut_ctx (E : axcut_ctx) (r : renaming) : axcut_ctx :=
  match E with
  | nil_l n => nil_l (r n)
  | nil_r n => nil_r (r n)
  | cons_l P E' => cons_l (rename_process P (up_ren r)) (rename_axcut_ctx E' (up_ren r))
  | cons_r E' P => cons_r (rename_axcut_ctx E' (up_ren r)) (rename_process P (up_ren r))
  end.

(* remove parameter from axcut_ctx; instead add nat index to WF *)
Fixpoint lift_ctx (E : axcut_ctx) (k n : nat) : axcut_ctx :=
  match E with
  | nil_l i     => nil_l (relocate i k n)
  | nil_r i     => nil_r (relocate i k n)
  | cons_l P E' => cons_l (lift_process P (S k) n) (lift_ctx E' (S k) n)
  | cons_r E' P => cons_r (lift_ctx E' (S k) n) (lift_process P (S k) n)
  end.

Definition upE E := lift_ctx E 0 1.

Fixpoint down1_ctx (E : axcut_ctx) (k : nat) : axcut_ctx :=
  match E with
  | nil_l i     => nil_l (if (Nat.ltb k i) then (pred i) else i)
  | nil_r i     => nil_r (if (Nat.ltb k i) then (pred i) else i)
  | cons_l P E' => cons_l (down1_process P (S k)) (down1_ctx E' (S k))
  | cons_r E' P => cons_r (down1_ctx E' (S k)) (down1_process P (S k))
  end.

Definition downE E := down1_ctx E 0.

(******************************************************************************)
(* Substitution in Contexts                                                   *)
(******************************************************************************)
Fixpoint subst_ctx (E : axcut_ctx) (σ : substitution) : axcut_ctx :=
  match E with
  | nil_l i     => nil_l i
  | nil_r i     => nil_r i
  | cons_l P E' => cons_l (subst_process P (up_subst σ)) (subst_ctx E' (up_subst σ))
  | cons_r E' P => cons_r (subst_ctx E' (up_subst σ)) (subst_process P (up_subst σ))
  end.

(******************************************************************************)
(* Free Variables in a Context                                                *)
(******************************************************************************)
Inductive occurs_free_ctx : nat -> axcut_ctx -> Prop :=
  | fv_ctx_nil_l : forall n, occurs_free_ctx n (nil_l n)
  | fv_ctx_nil_r : forall n, occurs_free_ctx n (nil_r n)
  | fv_ctx_cons_l1 : forall n P E,
                      (S n) ∈ P ->
                      occurs_free_ctx n (cons_l P E)
  | fv_ctx_cons_l2 : forall n P E,
                      occurs_free_ctx (S n) E ->
                      occurs_free_ctx n (cons_l P E)
  | fv_ctx_cons_r1 : forall n P E,
                      (S n) ∈ P ->
                      occurs_free_ctx n (cons_r E P)
  | fv_ctx_cons_r2 : forall n P E,
                      occurs_free_ctx (S n) E ->
                      occurs_free_ctx n (cons_r E P).

(******************************************************************************)
(* ⇛ for AxCut Contexts *)
(******************************************************************************)
Reserved Notation "E '#⇛' E'" (no associativity, at level 1).

Inductive directed_congruence_ctx : axcut_ctx -> axcut_ctx -> Prop :=
  | edc_nil_l : forall n, (nil_l n) #⇛ (nil_r n)
  | edc_nil_r : forall n, (nil_r n) #⇛ (nil_l n)
  | edc_nil_refl_l : forall n, (nil_l n) #⇛ (nil_l n)
  | edc_nil_refl_r : forall n, (nil_r n) #⇛ (nil_r n)
  | edc_cong_cons_l : forall P P' E E', P ⇛ P' -> E #⇛ E' ->
                       (cons_l P E) #⇛ (cons_l P' E')
  | edc_cong_cons_r : forall P P' E E', P ⇛ P' -> E #⇛ E' ->
                       (cons_r E P) #⇛ (cons_r E' P')
  | edc_comm_l : forall P P' E E', P ⇛ P' -> E #⇛ E' ->
                  (cons_l P E) #⇛ (cons_r E' P')
  | edc_comm_r : forall P P' E E', P ⇛ P' -> E #⇛ E' ->
                  (cons_r E P) #⇛ (cons_l P' E')
  | edc_assoc_rl : forall P P' P'' Q Q' Q'' E E' E'', P ⇛ P' -> Q ⇛ Q' -> E #⇛ E' ->
                    ~ (1 ∈ P) ->
                    P'' = down (rename_process P' swap01) ->
                    E'' = rename_axcut_ctx E' swap01 ->
                    Q'' = rename_process (up Q') swap01 ->
                    (cons_r (cons_l P E) Q) #⇛
                    (cons_l P'' (cons_r E'' Q''))
  | edc_assoc_rr : forall P P' P'' Q Q' Q'' E E' E'', P ⇛ P' -> Q ⇛ Q' -> E #⇛ E' ->
                    ~ (occurs_free_ctx 1 E) ->
                    E'' = downE (rename_axcut_ctx E' swap01) ->
                    P'' = rename_process P' swap01 ->
                    Q'' = rename_process (up Q') swap01 ->
                    (cons_r (cons_r E P) Q) #⇛
                    (cons_r E'' (cut P'' Q''))
  | edc_assoc_lr : forall P P' P'' Q Q' Q'' E E' E'', P ⇛ P' -> Q ⇛ Q' -> E #⇛ E' ->
                    ~ (1 ∈ Q) ->
                    P'' = rename_process (up P') swap01 ->
                    E'' = rename_axcut_ctx E' swap01 ->
                    Q'' = down (rename_process Q' swap01) ->
                    (cons_l P (cons_r E Q)) #⇛
                    (cons_r (cons_l P'' E'') Q'')
  | edc_assoc_ll : forall P P' P'' Q Q' Q'' E E' E'', P ⇛ P' -> Q ⇛ Q' -> E #⇛ E' ->
                    ~ (occurs_free_ctx 1 E) ->
                    P'' = rename_process (up P') swap01 ->
                    Q'' = rename_process Q' swap01 ->
                    E'' = downE (rename_axcut_ctx E' swap01) ->
                    (cons_l P (cons_l Q E)) #⇛
                    (cons_l (cut P'' Q'') E'')
  | edc_assoc_cut_l : forall P P' P'' Q Q' Q'' E E' E'', P ⇛ P' -> Q ⇛ Q' -> E #⇛ E' ->
                        ~ (1 ∈ P) ->
                        P'' = down (rename_process P' swap01) ->
                        Q'' = rename_process Q' swap01 ->
                        E'' = rename_axcut_ctx (upE E') swap01 ->
                        (cons_l (cut P Q) E) #⇛ (cons_l P'' (cons_l Q'' E''))
  | edc_assoc_cut_r : forall P P' P'' Q Q' Q'' E E' E'', P ⇛ P' -> Q ⇛ Q' -> E #⇛ E' ->
                        ~ (1 ∈ Q) ->
                        E'' = rename_axcut_ctx (upE E') swap01 ->
                        P'' = rename_process P' swap01 ->
                        Q'' = down (rename_process Q' swap01) ->
                        (cons_r E (cut P Q)) #⇛ (cons_r (cons_r E'' P'') Q'')
where
  "E '#⇛' E'" := (directed_congruence_ctx E E').

(******************************************************************************)
(* Length of Axcut Contexts                                                   *)
(******************************************************************************)

(* Conceptually, an axcut_ctx is a list, thus, its length is suited as
   an induction measure for many proofs. It is also well-founded, which is
   levarage to define the reduct of an axcut redex.
*)

(* Length of an evaluation context *)
Fixpoint length_axcut_ctx (E : axcut_ctx) : nat :=
  match E with
  | nil_l _ => 0
  | nil_r _ => 0
  | cons_l _ E' => S (length_axcut_ctx E')
  | cons_r E' _ => S (length_axcut_ctx E')
  end.

Lemma rename_axcut_ctx_preserves_length :
  forall (r : renaming) (E : axcut_ctx),
    length_axcut_ctx E = length_axcut_ctx (rename_axcut_ctx E r).
Proof.
  intros. generalize dependent r. induction E; intros; simpl; auto;
  rewrite (IHE (up_ren r)); auto.
Qed.

Lemma lift_ctx_preserves_length :
  forall E j k,
    length_axcut_ctx (lift_ctx E j k) = length_axcut_ctx E.
Proof.
  intro E; induction E; intros; simpl; auto.
Qed.

Lemma down_ctx_preserves_length :
  forall E k,
    length_axcut_ctx (down1_ctx E k) = length_axcut_ctx E.
Proof.
  intro E; induction E; intros; simpl; auto.
Qed.

Definition lt_axcut_ctx (E1 E2 : axcut_ctx) : Prop :=
  (length_axcut_ctx E1) < (length_axcut_ctx E2).

Lemma lt_axcut_ctx_well_founded : well_founded lt_axcut_ctx.
Proof. apply well_founded_ltof. Qed.

Instance lt_axcut_wf : WellFounded lt_axcut_ctx.
Proof. apply lt_axcut_ctx_well_founded. Qed.

(******************************************************************************)
(* n-th upshift of a renaming                                                 *)
(******************************************************************************)
Fixpoint up_ren_n (n : nat) (r : renaming) : renaming :=
  match n with
  | O    => r
  | S n' => up_ren (up_ren_n n' r)
  end.

Lemma up_ren_n_S_up_ren :
  forall r n, up_ren_n n (up_ren r) = up_ren_n (S n) r.
Proof.
  intros.
  induction n; auto.
  simpl. rewrite IHn. simpl. reflexivity.
Qed.

Lemma up_ren_n_preserves_bijection :
  forall r n, bijective r -> bijective (up_ren_n n r).
Proof.
  intros. induction n; simpl; auto.
  apply shift_preserves_bijection; auto.
Qed.

Lemma up_ren_n_additive :
  forall r n k, up_ren_n n (up_ren_n k r) = up_ren_n (n + k) r.
Proof.
  intros.
  induction n; auto.
  simpl. rewrite IHn. reflexivity.
Qed.

Lemma up_ren_n_swap_n :
  forall n, up_ren_n n swap01 n = S n.
Proof.
  induction n; auto. simpl. rewrite IHn; auto.
Qed.

Lemma up_ren_n_swap_Sn :
  forall n, up_ren_n n swap01 (S n) = n.
Proof.
  induction n; auto. simpl. rewrite IHn; auto.
Qed.

Lemma up_ren_n_swap_not_nSn :
  forall n j, n <> j -> S n <> j -> up_ren_n n swap01 j = j.
Proof.
  induction n; intros; simpl.
  + destruct j; try (exfalso; lia); destruct j; try (exfalso; lia).
    auto.
  + destruct j; auto; simpl.
    assert (n <> j) by lia.
    assert (S n <> j) by lia.
    rewrite IHn; auto.
Qed.

Lemma up_ren_n_swap_down_down_Sn :
  (forall P j,
    ~ (S j) ∈ P ->
    down1_process (rename_process P (up_ren_n j swap01)) j
      = down1_process P (S j)) /\
  (forall M j,
    ~ (occurs_free_message (S j) M) ->
    down1_message (rename_message M (up_ren_n j swap01)) j
      = down1_message M (S j)) /\
  (forall s j,
    ~ (occurs_free_statement (S j) s) ->
    down1_statement (rename_statement s (up_ren_n j swap01)) j
      = down1_statement s (S j)).
Proof.
  apply syntax_ind; intros; simpl; auto;
  try replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto;
  try replace (up_ren (up_ren_n (S j) swap01)) with (up_ren_n (S (S j)) swap01) by auto;
  try (rewrite H; try rewrite H0; auto; intro Hfv; try apply H0; try apply H1; free_var_econstructor; eauto).
  destruct (PeanoNat.Nat.eq_dec j n).
  + subst. rewrite up_ren_n_swap_n.
    assert (n < (S n)) by lia. apply PeanoNat.Nat.ltb_lt in H0; rewrite H0; simpl.
    assert (~ (S n) < n) by lia. apply PeanoNat.Nat.ltb_nlt in H1; rewrite H1.
    reflexivity.
  + destruct (PeanoNat.Nat.eq_dec (S j) n).
    - subst. exfalso. apply H; econstructor.
    - rewrite up_ren_n_swap_not_nSn; try lia.
      destruct (Nat.ltb j n) eqn:E.
      * apply PeanoNat.Nat.ltb_lt in E.
        assert (S j < n) by lia. apply PeanoNat.Nat.ltb_lt in H0; rewrite H0. auto.
      * apply PeanoNat.Nat.ltb_nlt in E.
        assert (~ S j < n) by lia. apply PeanoNat.Nat.ltb_nlt in H0; rewrite H0; auto.
Qed.

Lemma up_ren_n_swap_down_down_Sn_ctx :
  forall E j,
    ~ (occurs_free_ctx (S j) E) ->
    down1_ctx (rename_axcut_ctx E (up_ren_n j swap01)) j
      = down1_ctx E (S j).
Proof.
  induction E; intros; simpl.
  + destruct (PeanoNat.Nat.eq_dec j n).
    - subst. rewrite up_ren_n_swap_n.
      assert (n < (S n)) by lia. apply PeanoNat.Nat.ltb_lt in H0; rewrite H0; simpl.
      assert (~ (S n) < n) by lia. apply PeanoNat.Nat.ltb_nlt in H1; rewrite H1.
      reflexivity.
    - destruct (PeanoNat.Nat.eq_dec (S j) n).
      * subst. exfalso. apply H; econstructor.
      * rewrite up_ren_n_swap_not_nSn; try lia.
        destruct (Nat.ltb j n) eqn:E.
        ** apply PeanoNat.Nat.ltb_lt in E.
           assert (S j < n) by lia. apply PeanoNat.Nat.ltb_lt in H0; rewrite H0. auto.
        ** apply PeanoNat.Nat.ltb_nlt in E.
           assert (~ S j < n) by lia. apply PeanoNat.Nat.ltb_nlt in H0; rewrite H0; auto.
  + destruct (PeanoNat.Nat.eq_dec j n).
    - subst. rewrite up_ren_n_swap_n.
      assert (n < (S n)) by lia. apply PeanoNat.Nat.ltb_lt in H0; rewrite H0; simpl.
      assert (~ (S n) < n) by lia. apply PeanoNat.Nat.ltb_nlt in H1; rewrite H1.
      reflexivity.
    - destruct (PeanoNat.Nat.eq_dec (S j) n).
      * subst. exfalso. apply H; econstructor.
      * rewrite up_ren_n_swap_not_nSn; try lia.
        destruct (Nat.ltb j n) eqn:E.
        ** apply PeanoNat.Nat.ltb_lt in E.
           assert (S j < n) by lia. apply PeanoNat.Nat.ltb_lt in H0; rewrite H0. auto.
        ** apply PeanoNat.Nat.ltb_nlt in E.
           assert (~ S j < n) by lia. apply PeanoNat.Nat.ltb_nlt in H0; rewrite H0; auto.
  + replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
    rewrite IHE.
    - rewrite (proj1 up_ren_n_swap_down_down_Sn); auto.
      intro Hfv; apply H. apply fv_ctx_cons_l1; auto.
    - intro Hfv; apply H; apply fv_ctx_cons_l2; auto.
  + replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
    rewrite IHE.
    - rewrite (proj1 up_ren_n_swap_down_down_Sn); auto.
      intro Hfv; apply H. apply fv_ctx_cons_r1; auto.
    - intro Hfv; apply H; apply fv_ctx_cons_r2; auto.
Qed.

Lemma up_ren_n_swap_lift_lift_Sn :
  (forall P j,
    rename_process (lift_process P j 1) (up_ren_n j swap01)
      = lift_process P (S j) 1) /\
  (forall M j,
    rename_message (lift_message M j 1) (up_ren_n j swap01)
      = lift_message M (S j) 1) /\
  (forall s j,
    rename_statement (lift_statement s j 1) (up_ren_n j swap01)
      = lift_statement s (S j) 1).
Proof.
  apply syntax_ind; intros; simpl;
  replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto;
  replace (up_ren (up_ren_n (S j) swap01)) with (up_ren_n (S (S j)) swap01) by auto;
  try rewrite H; try rewrite H0; auto. f_equal.
  unfold relocate.
  destruct (PeanoNat.Nat.eq_dec j n); subst.
  + rewrite PeanoNat.Nat.leb_refl.
    assert (~ (S n) <= n) by lia. apply PeanoNat.Nat.leb_nle in H; rewrite H.
    simpl. rewrite up_ren_n_swap_Sn; auto.
  + destruct (Nat.leb j n) eqn:E.
    - apply PeanoNat.Nat.leb_le in E. assert ((S j) <= n) by lia.
      apply PeanoNat.Nat.leb_le in H; rewrite H; simpl.
      rewrite up_ren_n_swap_not_nSn; lia.
    - apply PeanoNat.Nat.leb_nle in E.
      assert (~ (S j) <= n) by lia. apply PeanoNat.Nat.leb_nle in H; rewrite H.
      rewrite up_ren_n_swap_not_nSn; lia.
Qed.

Lemma up_ren_n_swap_lift_lift_Sn_ctx :
  forall E j,
    rename_axcut_ctx (lift_ctx E j 1) (up_ren_n j swap01)
      = lift_ctx E (S j) 1.
Proof.
  induction E; intros; simpl.
  + f_equal. unfold relocate.
    destruct (Nat.leb j n) eqn:E.
    - apply PeanoNat.Nat.leb_le in E.
      destruct (Nat.leb (S j) n) eqn:E1.
      * apply PeanoNat.Nat.leb_le in E1.
        rewrite up_ren_n_swap_not_nSn; lia.
      * apply PeanoNat.Nat.leb_nle in E1. assert (n = j) by lia; subst.
        rewrite up_ren_n_swap_Sn. reflexivity.
    - apply PeanoNat.Nat.leb_nle in E. assert (~ (S j) <= n) by lia.
      apply PeanoNat.Nat.leb_nle in H; rewrite H.
      rewrite up_ren_n_swap_not_nSn; lia.
  + f_equal. unfold relocate.
    destruct (Nat.leb j n) eqn:E.
    - apply PeanoNat.Nat.leb_le in E.
      destruct (Nat.leb (S j) n) eqn:E1.
      * apply PeanoNat.Nat.leb_le in E1.
        rewrite up_ren_n_swap_not_nSn; lia.
      * apply PeanoNat.Nat.leb_nle in E1. assert (n = j) by lia; subst.
        rewrite up_ren_n_swap_Sn. reflexivity.
    - apply PeanoNat.Nat.leb_nle in E. assert (~ (S j) <= n) by lia.
      apply PeanoNat.Nat.leb_nle in H; rewrite H.
      rewrite up_ren_n_swap_not_nSn; lia.
  + replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
    rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
    rewrite IHE.
    reflexivity.
  + replace (up_ren (up_ren_n j swap01)) with (up_ren_n (S j) swap01) by auto.
    rewrite (proj1 up_ren_n_swap_lift_lift_Sn).
    rewrite IHE.
    reflexivity.
Qed.

Lemma down_at_k_rename_id_after_k_commute_ctx :
  forall E,
    forall k r, bijective r -> (forall j, k <= j -> r j = j) ->
      down1_ctx (rename_axcut_ctx E r) k
        = rename_axcut_ctx (down1_ctx E k) r.
Proof.
  induction E; intros; simpl.
  + destruct (Nat.ltb k n) eqn:E; simpl.
    - apply PeanoNat.Nat.ltb_lt in E.
      assert (Nat.ltb k n = true) by (apply PeanoNat.Nat.ltb_lt in E; auto).
      destruct n; try (exfalso; lia). simpl.
      assert (k <= (S n)) by lia. rewrite (H0 (S n)); auto. simpl.
      rewrite H1. rewrite H0; auto. lia.
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
          repeat rewrite c in H2. auto.
         }
         rewrite H in E1. congruence.
  + destruct (Nat.ltb k n) eqn:E; simpl.
    - apply PeanoNat.Nat.ltb_lt in E.
      assert (Nat.ltb k n = true) by (apply PeanoNat.Nat.ltb_lt in E; auto).
      destruct n; try (exfalso; lia). simpl.
      assert (k <= (S n)) by lia. rewrite (H0 (S n)); auto. simpl.
      rewrite H1. rewrite H0; auto. lia.
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
          repeat rewrite c in H2. auto.
         }
         rewrite H in E1. congruence.
  + f_equal.
    - rewrite (proj1 down_at_k_rename_id_after_k_commute); auto.
      apply shift_preserves_bijection; auto.
      intros; unfold up_ren; destruct j; auto; try rewrite H0; try rewrite H1; try rewrite H2; lia.
    - rewrite IHE; auto.
      apply shift_preserves_bijection; auto.
      intros; unfold up_ren; destruct j; auto; try rewrite H0; try rewrite H1; try rewrite H2; lia.
  + f_equal.
    - rewrite IHE; auto.
      apply shift_preserves_bijection; auto.
      intros; unfold up_ren; destruct j; auto; try rewrite H0; try rewrite H1; try rewrite H2; lia.
    - rewrite (proj1 down_at_k_rename_id_after_k_commute); auto.
      apply shift_preserves_bijection; auto.
      intros; unfold up_ren; destruct j; auto; try rewrite H0; try rewrite H1; try rewrite H2; lia.
Qed.

Lemma lift_at_k_rename_id_after_k_commute_ctx :
  forall E,
    forall k r, bijective r -> (forall j, k <= j -> r j = j) ->
      lift_ctx (rename_axcut_ctx E r) k 1
        = rename_axcut_ctx (lift_ctx E k 1) r.
Proof.
  induction E; intros; simpl.
  + f_equal. unfold relocate.
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
  + f_equal. unfold relocate.
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
  + f_equal.
    - rewrite (proj1 lift_at_k_rename_id_after_k_commute); auto.
      apply shift_preserves_bijection; auto.
      intros; unfold up_ren; destruct j; auto; try rewrite H0; try rewrite H1; try rewrite H2; lia.
    - rewrite IHE; auto.
      apply shift_preserves_bijection; auto.
      intros; unfold up_ren; destruct j; auto; try rewrite H0; try rewrite H1; try rewrite H2; lia.
  + f_equal.
    - rewrite IHE; auto.
      apply shift_preserves_bijection; auto.
      intros; unfold up_ren; destruct j; auto; try rewrite H0; try rewrite H1; try rewrite H2; lia.
    - rewrite (proj1 lift_at_k_rename_id_after_k_commute); auto.
      apply shift_preserves_bijection; auto.
      intros; unfold up_ren; destruct j; auto; try rewrite H0; try rewrite H1; try rewrite H2; lia.
Qed.

(******************************************************************************)
(* Reduct of an AxCut Redex                                                   *)
(******************************************************************************)

(* reduce_axcut computes the reduct of an AxCut, i.e. the process
   cut P E_0[M] (or (cut E_0[M] P)) reduces to (reduce_axcut E M P)
   where E_0 denotes a well-formed context indexed at 0 (well_formed_axcut_ctx 0 E)
*)

Equations? reduce_axcut (E : axcut_ctx) (M : message) (P : process) : process by wf E lt_axcut_ctx :=
  reduce_axcut (nil_l _) M P := subst_process P ((downM M) ⋅ id_subst);
  reduce_axcut (nil_r _) M P := subst_process P ((downM M) ⋅ id_subst);
  reduce_axcut (cons_l Q E') M P := cut (down (rename_process Q swap01))
                                        (reduce_axcut
                                           (rename_axcut_ctx E' swap01)
                                           (rename_message M (up_ren_n (length_axcut_ctx E') swap01))
                                           (rename_process (up P) swap01));
  reduce_axcut (cons_r E' Q) M P := cut (reduce_axcut
                                           (rename_axcut_ctx E' swap01)
                                           (rename_message M (up_ren_n (length_axcut_ctx E') swap01))
                                           (rename_process (up P) swap01))
                                        (down (rename_process Q swap01)).
  + intros; unfold lt_axcut_ctx. simpl. rewrite (rename_axcut_ctx_preserves_length swap01 E').
    apply PeanoNat.Nat.lt_succ_diag_r.
  + intros; unfold lt_axcut_ctx. simpl. rewrite (rename_axcut_ctx_preserves_length swap01 E').
    apply PeanoNat.Nat.lt_succ_diag_r.
Defined.

(******************************************************************************)
(* Properties about AxCut Contexts                                            *)
(******************************************************************************)

(* renaming distributes over fill_hole *)
Lemma rename_axcut_ctx_over_fill_hole :
  forall (E : axcut_ctx) M r,
    bijective r ->
    rename_process (fill_hole E M) r
      = fill_hole (rename_axcut_ctx E r) (rename_message M (up_ren_n (length_axcut_ctx E) r)).
Proof.
  intros.
  generalize dependent M.
  generalize dependent r.
  induction E; intros; auto.
  + simpl. f_equal.
    rewrite IHE.
    - replace (up_ren (up_ren_n (length_axcut_ctx E) r)) with (up_ren_n (S (length_axcut_ctx E)) r) by auto.
      rewrite up_ren_n_S_up_ren; reflexivity.
    - apply shift_preserves_bijection; auto.
  + simpl. f_equal.
    rewrite IHE.
    - rewrite up_ren_n_S_up_ren; reflexivity.
    - apply shift_preserves_bijection; auto.
Qed.

Lemma lift_after_down_ge_commute :
  (forall P,
    forall k1 k2, k1 <= k2 ->
      lift_process (down1_process P k2) k1 1
        = down1_process (lift_process P k1 1) (S k2)) /\
  (forall M,
    forall k1 k2, k1 <= k2 ->
      lift_message (down1_message M k2) k1 1
        = down1_message (lift_message M k1 1) (S k2)) /\
  (forall s,
    forall k1 k2, k1 <= k2 ->
      lift_statement (down1_statement s k2) k1 1
        = down1_statement (lift_statement s k1 1) (S k2)).
Proof.
  apply syntax_ind; intros; simpl; auto;
    try (now (rewrite (H (S k1) (S k2)); try lia; auto));
    try (now (rewrite (H (S k1) (S k2)); try lia; rewrite (H0 (S k1) (S k2)); try lia; auto)).
  + rewrite H; auto. rewrite H0; auto.
  + rewrite (H (S k1) (S k2)); try lia. rewrite (H0 k1 k2); try lia. auto.
  + unfold relocate.
    destruct (Nat.ltb k2 n) eqn:E; simpl.
    - apply PeanoNat.Nat.ltb_lt in E. assert (k1 <= n) by lia.
      apply PeanoNat.Nat.leb_le in H0. rewrite H0. simpl.
      assert ((S k2) < (S n)) by lia. apply PeanoNat.Nat.ltb_lt in H1.
      rewrite H1. unfold relocate.
      assert (k1 <= (Nat.pred n)) by lia. apply PeanoNat.Nat.leb_le in H2.
      rewrite H2. simpl. destruct n; try (exfalso; lia). simpl. auto.
    - unfold relocate. destruct (Nat.leb k1 n) eqn:E'; simpl.
      * apply PeanoNat.Nat.ltb_nlt in E.
        assert (~ ((S k2) < (S n))) by lia. apply PeanoNat.Nat.ltb_nlt in H0.
        rewrite H0. auto.
      * apply PeanoNat.Nat.ltb_nlt in E.
        assert (~ (S k2) < n) by lia. apply PeanoNat.Nat.ltb_nlt in H0.
        rewrite H0. auto.
  + rewrite H; auto.
  + rewrite (H (S (S k1)) (S (S k2))); try lia; auto.
  + rewrite (H k1 k2); try lia; auto.
Qed.

Lemma down_ctx_over_fill_hole :
  forall E M k,
    down1_process (fill_hole E M) k =
      fill_hole (down1_ctx E k) (down1_message M ((length_axcut_ctx E) + k)).
Proof.
  intros.
  generalize dependent M.
  generalize dependent k.
  induction E; intros; simpl.
  + destruct (Nat.ltb k n); auto.
  + destruct (Nat.ltb k n); auto.
  + f_equal.
    replace (S (length_axcut_ctx E + k)) with (length_axcut_ctx E + (S k)) by lia.
    rewrite IHE. reflexivity.
  + f_equal.
    replace (S (length_axcut_ctx E + k)) with (length_axcut_ctx E + (S k)) by lia.
    rewrite IHE. reflexivity.
Qed.

Lemma up_ctx_over_fill_hole :
  forall E M k,
    lift_process (fill_hole E M) k 1 =
      fill_hole (lift_ctx E k 1) (lift_message M (length_axcut_ctx E + k) 1).
Proof.
  intros.
  generalize dependent M.
  generalize dependent k.
  induction E; intros; simpl; auto.
  + f_equal.
    replace (S (length_axcut_ctx E + k)) with (length_axcut_ctx E + (S k)) by lia.
    rewrite IHE. reflexivity.
  + f_equal.
    replace (S (length_axcut_ctx E + k)) with (length_axcut_ctx E + (S k)) by lia.
    rewrite IHE. reflexivity.
Qed.

Lemma down_after_up_idE :
  forall j E,
    down1_ctx (lift_ctx E j 1) j = E.
Proof.
  intros.
  generalize dependent j.
  induction E; intros; simpl.
  + unfold relocate.
    destruct (Nat.leb j n) eqn:E.
    - simpl.
      apply PeanoNat.Nat.leb_le in E; assert (j < (S n)) by lia.
      apply PeanoNat.Nat.ltb_lt in H; rewrite H.
      reflexivity.
    - apply PeanoNat.Nat.leb_nle in E. assert (~ (j < n)) by lia.
      apply PeanoNat.Nat.ltb_nlt in H; rewrite H.
      reflexivity.
  + unfold relocate.
    destruct (Nat.leb j n) eqn:E.
    - simpl.
      apply PeanoNat.Nat.leb_le in E; assert (j < (S n)) by lia.
      apply PeanoNat.Nat.ltb_lt in H; rewrite H.
      reflexivity.
    - apply PeanoNat.Nat.leb_nle in E. assert (~ (j < n)) by lia.
      apply PeanoNat.Nat.ltb_nlt in H; rewrite H.
      reflexivity.
  + rewrite (proj1 down_after_up_id).
    rewrite IHE.
    reflexivity.
  + rewrite (proj1 down_after_up_id).
    rewrite IHE.
    reflexivity.
Qed.

Lemma fv_ctx_fill_hole :
  forall E n M, occurs_free_ctx n E -> n ∈ (fill_hole E M).
Proof.
  intros E. induction E; intros; simpl.
  + inversion H; free_var_econstructor; econstructor.
  + inversion H. apply fv_link_r. econstructor.
  + inversion H; subst.
    - apply fv_cut_l; auto.
    - apply fv_cut_r. apply IHE; auto.
  + inversion H; subst.
    - apply fv_cut_r; auto.
    - apply fv_cut_l. apply IHE; auto.
Qed.

Lemma well_formed_ctx_fv :
  forall E j, well_formed_axcut_ctx j E -> occurs_free_ctx j E.
Proof.
  intros.
  generalize dependent j.
  induction E; intros.
  + inversion H; subst. econstructor.
  + inversion H; subst. econstructor.
  + apply fv_ctx_cons_l2. apply IHE. inversion H; auto.
  + apply fv_ctx_cons_r2. apply IHE. inversion H; auto.
Qed.

Lemma nfv_well_typed_fill_hole :
  forall Γ E M j,
    well_formed_axcut_ctx j E ->
    Γ ⊢ (fill_hole E M) :# ->
    ~ (occurs_free_message (length_axcut_ctx E + j) M).
Proof.
  intros.
  generalize dependent Γ.
  generalize dependent j.
  induction E; intros; simpl.
  + inversion H; subst. simpl in H0.
    inversion H0; subst. intro Hfv.
    destruct ((proj1 (proj2 free_var_in_ctx)) _ _ Hfv _ _ H6).
    assert (occurs_free_message n (future n)) by (econstructor; eauto).
    destruct ((proj1 (proj2 free_var_in_ctx)) _ _ H2 _ _ H5).
    pose proof (ctx_split_lookup_in_partition _ _ _ n _ H3 H4).
    symmetry in H7.
    destruct (decide_ctx_split_partition _ _ _ n _ H3 H7) as [[? ?] | [? ?]]; subst; congruence.
  + inversion H; subst. simpl in H0.
    inversion H0; subst. intro Hfv.
    destruct ((proj1 (proj2 free_var_in_ctx)) _ _ Hfv _ _ H5).
    assert (occurs_free_message n (future n)) by (econstructor; eauto).
    destruct ((proj1 (proj2 free_var_in_ctx)) _ _ H2 _ _ H6).
    pose proof (ctx_split_lookup_in_partition _ _ _ n _ H3 H1).
    symmetry in H7.
    destruct (decide_ctx_split_partition _ _ _ n _ H3 H7) as [[? ?] | [? ?]]; subst; congruence.
  + inversion H; subst.
    inversion H0; subst.
    replace (S (length_axcut_ctx E + j)) with (length_axcut_ctx E + (S j)) by lia.
    eapply IHE; eauto.
  + inversion H; subst.
    inversion H0; subst.
    replace (S (length_axcut_ctx E + j)) with (length_axcut_ctx E + (S j)) by lia.
    eapply IHE; eauto.
Qed.

Lemma nfv_fill_hole :
  forall E M j,
    ~ (j ∈ fill_hole E M) ->
      ~ (occurs_free_ctx j E) /\ ~ (occurs_free_message (length_axcut_ctx E + j) M).
Proof.
  intros.
  generalize dependent j.
  induction E; intros; simpl in *.
  + split; intros Hfv; apply H; free_var_econstructor; eauto.
    inversion Hfv; subst. econstructor.
  + split; intros Hfv; apply H.
    - apply fv_link_r. inversion Hfv. econstructor.
    - apply fv_link_l; auto.
  + split; intros; intro Hfv; apply H.
    - inversion Hfv; subst.
      * apply fv_cut_l. assumption.
      * apply fv_cut_r. eapply fv_ctx_fill_hole; auto.
    - apply fv_cut_r.
      assert (~ (S j) ∈ fill_hole E M).
      { intro Hfv'; apply H; apply fv_cut_r; auto. }
      pose proof (proj2 (IHE _ H0)).
      replace (length_axcut_ctx E + S j) with (S (length_axcut_ctx E + j)) in H1 by lia.
      congruence.
  + split; intros; intro Hfv; apply H.
    - inversion Hfv; subst.
      * apply fv_cut_r. assumption.
      * apply fv_cut_l. eapply fv_ctx_fill_hole; auto.
    - apply fv_cut_r.
      assert (~ (S j) ∈ fill_hole E M).
      { intro Hfv'; apply H; apply fv_cut_l; auto. }
      pose proof (proj2 (IHE _ H0)).
      replace (length_axcut_ctx E + S j) with (S (length_axcut_ctx E + j)) in H1 by lia.
      congruence.
Qed.

(* swap01 preserves well-formedness *)
Lemma well_formedness_preserved_under_swap01 :
  forall (n : nat) (E : axcut_ctx),
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
  forall n (E : axcut_ctx) P M Q R,
    n = length_axcut_ctx E ->
    well_formed_axcut_ctx 0 E ->
    Q = fill_hole E M ->
    R = reduce_axcut E M P ->
    exists L, (cut Q P) ≡ L /\ L ⊳ R.
Proof.
  intros n. induction n; intros.
  + destruct E; simpl in H; try (exfalso; lia); eexists; split; try apply c_refl.
    - rewrite H1, H2. simpl.
      rewrite reduce_axcut_equation_1. inversion H0; subst.
      econstructor.
    - rewrite H1, H2. simpl. rewrite reduce_axcut_equation_2. eapply r_struct.
      * apply c_cong_cut. apply c_link. apply c_refl.
      * inversion H0; subst. econstructor.
      * apply c_refl.
  + destruct E; simpl in H; try (exfalso; lia).
    - simpl in H1. rewrite reduce_axcut_equation_3 in H2.
      rewrite H1.
      assert (
        exists L,
        (cut (rename_process (fill_hole E M) swap01) (rename_process (up P) swap01)) 
          ≡ L /\
        L ⊳
        (reduce_axcut
          (rename_axcut_ctx E swap01)
          (rename_message M (up_ren_n (length_axcut_ctx E) swap01))
          (rename_process (up P) swap01))
      ).
      {
        specialize IHn with (E := rename_axcut_ctx E swap01).
        specialize IHn with (P := rename_process (up P) swap01).
        specialize IHn with (M := rename_message M (up_ren_n (length_axcut_ctx E) swap01)).
        eapply IHn; auto.
        + inversion H. rewrite (rename_axcut_ctx_preserves_length swap01 E). auto.
        + inversion H0; subst.
          apply well_formedness_preserved_under_swap01 with (j := 0) in H7.
          auto.
        + rewrite (rename_axcut_ctx_over_fill_hole); auto.
          apply swap01_is_bijective.
      }
      destruct H3 as [? [? ?]]. eexists; split.
      * rewrite H1. eapply c_cut_assoc; auto. inversion H0; auto.
      * rewrite H2. eapply r_struct.
        ** eapply c_trans. apply c_cut_comm. apply c_cong_cut.
           apply H3. apply c_refl.
        ** apply r_cong_cut. apply H4.
        ** apply c_cut_comm.
    - simpl in H1. rewrite reduce_axcut_equation_4 in H2.
      rewrite H1.
      assert (
        exists L,
        (cut (rename_process (fill_hole E M) swap01) (rename_process (up P) swap01)) 
          ≡ L /\
        L ⊳
        (reduce_axcut
          (rename_axcut_ctx E swap01)
          (rename_message M (up_ren_n (length_axcut_ctx E) swap01))
          (rename_process (up P) swap01))
      ).
      {
        specialize IHn with (E := rename_axcut_ctx E swap01).
        specialize IHn with (P := rename_process (up P) swap01).
        specialize IHn with (M := rename_message M (up_ren_n (length_axcut_ctx E) swap01)).
        eapply IHn; auto.
        + inversion H. rewrite (rename_axcut_ctx_preserves_length swap01 E). auto.
        + inversion H0; subst.
          apply well_formedness_preserved_under_swap01 with (j := 0) in H7.
          auto.
        + rewrite (rename_axcut_ctx_over_fill_hole); auto.
          apply swap01_is_bijective.
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
        ** apply c_refl.
Qed.

Lemma equiv_red_axcut_in_reduces_axcut :
  forall (E : axcut_ctx) P M Q R,
    well_formed_axcut_ctx 0 E ->
    Q = fill_hole E M ->
    R = reduce_axcut E M P ->
    exists L, (cut Q P) ≡ L /\ L ⊳ R.
Proof.
  intros. eapply (equiv_red_axcut_in_reduces_axcut' (length_axcut_ctx E)); eauto.
Qed.

(******************************************************************************)
(* Properties about Contexts and Congruences                                  *)
(******************************************************************************)
Lemma downE_preserves_well_formedness' :
  forall n k E,
    k < n ->
    well_formed_axcut_ctx (S n) E ->
      well_formed_axcut_ctx n (down1_ctx E k).
Proof.
  intros n k E.
  generalize dependent n.
  generalize dependent k.
  induction E; intros; simpl.
  + inversion H0; subst.
    assert (k < S n0) by lia. apply PeanoNat.Nat.ltb_lt in H1.
    rewrite H1. simpl. econstructor.
  + inversion H0; subst.
    assert (k < S n0) by lia. apply PeanoNat.Nat.ltb_lt in H1.
    rewrite H1. simpl. econstructor.
  + inversion H0; subst.
    econstructor.
    - intro Hfv.
      apply n_fv_down_Sn in Hfv; auto. lia.
    - apply IHE; auto. lia.
  + inversion H0; subst.
    econstructor.
    - intro Hfv.
      apply n_fv_down_Sn in Hfv; auto. lia.
    - apply IHE; auto. lia.
Qed.

Lemma downE_preserves_well_formedness_nfv :
  forall n k E,
    k <= n ->
    ~ (occurs_free_ctx k E) ->
    well_formed_axcut_ctx (S n) E ->
      well_formed_axcut_ctx n (down1_ctx E k).
Proof.
  intros n k E.
  generalize dependent n.
  generalize dependent k.
  induction E; intros; simpl.
  + inversion H1; subst.
    assert (k < S n0) by lia. apply PeanoNat.Nat.ltb_lt in H2.
    rewrite H2. simpl. econstructor.
  + inversion H1; subst.
    assert (k < S n0) by lia. apply PeanoNat.Nat.ltb_lt in H2.
    rewrite H2. simpl. econstructor.
  + inversion H1; subst.
    econstructor.
    - intro Hfv.
      apply n_fv_down_Sn' in Hfv; auto. lia.
      intro Hfv'. apply H0. apply fv_ctx_cons_l1. assumption.
    - apply IHE; auto. lia.
      intro Hfv'. apply H0. apply fv_ctx_cons_l2. assumption.
  + inversion H1; subst.
    econstructor.
    - intro Hfv.
      apply n_fv_down_Sn' in Hfv; auto. lia.
      intro Hfv'. apply H0. apply fv_ctx_cons_r1. assumption.
    - apply IHE; auto. lia.
      intro Hfv'. apply H0. apply fv_ctx_cons_r2. assumption.
Qed.

Lemma downE_preserves_well_formedness_nfv2 :
  forall n k E,
    n < k ->
    ~ (occurs_free_ctx k E) ->
    well_formed_axcut_ctx n E ->
      well_formed_axcut_ctx n (down1_ctx E k).
Proof.
  intros n k E.
  generalize dependent n.
  generalize dependent k.
  induction E; intros; simpl.
  + inversion H1; subst.
    assert (k <> n). { destruct (PeanoNat.Nat.eq_dec k n); auto. subst; exfalso; apply H0; econstructor. }
    assert (~ k < n) by lia. apply PeanoNat.Nat.ltb_nlt in H3; rewrite H3.
    econstructor.
  + inversion H1; subst.
    assert (k <> n). { destruct (PeanoNat.Nat.eq_dec k n); auto. subst; exfalso; apply H0; econstructor. }
    assert (~ k < n) by lia. apply PeanoNat.Nat.ltb_nlt in H3; rewrite H3.
    econstructor.
  + inversion H1; subst.
    econstructor.
    - apply nfv_down_lt; auto. lia.
    - apply IHE; auto. lia.
      intro Hfv'. apply H0. apply fv_ctx_cons_l2. assumption.
  + inversion H1; subst.
    econstructor.
    - apply nfv_down_lt; auto. lia.
    - apply IHE; auto. lia.
      intro Hfv'. apply H0. apply fv_ctx_cons_r2. assumption.
Qed.

Corollary downE_preserves_well_formedness :
  forall n E,
    well_formed_axcut_ctx (S (S n)) E -> well_formed_axcut_ctx (S n) (downE E).
Proof. intros. apply downE_preserves_well_formedness'; auto. lia. Qed.

Lemma upE_preserves_well_formedness' :
  forall n k E,
    k <= n ->
      well_formed_axcut_ctx n E ->
        well_formed_axcut_ctx (S n) (lift_ctx E k 1).
Proof.
  intros n k E.
  generalize dependent n.
  generalize dependent k.
  induction E; intros; simpl; unfold relocate.
  + inversion H0; subst. apply PeanoNat.Nat.leb_le in H.
    rewrite H. simpl. econstructor.
  + inversion H0; subst. apply PeanoNat.Nat.leb_le in H.
    rewrite H. simpl. econstructor.
  + inversion H0; subst.
    econstructor.
    - intro Hfv. apply fv_up_Sn2' in Hfv; auto. lia.
    - apply IHE; auto. lia.
  + inversion H0; subst.
    econstructor.
    - intro Hfv. apply fv_up_Sn2' in Hfv; auto. lia.
    - apply IHE; auto. lia.
Qed.

Corollary upE_preserves_well_formedness :
  forall n E,
    well_formed_axcut_ctx n E -> well_formed_axcut_ctx (S n) (upE E).
Proof. intros. apply upE_preserves_well_formedness'; auto. lia. Qed.

Lemma upE_preserves_well_formedness2 :
  forall n k E,
    n < k ->
      well_formed_axcut_ctx n E ->
        well_formed_axcut_ctx n (lift_ctx E k 1).
Proof.
  intros n k E.
  generalize dependent n.
  generalize dependent k.
  induction E; intros; simpl; unfold relocate.
  + inversion H0; subst. assert (~ (k <= n)) by lia.
    apply PeanoNat.Nat.leb_nle in H1. rewrite H1. econstructor.
  + inversion H0; subst. assert (~ (k <= n)) by lia.
    apply PeanoNat.Nat.leb_nle in H1. rewrite H1. econstructor.
  + inversion H0; subst.
    econstructor.
    - intro Hfv. apply nfv_up_lt in Hfv; eauto. lia.
    - apply IHE; auto. lia.
  + inversion H0; subst.
    econstructor.
    - intro Hfv. apply nfv_up_lt in Hfv; eauto. lia.
    - apply IHE; auto. lia.
Qed.

Lemma edc_preserves_well_formedness :
  forall E E' n, E #⇛ E' -> well_formed_axcut_ctx n E ->
    well_formed_axcut_ctx n E'.
Proof.
  intros. generalize dependent n.
  induction H; intros.
  + inversion H0; econstructor.
  + inversion H0; econstructor.
  + auto.
  + auto.
  + inversion H1; subst.
    apply directed_cong_in_struct_cong in H.
    destruct ((proj1 free_vars_decidable) P' (S n)).
    {
      apply (proj1 free_vars_under_struct_cong) with (k := S n) in H.
      exfalso; apply H5. apply H. assumption.
    }
    econstructor; auto.
  + inversion H1; subst.
    apply directed_cong_in_struct_cong in H.
    destruct ((proj1 free_vars_decidable) P' (S n)).
    {
      apply (proj1 free_vars_under_struct_cong) with (k := S n) in H.
      exfalso; apply H5. apply H. assumption.
    }
    econstructor; auto.
  + inversion H1; subst.
    apply directed_cong_in_struct_cong in H.
    destruct ((proj1 free_vars_decidable) P' (S n)).
    {
      apply (proj1 free_vars_under_struct_cong) with (k := S n) in H.
      exfalso; apply H5. apply H. assumption.
    }
    econstructor; auto.
  + inversion H1; subst.
    apply directed_cong_in_struct_cong in H.
    destruct ((proj1 free_vars_decidable) P' (S n)).
    {
      apply (proj1 free_vars_under_struct_cong) with (k := S n) in H.
      exfalso; apply H5. apply H. assumption.
    }
    econstructor; auto.
  + inversion H6; subst. inversion H11; subst.
    econstructor.
    {
      assert ( ~ (S (S n)) ∈ (rename_process P' swap01) ).
      {
        apply directed_cong_in_struct_cong in H.
        pose proof (nfv_under_struct_cong _ _ (S (S n)) H H7).
        apply ((proj1 nfv_under_renaming) _ swap01 (S (S n)) swap01_is_bijective H3).
      }
      intro Hfv. apply n_fv_down_Sn in Hfv.
      congruence. lia.
    }
    econstructor.
    - assert ( ~ (S (S n)) ∈ (up Q') ).
      {
        apply (proj1 directed_cong_invariant_under_upshifting) with (k := 0) in H0.
        assert ( ~ (S (S n)) ∈ (lift_process Q 0 1)).
        {
          intro Hfv. apply fv_up_Sn2 in Hfv. congruence. lia.
        }
        unfold up.
        apply directed_cong_in_struct_cong in H0.
        eapply nfv_under_struct_cong; eauto.
      }
      apply ((proj1 nfv_under_renaming) _ swap01 (S (S n)) swap01_is_bijective H3).
    - pose proof (IHdirected_congruence_ctx (S (S n)) H8).
      replace swap01 with (up_ren_n 0 swap01) by auto.
      replace (S (S n)) with (up_ren_n 0 swap01 (S (S n))) by auto.
      apply (well_formedness_preserved_under_swap01 (S (S n)) _ H3).
  + inversion H6; subst. inversion H11; subst.
    econstructor.
    - intro Hfv. inversion Hfv; subst.
      * apply ((proj1 nfv_under_renaming) _ swap01 (S (S n)) swap01_is_bijective H7).
        simpl.
        pose proof ((proj1 directed_cong_invariant_under_renaming) _ _ H swap01 swap01_is_bijective).
        apply directed_cong_in_struct_cong in H3. apply c_comm in H3.
        apply ((proj1 free_vars_under_struct_cong) _ _ H3 _) in H5. auto.
      * assert ( ~ (S (S n)) ∈ (up Q')).
        {
          apply (proj1 directed_cong_invariant_under_upshifting) with (k := 0) in H0.
          assert ( ~ (S (S n)) ∈ (lift_process Q 0 1)).
          {
            intro Hfv'. apply fv_up_Sn2 in Hfv'. congruence. lia.
          }
          unfold up.
          apply directed_cong_in_struct_cong in H0.
          eapply nfv_under_struct_cong; eauto.
        }
        apply ((proj1 nfv_under_renaming) _ swap01 (S (S n)) swap01_is_bijective H3).
        auto.
    - pose proof (IHdirected_congruence_ctx (S (S n)) H8).
      apply well_formedness_preserved_under_swap01 with (j := 0) in H3.
      simpl in H3.
      apply downE_preserves_well_formedness. auto.
  + inversion H6; subst. inversion H11; subst.
    econstructor.
    {
      assert ( ~ (S (S n)) ∈ (rename_process Q' swap01) ).
      {
        apply directed_cong_in_struct_cong in H0.
        pose proof (nfv_under_struct_cong _ _ (S (S n)) H0 H7).
        apply ((proj1 nfv_under_renaming) _ swap01 (S (S n)) swap01_is_bijective H3).
      }
      intro Hfv. apply n_fv_down_Sn in Hfv.
      congruence. lia.
    }
    econstructor.
    - assert ( ~ (S (S n)) ∈ (up P') ).
      {
        apply (proj1 directed_cong_invariant_under_upshifting) with (k := 0) in H.
        assert ( ~ (S (S n)) ∈ (lift_process P 0 1)).
        {
          intro Hfv. apply fv_up_Sn2 in Hfv. congruence. lia.
        }
        unfold up.
        apply directed_cong_in_struct_cong in H.
        eapply nfv_under_struct_cong; eauto.
      }
      apply ((proj1 nfv_under_renaming) _ swap01 (S (S n)) swap01_is_bijective H3).
    - pose proof (IHdirected_congruence_ctx (S (S n)) H8).
      replace swap01 with (up_ren_n 0 swap01) by auto.
      replace (S (S n)) with (up_ren_n 0 swap01 (S (S n))) by auto.
      apply (well_formedness_preserved_under_swap01 (S (S n)) _ H3).
  + inversion H6; subst. inversion H11; subst.
    econstructor.
    - intro Hfv. inversion Hfv; subst.
      * assert ( ~ (S (S n)) ∈ (up P')).
        {
          apply (proj1 directed_cong_invariant_under_upshifting) with (k := 0) in H.
          assert ( ~ (S (S n)) ∈ (lift_process P 0 1)).
          {
            intro Hfv'. apply fv_up_Sn2 in Hfv'. congruence. lia.
          }
          unfold up.
          apply directed_cong_in_struct_cong in H.
          eapply nfv_under_struct_cong; eauto.
        }
        apply ((proj1 nfv_under_renaming) _ swap01 (S (S n)) swap01_is_bijective H3).
        auto.
      * apply ((proj1 nfv_under_renaming) _ swap01 (S (S n)) swap01_is_bijective H7).
        simpl.
        pose proof ((proj1 directed_cong_invariant_under_renaming) _ _ H0 swap01 swap01_is_bijective).
        apply directed_cong_in_struct_cong in H3. apply c_comm in H3.
        apply ((proj1 free_vars_under_struct_cong) _ _ H3 _) in H5. auto.
    - pose proof (IHdirected_congruence_ctx (S (S n)) H8).
      apply well_formedness_preserved_under_swap01 with (j := 0) in H3.
      simpl in H3.
      apply downE_preserves_well_formedness. auto.
  + inversion H6; subst.
    econstructor.
    - assert ( ~ (S (S n)) ∈ P ).
      { intro Hfv. apply H10. apply fv_cut_l. auto. }
      intro Hfv. apply n_fv_down_Sn in Hfv; try lia.
      apply directed_cong_in_struct_cong in H.
      apply (nfv_under_struct_cong _ _ _ H) in H3.
      apply ((proj1 nfv_under_renaming) _ swap01 _ swap01_is_bijective) in H3.
      simpl in H3. congruence.
    - econstructor.
      * assert ( ~ (S (S n)) ∈ Q ).
        { intro Hfv. apply H10. apply fv_cut_r. auto. }
        apply directed_cong_in_struct_cong in H0.
        apply (nfv_under_struct_cong _ _ _ H0) in H3.
        apply ((proj1 nfv_under_renaming) _ swap01 _ swap01_is_bijective) in H3.
        assumption.
      * pose proof (IHdirected_congruence_ctx (S n) H11).
        assert (well_formed_axcut_ctx (S (S n)) (upE E')).
        { apply upE_preserves_well_formedness; auto. }
        apply well_formedness_preserved_under_swap01 with (j := 0) in H4.
        assumption.
  + inversion H6; subst.
    econstructor.
    - assert ( ~ (S (S n)) ∈ Q ).
      { intro Hfv. apply H10. apply fv_cut_r. auto. }
      intro Hfv. apply n_fv_down_Sn in Hfv; try lia.
      apply directed_cong_in_struct_cong in H0.
      apply (nfv_under_struct_cong _ _ _ H0) in H3.
      apply ((proj1 nfv_under_renaming) _ swap01 _ swap01_is_bijective) in H3.
      simpl in H3. congruence.
    - econstructor.
      * assert ( ~ (S (S n)) ∈ P ).
        { intro Hfv. apply H10. apply fv_cut_l. auto. }
        apply directed_cong_in_struct_cong in H.
        apply (nfv_under_struct_cong _ _ _ H) in H3.
        apply ((proj1 nfv_under_renaming) _ swap01 _ swap01_is_bijective) in H3.
        assumption.
      * pose proof (IHdirected_congruence_ctx (S n) H11).
        assert (well_formed_axcut_ctx (S (S n)) (upE E')).
        { apply upE_preserves_well_formedness; auto. }
        apply well_formedness_preserved_under_swap01 with (j := 0) in H4.
        assumption.
Qed.

(* In general, if E[M] ⇛ P, then there may be swaps and lifts within M
   which result in a (behaviourally) different message.
*)
Lemma fill_hole_congruence :
  forall P P' E M, P = fill_hole E M -> P ⇛ P' ->
    exists E' M', P' = fill_hole E' M' /\ E #⇛ E'.
Proof.
  intros.
  generalize dependent E.
  generalize dependent M.
  induction H0; intros.
  + destruct E; simpl in H1; try congruence; inversion H1; subst.
    - exists (nil_l n), mr2. split.
      * simpl.
        apply directed_cong_in_struct_cong in H.
        apply future_equiv_future1 in H. rewrite H; auto.
      * econstructor.
    - exists (nil_r n), ml2. split.
      * simpl.
        apply directed_cong_in_struct_cong in H0.
        apply future_equiv_future1 in H0. rewrite H0; auto.
      * econstructor.
  + destruct E; simpl in H1; try congruence; inversion H1; subst.
    - exists (nil_r n), mr2. split.
      * simpl.
        apply directed_cong_in_struct_cong in H.
        apply future_equiv_future1 in H. rewrite H; auto.
      * econstructor.
    - exists (nil_l n), ml2. split.
      * simpl.
        apply directed_cong_in_struct_cong in H0.
        apply future_equiv_future1 in H0. rewrite H0; auto.
      * econstructor.
  + destruct E; simpl in H; try congruence; inversion H; subst.
    - specialize IHdirected_congruence2 with M E.
      destruct (IHdirected_congruence2 eq_refl) as [? [? [? ?]]].
      exists (cons_r x P'). exists x0.
      split.
      * simpl. rewrite H0. reflexivity.
      * econstructor; eauto.
    - specialize IHdirected_congruence1 with M E.
      destruct (IHdirected_congruence1 eq_refl) as [? [? [? ?]]].
      exists (cons_l Q' x). exists x0.
      split.
      * simpl. rewrite H0. reflexivity.
      * econstructor; eauto.
  + destruct E; simpl in H3; try congruence.
    - inversion H3; subst.
      clear H3 IHdirected_congruence1 IHdirected_congruence2.
      destruct (IHdirected_congruence3 M E eq_refl) as [E' [M' [? ?]]].
      exists (
        cons_l (down (rename_process P1 swap01))
          (cons_l (rename_process Q1 swap01)
                  (rename_axcut_ctx (upE E') swap01))
      ).
      exists (rename_message (lift_message M' (length_axcut_ctx E') 1)
              (up_ren_n (length_axcut_ctx (upE E')) swap01)).
      split.
      * simpl. f_equal. f_equal.
        rewrite H0.
        unfold up.
        rewrite up_ctx_over_fill_hole. rewrite <- plus_n_O.
        replace (lift_ctx E' 0 1) with (upE E') by auto.
        rewrite (rename_axcut_ctx_over_fill_hole _ _ swap01 swap01_is_bijective).
        reflexivity.
      * eapply edc_assoc_cut_l; eauto.
    - destruct E; simpl in H3; try congruence.
      * inversion H3; subst.
        clear H3 IHdirected_congruence1 IHdirected_congruence3.
        destruct (IHdirected_congruence2 M E eq_refl) as [E' [M' [? ?]]].
        exists (cons_l (down (rename_process P1 swap01))
               (cons_r (rename_axcut_ctx E' swap01)
                       (rename_process (up R1) swap01))).
        exists (rename_message M' (up_ren_n (length_axcut_ctx E') swap01)).
        split.
        {
          simpl. rewrite H0. f_equal. f_equal.
          rewrite (rename_axcut_ctx_over_fill_hole _ _ swap01 swap01_is_bijective).
          reflexivity.
        }
        eapply edc_assoc_rl; eauto.
      * inversion H3; subst.
        clear H3 IHdirected_congruence2 IHdirected_congruence3.
        destruct (IHdirected_congruence1 M E eq_refl) as [E' [M' [? ?]]].
        exists (cons_r (downE (rename_axcut_ctx E' swap01)) (cut (rename_process Q1 swap01) (rename_process (up R1) swap01))).
        exists (
          down1_message
            (rename_message M' (up_ren_n (length_axcut_ctx E') swap01))
            (length_axcut_ctx (rename_axcut_ctx E' swap01))
        ).
        split.
        {
          simpl.
          rewrite H0. f_equal; f_equal.
          rewrite (rename_axcut_ctx_over_fill_hole _ _ swap01 swap01_is_bijective).
          unfold down. rewrite down_ctx_over_fill_hole.
          rewrite <- plus_n_O.
          reflexivity.
        }
        eapply edc_assoc_rr; eauto.
        intro Hfv. apply fv_ctx_fill_hole with (M := M) in Hfv. congruence.
  + destruct E; simpl in H3; try congruence.
    - destruct E; simpl in H3; try congruence.
      * inversion H3; subst.
        clear H3 IHdirected_congruence1 IHdirected_congruence2.
        destruct (IHdirected_congruence3 M E eq_refl) as [E' [M' [? ?]]].
        exists (
          cons_l (cut (rename_process (up P1) swap01)
                      (rename_process Q1 swap01))
                 (downE (rename_axcut_ctx E' swap01))
        ).
        exists (
          down1_message
            (rename_message M' (up_ren_n (length_axcut_ctx E') swap01))
            (length_axcut_ctx (rename_axcut_ctx E' swap01))
        ).
        split.
        {
          simpl. f_equal. f_equal.
          rewrite H0.
          rewrite (rename_axcut_ctx_over_fill_hole E' _ swap01 swap01_is_bijective).
          unfold down. rewrite down_ctx_over_fill_hole. rewrite <- plus_n_O.
          reflexivity.
        }
        eapply edc_assoc_ll; eauto.
        intro Hfv. eapply fv_ctx_fill_hole with (M := M) in Hfv; congruence.
      * inversion H3; subst.
        clear H3 IHdirected_congruence1 IHdirected_congruence3.
        destruct (IHdirected_congruence2 M E eq_refl) as [E' [M' [? ?]]].
        exists (
          cons_r (cons_l (rename_process (up P1) swap01)
                         (rename_axcut_ctx E' swap01))
                 (down (rename_process R1 swap01))
        ).
        exists (rename_message M' (up_ren_n (length_axcut_ctx E') swap01)).
        split.
        {
          simpl. f_equal; f_equal.
          rewrite H0.
          rewrite (rename_axcut_ctx_over_fill_hole E' _ swap01 swap01_is_bijective).
          reflexivity.
        }
        eapply edc_assoc_lr; eauto.
    - inversion H3; subst.
      clear H3 IHdirected_congruence2 IHdirected_congruence3.
      destruct (IHdirected_congruence1 M E eq_refl) as [E' [M' [? ?]]].
      exists (
        cons_r (cons_r (rename_axcut_ctx (upE E') swap01)
                       (rename_process Q1 swap01))
               (down (rename_process R1 swap01))
      ).
      eexists.
      split.
      {
        simpl. f_equal. f_equal.
        rewrite H0.
        unfold up. rewrite up_ctx_over_fill_hole.
        rewrite (rename_axcut_ctx_over_fill_hole (upE E') _ swap01 swap01_is_bijective).
        reflexivity.
      }
      eapply edc_assoc_cut_r; eauto.
  + destruct E; simpl in H; try congruence; inversion H; subst.
    - specialize IHdirected_congruence2 with M E.
      destruct (IHdirected_congruence2 eq_refl) as [? [? [? ?]]].
      exists (cons_l P' x). exists x0.
      split.
      * simpl. rewrite H0. reflexivity.
      * econstructor; eauto.
    - specialize IHdirected_congruence1 with M E.
      destruct (IHdirected_congruence1 eq_refl) as [? [? [? ?]]].
      exists (cons_r x Q'). exists x0.
      split.
      * simpl. rewrite H0. reflexivity.
      * econstructor; eauto.
  + destruct E; simpl in H1; congruence.
  + destruct E; simpl in H; congruence.
Qed.

(******************************************************************************)
(* Properties about Free Variables in Evaluation Contexts                     *)
(******************************************************************************)
Lemma fv_ctx_under_renaming :
  forall E r j, bijective r ->
    (occurs_free_ctx j E) <-> (occurs_free_ctx (r j) (rename_axcut_ctx E r)).
Proof.
  intro E. induction E; intros.
  + split; intros; simpl.
    - inversion H0; subst. econstructor.
    - inversion H0; subst. destruct H.
      assert ( g (r j) = g (r n) ) by auto.
      repeat rewrite c in H; subst. econstructor.
  + split; intros; simpl.
    - inversion H0; subst. econstructor.
    - inversion H0; subst. destruct H.
      assert ( g (r j) = g (r n) ) by auto.
      repeat rewrite c in H; subst. econstructor.
  + split; intros; simpl.
    - inversion H0; subst.
      * apply fv_ctx_cons_l1.
        replace (S (r j)) with ((up_ren r) (S j)) by auto.
        apply fv_under_renaming; auto. apply shift_preserves_bijection; auto.
      * apply fv_ctx_cons_l2.
        replace (S (r j)) with ((up_ren r) (S j)) by auto.
        apply IHE; auto. apply shift_preserves_bijection; auto.
    - inversion H0; subst.
      * apply fv_ctx_cons_l1.
        apply ((proj1 fv_under_renaming) _ (up_ren r) (S j)).
        apply shift_preserves_bijection; auto.
        auto.
      * apply fv_ctx_cons_l2.
        apply (IHE (up_ren r) (S j)). apply shift_preserves_bijection; auto.
        auto.
  + split; intros; simpl.
    - inversion H0; subst.
      * apply fv_ctx_cons_r1.
        replace (S (r j)) with ((up_ren r) (S j)) by auto.
        apply fv_under_renaming; auto. apply shift_preserves_bijection; auto.
      * apply fv_ctx_cons_r2.
        replace (S (r j)) with ((up_ren r) (S j)) by auto.
        apply IHE; auto. apply shift_preserves_bijection; auto.
    - inversion H0; subst.
      * apply fv_ctx_cons_r1.
        apply ((proj1 fv_under_renaming) _ (up_ren r) (S j)).
        apply shift_preserves_bijection; auto.
        auto.
      * apply fv_ctx_cons_r2.
        apply (IHE (up_ren r) (S j)). apply shift_preserves_bijection; auto.
        auto.
Qed.

Lemma nfv_ctx_under_renaming :
  forall E r j, bijective r ->
    ~ (occurs_free_ctx j E) -> ~ (occurs_free_ctx (r j) (rename_axcut_ctx E r)).
Proof.
  repeat split; intros;
  intro Hfv; apply fv_ctx_under_renaming in Hfv; congruence.
Qed.

Corollary nfv_ctx_01_swap :
  forall E, ~ (occurs_free_ctx 1 E) -> ~ (occurs_free_ctx 0 (rename_axcut_ctx E swap01)).
Proof.
  intros. replace 0 with (swap01 1) by reflexivity.
  apply nfv_ctx_under_renaming; auto. apply swap01_is_bijective.
Qed.

Corollary nfv_ctx_10_swap :
  forall E, ~ (occurs_free_ctx 0 E) -> ~ (occurs_free_ctx 1 (rename_axcut_ctx E swap01)).
Proof.
  intros. replace 1 with (swap01 0) by reflexivity.
  apply nfv_ctx_under_renaming; auto. apply swap01_is_bijective.
Qed.

Lemma fv_ctx_down_Sn2 :
  forall E n k, k < n ->
    occurs_free_ctx (S n) E -> occurs_free_ctx n (down1_ctx E k).
Proof.
  intros E; induction E; intros; simpl.
  + inversion H0; subst. assert (k < (S n0)) by lia.
    apply PeanoNat.Nat.ltb_lt in H1; rewrite H1. econstructor.
  + inversion H0; subst. assert (k < (S n0)) by lia.
    apply PeanoNat.Nat.ltb_lt in H1; rewrite H1. econstructor.
  + inversion H0; subst.
    - apply fv_ctx_cons_l1. apply (proj1 n_fv_down_Sn2); auto. lia.
    - apply fv_ctx_cons_l2. apply IHE; auto. lia.
  + inversion H0; subst.
    - apply fv_ctx_cons_r1. apply (proj1 n_fv_down_Sn2); auto. lia.
    - apply fv_ctx_cons_r2. apply IHE; auto. lia.
Qed.

Lemma fv_ctx_down_Sn :
  forall E n k, k < n ->
    occurs_free_ctx n (down1_ctx E k) -> occurs_free_ctx (S n) E.
Proof.
  intros E; induction E; intros; simpl.
  + inversion H0; subst.
    destruct (Nat.ltb k n) eqn:E.
    - destruct n; try (exfalso; lia); econstructor.
    - apply PeanoNat.Nat.ltb_nlt in E; exfalso; lia.
  + inversion H0; subst.
    destruct (Nat.ltb k n) eqn:E.
    - destruct n; try (exfalso; lia); econstructor.
    - apply PeanoNat.Nat.ltb_nlt in E; exfalso; lia.
  + inversion H0; subst.
    - apply fv_ctx_cons_l1. apply (proj1 n_fv_down_Sn) with (k := (S k)); auto; lia.
    - apply fv_ctx_cons_l2; apply IHE with (k := (S k)); auto. lia.
  + inversion H0; subst.
    - apply fv_ctx_cons_r1. apply (proj1 n_fv_down_Sn) with (k := (S k)); auto; lia.
    - apply fv_ctx_cons_r2; apply IHE with (k := (S k)); auto. lia.
Qed.

Lemma fv_ctx_up_Sn :
  forall E n k, k < n ->
    occurs_free_ctx n E -> occurs_free_ctx (S n) (lift_ctx E k 1).
Proof.
  intros E.
  induction E; intros; simpl.
  + inversion H0; subst. unfold relocate.
    assert (k <= n) by lia. apply PeanoNat.Nat.leb_le in H1; rewrite H1.
    econstructor.
  + inversion H0; subst. unfold relocate.
    assert (k <= n) by lia. apply PeanoNat.Nat.leb_le in H1; rewrite H1.
    econstructor.
  + inversion H0; subst.
    - apply fv_ctx_cons_l1.
      apply (proj1 fv_up_Sn); auto. lia.
    - apply fv_ctx_cons_l2. apply IHE; auto. lia.
  + inversion H0; subst.
    - apply fv_ctx_cons_r1.
      apply (proj1 fv_up_Sn); auto. lia.
    - apply fv_ctx_cons_r2. apply IHE; auto. lia.
Qed.

Lemma fv_ctx_up_Sn2 :
  forall E n k, k < n ->
    occurs_free_ctx (S n) (lift_ctx E k 1) -> occurs_free_ctx n E.
Proof.
  intros E; induction E; intros; simpl.
  + inversion H0; subst. unfold relocate in H3.
    destruct (Nat.leb k n) eqn:E.
    - inversion H3; subst; econstructor.
    - apply PeanoNat.Nat.leb_nle in E. exfalso. lia.
  + inversion H0; subst. unfold relocate in H3.
    destruct (Nat.leb k n) eqn:E.
    - inversion H3; subst; econstructor.
    - apply PeanoNat.Nat.leb_nle in E. exfalso. lia.
  + inversion H0; subst.
    - apply fv_ctx_cons_l1. apply (proj1 fv_up_Sn2) with (k := (S k)); auto.
      lia.
    - apply fv_ctx_cons_l2. apply IHE with (k := (S k)); auto. lia.
  + inversion H0; subst.
    - apply fv_ctx_cons_r1. apply (proj1 fv_up_Sn2) with (k := (S k)); auto.
      lia.
    - apply fv_ctx_cons_r2. apply IHE with (k := (S k)); auto. lia.
Qed.

Lemma nfv_lift_nE :
  forall E k n j, k <= j /\ j < k + n -> ~ (occurs_free_ctx j (lift_ctx E k n)).
Proof.
  induction E; intros; simpl; intro Hfv.
  + unfold relocate in Hfv.
    destruct (Nat.leb k n) eqn:E.
    - inversion Hfv; subst. apply PeanoNat.Nat.leb_le in E; lia.
    - inversion Hfv; subst. apply PeanoNat.Nat.leb_nle in E; lia.
  + unfold relocate in Hfv.
    destruct (Nat.leb k n) eqn:E.
    - inversion Hfv; subst. apply PeanoNat.Nat.leb_le in E; lia.
    - inversion Hfv; subst. apply PeanoNat.Nat.leb_nle in E; lia.
  + inversion Hfv; subst.
    - apply nfv_lift_n in H2; auto. lia.
    - apply (IHE (S k) n (S j)); auto. lia.
  + inversion Hfv; subst.
    - apply nfv_lift_n in H2; auto. lia.
    - apply (IHE (S k) n (S j)); auto. lia.
Qed.

Lemma free_vars_ctx_under_directed_cong :
  forall E E', E #⇛ E' -> forall k,
    (occurs_free_ctx k E) <-> (occurs_free_ctx k E').
Proof.
  intros. generalize dependent k.
  induction H; intros.
  + split; intros; inversion H; subst; econstructor.
  + split; intros; inversion H; subst; econstructor.
  + split; intros; inversion H; subst; econstructor.
  + split; intros; inversion H; subst; econstructor.
  + split; intros.
    - inversion H1; subst.
      * apply fv_ctx_cons_l1.
        apply directed_cong_in_struct_cong in H.
        apply ((proj1 free_vars_under_struct_cong) _ _ H); auto.
      * apply fv_ctx_cons_l2.
        apply IHdirected_congruence_ctx; auto.
    - inversion H1; subst.
      * apply fv_ctx_cons_l1.
        apply directed_cong_in_struct_cong in H. apply c_comm in H.
        apply ((proj1 free_vars_under_struct_cong) _ _ H); auto.
      * apply fv_ctx_cons_l2.
        apply IHdirected_congruence_ctx; auto.
  + split; intros.
    - inversion H1; subst.
      * apply fv_ctx_cons_r1.
        apply directed_cong_in_struct_cong in H.
        apply ((proj1 free_vars_under_struct_cong) _ _ H); auto.
      * apply fv_ctx_cons_r2.
        apply IHdirected_congruence_ctx; auto.
    - inversion H1; subst.
      * apply fv_ctx_cons_r1.
        apply directed_cong_in_struct_cong in H. apply c_comm in H.
        apply ((proj1 free_vars_under_struct_cong) _ _ H); auto.
      * apply fv_ctx_cons_r2.
        apply IHdirected_congruence_ctx; auto.
  + split; intros.
    - inversion H1; subst.
      * apply fv_ctx_cons_r1.
        apply directed_cong_in_struct_cong in H.
        apply ((proj1 free_vars_under_struct_cong) _ _ H); auto.
      * apply fv_ctx_cons_r2.
        apply IHdirected_congruence_ctx; auto.
    - inversion H1; subst.
      * apply fv_ctx_cons_l1.
        apply directed_cong_in_struct_cong in H. apply c_comm in H.
        apply ((proj1 free_vars_under_struct_cong) _ _ H); auto.
      * apply fv_ctx_cons_l2.
        apply IHdirected_congruence_ctx; auto.
  + split; intros.
    - inversion H1; subst.
      * apply fv_ctx_cons_l1.
        apply directed_cong_in_struct_cong in H.
        apply ((proj1 free_vars_under_struct_cong) _ _ H); auto.
      * apply fv_ctx_cons_l2.
        apply IHdirected_congruence_ctx; auto.
    - inversion H1; subst.
      * apply fv_ctx_cons_r1.
        apply directed_cong_in_struct_cong in H. apply c_comm in H.
        apply ((proj1 free_vars_under_struct_cong) _ _ H); auto.
      * apply fv_ctx_cons_r2.
        apply IHdirected_congruence_ctx; auto.
  + split; intros.
    - inversion H6; subst.
      * apply fv_ctx_cons_l2. apply fv_ctx_cons_r1.
        replace (S (S k)) with (swap01 (S (S k))) by auto.
        apply fv_under_renaming; try apply swap01_is_bijective.
        unfold up. apply fv_up_Sn; try lia.
        apply directed_cong_in_struct_cong in H0.
        apply ((proj1 free_vars_under_struct_cong) _ _ H0); auto.
      * inversion H9; subst.
        ** apply fv_ctx_cons_l1.
           assert ( (S (S k)) ∈ (rename_process P' swap01) ).
           {
            replace (S (S k)) with (swap01 (S (S k))) by auto.
            apply fv_under_renaming; try apply swap01_is_bijective.
            apply directed_cong_in_struct_cong in H.
            apply ((proj1 free_vars_under_struct_cong) _ _ H); auto.
           }
           apply n_fv_down_Sn2; auto. lia.
        ** apply fv_ctx_cons_l2. apply fv_ctx_cons_r2.
           replace (S (S k)) with (swap01 (S (S k))) by auto.
           apply fv_ctx_under_renaming; try apply swap01_is_bijective.
           apply IHdirected_congruence_ctx; auto.
    - inversion H6; subst.
      * apply fv_ctx_cons_r2. apply fv_ctx_cons_l1.
        apply directed_cong_in_struct_cong in H.
        apply ((proj1 free_vars_under_struct_cong) _ _ H).
        apply ((proj1 fv_under_renaming) _ swap01 (S (S k)) swap01_is_bijective).
        simpl.
        apply (proj1 n_fv_down_Sn) with (k := 0); auto. lia.
      * inversion H9; subst.
        ** apply fv_ctx_cons_r1.
           apply directed_cong_in_struct_cong in H0.
           apply ((proj1 free_vars_under_struct_cong) _ _ H0).
           apply (proj1 fv_up_Sn2) with (k := 0); try lia.
           apply ((proj1 fv_under_renaming) _ swap01 _ swap01_is_bijective).
           auto.
        ** apply fv_ctx_cons_r2. apply fv_ctx_cons_l2.
           apply IHdirected_congruence_ctx.
           apply (fv_ctx_under_renaming _ swap01 _ swap01_is_bijective); auto.
  + split; intros.
    - inversion H6; subst.
      * apply fv_ctx_cons_r1. apply fv_cut_r.
        replace (S (S k)) with (swap01 (S (S k))) by auto.
        apply fv_under_renaming; try apply swap01_is_bijective.
        unfold up. apply fv_up_Sn; try lia.
        apply directed_cong_in_struct_cong in H0.
        apply ((proj1 free_vars_under_struct_cong) _ _ H0); auto.
      * inversion H9; subst.
        ** apply fv_ctx_cons_r1. apply fv_cut_l.
           assert ( (S (S k)) ∈ (rename_process P' swap01) ).
           {
            replace (S (S k)) with (swap01 (S (S k))) by auto.
            apply fv_under_renaming; try apply swap01_is_bijective.
            apply directed_cong_in_struct_cong in H.
            apply ((proj1 free_vars_under_struct_cong) _ _ H); auto.
           }
           auto.
        ** apply fv_ctx_cons_r2.
           unfold downE.
           assert ( occurs_free_ctx (S (S k)) (rename_axcut_ctx E' swap01) ).
           {
            replace (S (S k)) with (swap01 (S (S k))) by auto.
            apply fv_ctx_under_renaming; try apply swap01_is_bijective.
            apply IHdirected_congruence_ctx; auto.
           }
           apply fv_ctx_down_Sn2; auto. lia.
    - inversion H6; subst.
      * inversion H9; subst.
        ** apply fv_ctx_cons_r2. apply fv_ctx_cons_r1.
           apply directed_cong_in_struct_cong in H.
           apply ((proj1 free_vars_under_struct_cong) _ _ H).
           apply ((proj1 fv_under_renaming) _ swap01 _ swap01_is_bijective).
           auto.
        ** apply fv_ctx_cons_r1.
           apply directed_cong_in_struct_cong in H0.
           apply ((proj1 free_vars_under_struct_cong) _ _ H0).
           apply (proj1 fv_up_Sn2) with (k := 0); try lia.
           apply ((proj1 fv_under_renaming) _ swap01 _ swap01_is_bijective).
           auto.
      * apply fv_ctx_cons_r2. apply fv_ctx_cons_r2.
        apply IHdirected_congruence_ctx.
        apply (fv_ctx_under_renaming _ swap01 _ swap01_is_bijective). simpl.
        apply fv_ctx_down_Sn with (k := 0); auto. lia.
  + split; intros.
    - inversion H6; subst.
      * apply fv_ctx_cons_r2. apply fv_ctx_cons_l1.
        replace (S (S k)) with (swap01 (S (S k))) by auto.
        apply fv_under_renaming; try apply swap01_is_bijective.
        unfold up. apply fv_up_Sn; try lia.
        apply directed_cong_in_struct_cong in H.
        apply ((proj1 free_vars_under_struct_cong) _ _ H); auto.
      * inversion H9; subst.
        ** apply fv_ctx_cons_r1.
           assert ( (S (S k)) ∈ (rename_process Q' swap01) ).
           {
            replace (S (S k)) with (swap01 (S (S k))) by auto.
            apply fv_under_renaming; try apply swap01_is_bijective.
            apply directed_cong_in_struct_cong in H0.
            apply ((proj1 free_vars_under_struct_cong) _ _ H0); auto.
           }
           apply n_fv_down_Sn2; auto. lia.
        ** apply fv_ctx_cons_r2. apply fv_ctx_cons_l2.
           replace (S (S k)) with (swap01 (S (S k))) by auto.
           apply fv_ctx_under_renaming; try apply swap01_is_bijective.
           apply IHdirected_congruence_ctx; auto.
    - inversion H6; subst.
      * apply fv_ctx_cons_l2. apply fv_ctx_cons_r1.
        apply directed_cong_in_struct_cong in H0.
        apply ((proj1 free_vars_under_struct_cong) _ _ H0).
        apply ((proj1 fv_under_renaming) _ swap01 (S (S k)) swap01_is_bijective).
        simpl.
        apply (proj1 n_fv_down_Sn) with (k := 0); auto. lia.
      * inversion H9; subst.
        ** apply fv_ctx_cons_l1.
           apply directed_cong_in_struct_cong in H.
           apply ((proj1 free_vars_under_struct_cong) _ _ H).
           apply (proj1 fv_up_Sn2) with (k := 0); try lia.
           apply ((proj1 fv_under_renaming) _ swap01 _ swap01_is_bijective).
           auto.
        ** apply fv_ctx_cons_l2. apply fv_ctx_cons_r2.
           apply IHdirected_congruence_ctx.
           apply (fv_ctx_under_renaming _ swap01 _ swap01_is_bijective); auto.
  + split; intros.
    - inversion H6; subst.
      * apply fv_ctx_cons_l1. apply fv_cut_l.
        replace (S (S k)) with (swap01 (S (S k))) by auto.
        apply fv_under_renaming; try apply swap01_is_bijective.
        unfold up. apply fv_up_Sn; try lia.
        apply directed_cong_in_struct_cong in H.
        apply ((proj1 free_vars_under_struct_cong) _ _ H); auto.
      * inversion H9; subst.
        ** apply fv_ctx_cons_l1. apply fv_cut_r.
           assert ( (S (S k)) ∈ (rename_process Q' swap01) ).
           {
            replace (S (S k)) with (swap01 (S (S k))) by auto.
            apply fv_under_renaming; try apply swap01_is_bijective.
            apply directed_cong_in_struct_cong in H0.
            apply ((proj1 free_vars_under_struct_cong) _ _ H0); auto.
           }
           auto.
        ** apply fv_ctx_cons_l2.
           unfold downE.
           assert ( occurs_free_ctx (S (S k)) (rename_axcut_ctx E' swap01) ).
           {
            replace (S (S k)) with (swap01 (S (S k))) by auto.
            apply fv_ctx_under_renaming; try apply swap01_is_bijective.
            apply IHdirected_congruence_ctx; auto.
           }
           apply fv_ctx_down_Sn2; auto. lia.
    - inversion H6; subst.
      * inversion H9; subst.
        ** apply fv_ctx_cons_l1.
           apply directed_cong_in_struct_cong in H.
           apply ((proj1 free_vars_under_struct_cong) _ _ H).
           apply (proj1 fv_up_Sn2) with (k := 0); try lia.
           apply ((proj1 fv_under_renaming) _ swap01 _ swap01_is_bijective).
           auto.
        ** apply fv_ctx_cons_l2. apply fv_ctx_cons_l1.
           apply directed_cong_in_struct_cong in H0.
           apply ((proj1 free_vars_under_struct_cong) _ _ H0).
           apply ((proj1 fv_under_renaming) _ swap01 _ swap01_is_bijective).
           auto.
      * apply fv_ctx_cons_l2. apply fv_ctx_cons_l2.
        apply IHdirected_congruence_ctx.
        apply (fv_ctx_under_renaming _ swap01 _ swap01_is_bijective). simpl.
        apply fv_ctx_down_Sn with (k := 0); auto. lia.
  + split; intros.
    - inversion H6; subst.
      * inversion H9; subst.
        ** apply fv_ctx_cons_l1.
           assert ( (S (S k)) ∈ (rename_process P' swap01) ).
           {
            replace (S (S k)) with (swap01 (S (S k))) by auto.
            apply fv_under_renaming; try apply swap01_is_bijective.
            apply directed_cong_in_struct_cong in H.
            apply ((proj1 free_vars_under_struct_cong) _ _ H); auto.
           }
           apply n_fv_down_Sn2; auto. lia.
        ** apply fv_ctx_cons_l2. apply fv_ctx_cons_l1.
           replace (S (S k)) with (swap01 (S (S k))) by auto.
           apply fv_under_renaming; try apply swap01_is_bijective.
           apply directed_cong_in_struct_cong in H0.
           apply ((proj1 free_vars_under_struct_cong) _ _ H0); auto.
      * apply fv_ctx_cons_l2. apply fv_ctx_cons_l2.
        replace (S (S k)) with (swap01 (S (S k))) by auto.
        apply fv_ctx_under_renaming; try apply swap01_is_bijective.
        unfold upE. apply fv_ctx_up_Sn; try lia.
        apply IHdirected_congruence_ctx; auto.
    - inversion H6; subst.
      * apply fv_ctx_cons_l1. apply fv_cut_l.
        apply directed_cong_in_struct_cong in H.
        apply ((proj1 free_vars_under_struct_cong) _ _ H).
        apply ((proj1 fv_under_renaming) _ swap01 _ swap01_is_bijective); simpl.
        apply (proj1 n_fv_down_Sn) with (k := 0); auto. lia.
      * inversion H9; subst.
        ** apply fv_ctx_cons_l1. apply fv_cut_r.
           apply directed_cong_in_struct_cong in H0.
           apply ((proj1 free_vars_under_struct_cong) _ _ H0).
           apply ((proj1 fv_under_renaming) _ swap01 _ swap01_is_bijective).
           auto.
        ** apply fv_ctx_cons_l2.
           apply IHdirected_congruence_ctx.
           apply fv_ctx_up_Sn2 with (k := 0); try lia.
           apply (fv_ctx_under_renaming _ swap01 _ swap01_is_bijective); auto.
  + split; intros.
    - inversion H6; subst.
      * inversion H9; subst.
        ** apply fv_ctx_cons_r2. apply fv_ctx_cons_r1.
           assert ( (S (S k)) ∈ (rename_process P' swap01) ).
           {
            replace (S (S k)) with (swap01 (S (S k))) by auto.
            apply fv_under_renaming; try apply swap01_is_bijective.
            apply directed_cong_in_struct_cong in H.
            apply ((proj1 free_vars_under_struct_cong) _ _ H); auto.
           }
           auto.
        ** apply fv_ctx_cons_r1.
           assert ( (S (S k)) ∈ (rename_process Q' swap01) ).
           {
            replace (S (S k)) with (swap01 (S (S k))) by auto.
            apply fv_under_renaming; try apply swap01_is_bijective.
            apply directed_cong_in_struct_cong in H0.
            apply ((proj1 free_vars_under_struct_cong) _ _ H0); auto.
           }
           apply n_fv_down_Sn2; auto. lia.
      * apply fv_ctx_cons_r2. apply fv_ctx_cons_r2.
        replace (S (S k)) with (swap01 (S (S k))) by auto.
        apply fv_ctx_under_renaming; try apply swap01_is_bijective.
        unfold upE. apply fv_ctx_up_Sn; try lia.
        apply IHdirected_congruence_ctx; auto.
    - inversion H6; subst.
      * apply fv_ctx_cons_r1. apply fv_cut_r.
        apply directed_cong_in_struct_cong in H0.
        apply ((proj1 free_vars_under_struct_cong) _ _ H0).
        apply ((proj1 fv_under_renaming) _ swap01 _ swap01_is_bijective); simpl.
        apply (proj1 n_fv_down_Sn) with (k := 0); auto. lia.
      * inversion H9; subst.
        ** apply fv_ctx_cons_r1. apply fv_cut_l.
           apply directed_cong_in_struct_cong in H.
           apply ((proj1 free_vars_under_struct_cong) _ _ H).
           apply ((proj1 fv_under_renaming) _ swap01 _ swap01_is_bijective).
           auto.
        ** apply fv_ctx_cons_r2.
           apply IHdirected_congruence_ctx.
           apply fv_ctx_up_Sn2 with (k := 0); try lia.
           apply (fv_ctx_under_renaming _ swap01 _ swap01_is_bijective); auto.
Qed.

Lemma rename_axcut_ctx_compose :
  forall E (f g c : renaming),
    (forall x, Basics.compose f g x = c x) ->
      rename_axcut_ctx (rename_axcut_ctx E g) f = rename_axcut_ctx E c.
Proof.
  intro E. induction E; intros; simpl.
  + rewrite <- H. auto.
  + rewrite <- H. auto.
  + f_equal.
    - rewrite (proj1 renamings_compose) with (c := (up_ren c)); auto.
      apply up_shift_compose; auto.
    - rewrite (IHE (up_ren f) (up_ren g) (up_ren c)); auto.
      apply up_shift_compose; auto.
  + f_equal.
    - rewrite (IHE (up_ren f) (up_ren g) (up_ren c)); auto.
      apply up_shift_compose; auto.
    - rewrite (proj1 renamings_compose) with (c := (up_ren c)); auto.
      apply up_shift_compose; auto.
Qed.

Lemma up_ren_swap_involutive :
  forall n x,
    id x = Basics.compose (up_ren_n n swap01) (up_ren_n n swap01) x.
Proof.
  intros; unfold Basics.compose.
  destruct (PeanoNat.Nat.eq_dec n x).
  + subst. rewrite up_ren_n_swap_n. rewrite up_ren_n_swap_Sn. reflexivity.
  + destruct (PeanoNat.Nat.eq_dec (S n) x); subst.
    - rewrite up_ren_n_swap_Sn. rewrite up_ren_n_swap_n. reflexivity.
    - rewrite (up_ren_n_swap_not_nSn _ x); try lia.
      rewrite up_ren_n_swap_not_nSn; try lia.
      reflexivity.
Qed.

Lemma rename_axcut_ctx_id :
  forall E r, (forall x, r x = x) ->
    rename_axcut_ctx E r = E.
Proof.
  intros E; induction E; intros; simpl; try rewrite H; eauto.
  + rewrite (proj1 rename_id); try rewrite IHE; auto; intros [|]; auto; simpl; rewrite H; auto.
  + rewrite (proj1 rename_id); try rewrite IHE; auto; intros [|]; auto; simpl; rewrite H; auto.
Qed.

Lemma up_ren_swap_swap_idE :
  forall n E,
    rename_axcut_ctx (rename_axcut_ctx E (up_ren_n n swap01)) (up_ren_n n swap01) = E.
Proof.
  intros.
  rewrite rename_axcut_ctx_compose with (c := id).
  + rewrite rename_axcut_ctx_id; auto.
  + intros. erewrite up_ren_swap_involutive; eauto.
Qed.

Corollary swap_swap_idE :
  forall E, rename_axcut_ctx (rename_axcut_ctx E swap01) swap01 = E.
Proof.
  intros. replace swap01 with (up_ren_n 0 swap01) by reflexivity.
  apply up_ren_swap_swap_idE.
Qed.

Lemma up_ren_swap_swap_idP :
  forall n P,
    rename_process (rename_process P (up_ren_n n swap01)) (up_ren_n n swap01) = P.
Proof.
  intros.
  rewrite (proj1 renamings_compose) with (c := id).
  + rewrite (proj1 rename_id); auto.
  + intros. erewrite up_ren_swap_involutive; eauto.
Qed.

Lemma up_ren_swap_swap_idM :
  forall n M,
    rename_message (rename_message M (up_ren_n n swap01)) (up_ren_n n swap01) = M.
Proof.
  intros.
  rewrite (proj1 (proj2 renamings_compose)) with (c := id).
  + rewrite (proj1 (proj2 rename_id)); auto.
  + intros. erewrite up_ren_swap_involutive; eauto.
Qed.

Lemma axcut_ctx_down_ren_up_ren_commute :
  forall E, forall r k,
    bijective r -> (forall j, j < k -> r j = j) ->
    ~ (occurs_free_ctx k E) ->
    down1_ctx (rename_axcut_ctx E (up_ren r)) k =
    rename_axcut_ctx (down1_ctx E k) r.
Proof.
  intros E; induction E; intros; simpl;
  try assert (forall j : nat, j < S k -> up_ren r j = j) by 
    (intros; unfold up_ren; destruct j; auto; try rewrite H0; try rewrite H1; try rewrite H2; lia).
  + assert (k <> n). { intro Hneq. subst. apply H1. econstructor. }
    destruct (Nat.ltb k n) eqn:E.
    - apply PeanoNat.Nat.ltb_lt in E. destruct n; try (exfalso; lia).
      simpl.
      destruct (Nat.ltb k (S (r n))) eqn:E1; auto.
      exfalso. apply PeanoNat.Nat.ltb_nlt in E1.
      assert (r n < k) by lia.
      assert (r (r n) = (r n)) by (rewrite H0; auto).
      destruct H.
      assert (g (r (r n)) = g (r n)). { rewrite H5; auto. }
      repeat rewrite c in H. lia.
    - apply PeanoNat.Nat.ltb_nlt in E.
      assert (n < k) by lia.
      assert (n < S k) by lia.
      rewrite (H2 _ H5). apply PeanoNat.Nat.ltb_nlt in E. rewrite E.
      simpl. rewrite (H0 _ H4). reflexivity.
  + assert (k <> n). { intro Hneq. subst. apply H1. econstructor. }
    destruct (Nat.ltb k n) eqn:E.
    - apply PeanoNat.Nat.ltb_lt in E. destruct n; try (exfalso; lia).
      simpl.
      destruct (Nat.ltb k (S (r n))) eqn:E1; auto.
      exfalso. apply PeanoNat.Nat.ltb_nlt in E1.
      assert (r n < k) by lia.
      assert (r (r n) = (r n)) by (rewrite H0; auto).
      destruct H.
      assert (g (r (r n)) = g (r n)). { rewrite H5; auto. }
      repeat rewrite c in H. lia.
    - apply PeanoNat.Nat.ltb_nlt in E.
      assert (n < k) by lia.
      assert (n < S k) by lia.
      rewrite (H2 _ H5). apply PeanoNat.Nat.ltb_nlt in E. rewrite E.
      simpl. rewrite (H0 _ H4). reflexivity.
  + rewrite (proj1 down_ren_up_ren_commute);
    try rewrite IHE; auto;
    try (apply shift_preserves_bijection; auto).
    - intro Hfv. apply H1. apply fv_ctx_cons_l2; auto.
    - intro Hfv. apply H1. apply fv_ctx_cons_l1; auto.
  + rewrite (proj1 down_ren_up_ren_commute);
    try rewrite IHE; auto;
    try (apply shift_preserves_bijection; auto).
    - intro Hfv. apply H1. apply fv_ctx_cons_r2; auto.
    - intro Hfv. apply H1. apply fv_ctx_cons_r1; auto.
Qed.

Lemma axcut_ctx_ren_up_up_ren_commute :
  forall E, forall r k,
    bijective r -> (forall j, j < k -> r j = j) ->
    rename_axcut_ctx (lift_ctx E k 1) (up_ren r)
      = lift_ctx (rename_axcut_ctx E r) k 1.
Proof.
  intros E; induction E; intros; simpl;
  assert (bijective (up_ren r)) by (apply shift_preserves_bijection; auto);
  try assert (forall j : nat, j < S k -> up_ren r j = j) by 
    (intros; unfold up_ren; destruct j; auto; try rewrite H0; try rewrite H1; try rewrite H2; lia).
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
  + rewrite (proj1 ren_up_up_ren_commute); try rewrite IHE; auto.
  + rewrite (proj1 ren_up_up_ren_commute); try rewrite IHE; auto.
Qed.

(******************************************************************************)
(* Invariances                                                                *)
(******************************************************************************)
Lemma edc_invariant_under_renaming :
  forall E E' r, bijective r -> E #⇛ E' ->
    (rename_axcut_ctx E r) #⇛ (rename_axcut_ctx E' r).
Proof.
  intros. generalize dependent r.
  induction H0; intros; simpl; try (now econstructor).
  + apply edc_cong_cons_l.
    - apply directed_cong_invariant_under_renaming; auto.
      apply shift_preserves_bijection; auto.
    - apply IHdirected_congruence_ctx; apply shift_preserves_bijection; auto.
  + econstructor.
    - apply directed_cong_invariant_under_renaming; auto.
      apply shift_preserves_bijection; auto.
    - apply IHdirected_congruence_ctx; apply shift_preserves_bijection; auto.
  + econstructor.
    - apply directed_cong_invariant_under_renaming; auto.
      apply shift_preserves_bijection; auto.
    - apply IHdirected_congruence_ctx; apply shift_preserves_bijection; auto.
  + econstructor.
    - apply directed_cong_invariant_under_renaming; auto.
      apply shift_preserves_bijection; auto.
    - apply IHdirected_congruence_ctx; apply shift_preserves_bijection; auto.
  + eapply edc_assoc_rl.
    - apply directed_cong_invariant_under_renaming; eauto.
      repeat apply shift_preserves_bijection; auto.
    - apply directed_cong_invariant_under_renaming; eauto.
      apply shift_preserves_bijection; auto.
    - apply IHdirected_congruence_ctx.
      repeat apply shift_preserves_bijection; auto.
    - replace 1 with ((up_ren (up_ren r)) 1) by auto.
      apply ((proj1 nfv_under_renaming) _ (up_ren (up_ren r))); auto.
      repeat apply shift_preserves_bijection; auto.
    - rewrite H3.
      assert (
        (rename_process (down (rename_process P' swap01)) (up_ren r)) =
        (down (rename_process (rename_process P' swap01) (up_ren (up_ren r))))
      ).
      {
        unfold down. rewrite <- (proj1 down_ren_up_ren_commute); auto.
        + apply shift_preserves_bijection; auto.
        + intros [|[|]] ?; exfalso; lia.
        + apply nfv_01_swap; auto. intro Hfv. apply directed_cong_in_struct_cong in H.
          apply c_comm in H. apply ((proj1 free_vars_under_struct_cong) _ _ H) in Hfv; congruence.
      }
      assert (
        rename_process (rename_process P' (up_ren (up_ren r))) swap01 =
        rename_process (rename_process P' swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H8. auto.
    - rewrite H4.
      assert (
        rename_axcut_ctx (rename_axcut_ctx E' (up_ren (up_ren r))) swap01 =
        rename_axcut_ctx (rename_axcut_ctx E' swap01) (up_ren (up_ren r))
      ).
      {
        rewrite (rename_axcut_ctx_compose _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite (rename_axcut_ctx_compose _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      auto.
    - rewrite H5.
      assert (
        (rename_process (rename_process (up Q') swap01) (up_ren (up_ren r))) =
        (rename_process (rename_process (up Q') (up_ren (up_ren r))) swap01)
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      assert (
        up (rename_process Q' (up_ren r)) =
        rename_process (up Q') (up_ren (up_ren r))
      ).
      {
        unfold up.
        rewrite (proj1 ren_up_up_ren_commute); auto.
        + apply shift_preserves_bijection; auto.
        + intros. exfalso; lia.
      }
      rewrite H7; rewrite H8; auto.
  + eapply edc_assoc_rr.
    - apply directed_cong_invariant_under_renaming; eauto.
      repeat apply shift_preserves_bijection; auto.
    - apply directed_cong_invariant_under_renaming; eauto.
      apply shift_preserves_bijection; auto.
    - apply IHdirected_congruence_ctx; auto.
      repeat apply shift_preserves_bijection; auto.
    - replace 1 with ((up_ren (up_ren r)) 1) by auto.
      apply nfv_ctx_under_renaming; auto.
      repeat apply shift_preserves_bijection; auto.
    - rewrite H3.
      assert (
        rename_axcut_ctx (rename_axcut_ctx E' (up_ren (up_ren r))) swap01 =
        rename_axcut_ctx (rename_axcut_ctx E' swap01) (up_ren (up_ren r))
      ).
      {
        rewrite (rename_axcut_ctx_compose _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite (rename_axcut_ctx_compose _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H7.
      assert (
        (rename_axcut_ctx (downE (rename_axcut_ctx E' swap01)) (up_ren r)) =
        (downE (rename_axcut_ctx (rename_axcut_ctx E' swap01) (up_ren (up_ren r))))
      ).
      {
        unfold downE. rewrite <- axcut_ctx_down_ren_up_ren_commute; auto.
        + apply shift_preserves_bijection; auto.
        + intros [|[|]] ?; exfalso; lia.
        + apply nfv_ctx_01_swap; auto. intro Hfv.
          apply (free_vars_ctx_under_directed_cong _ _ H1) in Hfv; congruence.
      }
      rewrite H8. auto.
    - rewrite H4.
      assert (
        rename_process (rename_process P' (up_ren (up_ren r))) swap01 =
        rename_process (rename_process P' swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      auto.
    - rewrite H5.
      assert (
        (rename_process (rename_process (up Q') swap01) (up_ren (up_ren r))) =
        (rename_process (rename_process (up Q') (up_ren (up_ren r))) swap01)
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      assert (
        up (rename_process Q' (up_ren r)) =
        rename_process (up Q') (up_ren (up_ren r))
      ).
      {
        unfold up.
        rewrite (proj1 ren_up_up_ren_commute); auto.
        + apply shift_preserves_bijection; auto.
        + intros. exfalso; lia.
      }
      rewrite H7; rewrite H8; auto.
  + eapply edc_assoc_lr.
    - apply directed_cong_invariant_under_renaming; eauto.
      apply shift_preserves_bijection; auto.
    - apply directed_cong_invariant_under_renaming; eauto.
      repeat apply shift_preserves_bijection; auto.
    - apply IHdirected_congruence_ctx; repeat apply shift_preserves_bijection; auto.
    - replace 1 with ((up_ren (up_ren r)) 1) by auto.
      apply nfv_under_renaming; auto. repeat apply shift_preserves_bijection.
      auto.
    - rewrite H3.
      assert (
        rename_process (rename_process (up P') (up_ren (up_ren r))) swap01 =
        rename_process (rename_process (up P') swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite <- H7.
      assert (
        up (rename_process P' (up_ren r)) =
        rename_process (up P') (up_ren (up_ren r))
      ).
      {
        unfold up.
        rewrite (proj1 ren_up_up_ren_commute); auto.
        + apply shift_preserves_bijection; auto.
        + intros. exfalso; lia.
      }
      rewrite H8. auto.
    - rewrite H4.
      assert (
        rename_axcut_ctx (rename_axcut_ctx E' (up_ren (up_ren r))) swap01 =
        rename_axcut_ctx (rename_axcut_ctx E' swap01) (up_ren (up_ren r))
      ).
      {
        rewrite (rename_axcut_ctx_compose _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite (rename_axcut_ctx_compose _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      auto.
    - rewrite H5.
      assert (
        rename_process (rename_process Q' (up_ren (up_ren r))) swap01 =
        rename_process (rename_process Q' swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H7.
      assert (
        (rename_process (down (rename_process Q' swap01)) (up_ren r)) =
        (down (rename_process (rename_process Q' swap01) (up_ren (up_ren r))))
      ).
      {
        unfold down. rewrite <- (proj1 down_ren_up_ren_commute); auto.
        + apply shift_preserves_bijection; auto.
        + intros [|[|]] ?; exfalso; lia.
        + apply nfv_01_swap; auto. intro Hfv. apply directed_cong_in_struct_cong in H0.
          apply c_comm in H0. apply ((proj1 free_vars_under_struct_cong) _ _ H0) in Hfv; congruence.
      }
      rewrite H8. auto.
  + eapply edc_assoc_ll.
    - apply directed_cong_invariant_under_renaming; eauto.
      apply shift_preserves_bijection; auto.
    - apply directed_cong_invariant_under_renaming; eauto.
      repeat apply shift_preserves_bijection; auto.
    - apply IHdirected_congruence_ctx.
      repeat apply shift_preserves_bijection; auto.
    - replace 1 with ((up_ren (up_ren r)) 1) by auto.
      apply nfv_ctx_under_renaming; auto.
      repeat apply shift_preserves_bijection; auto.
    - rewrite H3.
      assert (
        rename_process (rename_process (up P') (up_ren (up_ren r))) swap01 =
        rename_process (rename_process (up P') swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite <- H7.
      assert (
        up (rename_process P' (up_ren r)) =
        rename_process (up P') (up_ren (up_ren r))
      ).
      {
        unfold up.
        rewrite (proj1 ren_up_up_ren_commute); auto.
        + apply shift_preserves_bijection; auto.
        + intros. exfalso; lia.
      }
      rewrite H8. auto.
    - rewrite H4.
      assert (
        rename_process (rename_process Q' (up_ren (up_ren r))) swap01 =
        rename_process (rename_process Q' swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      auto.
    - rewrite H5.
      assert (
        rename_axcut_ctx (rename_axcut_ctx E' (up_ren (up_ren r))) swap01 =
        rename_axcut_ctx (rename_axcut_ctx E' swap01) (up_ren (up_ren r))
      ).
      {
        rewrite (rename_axcut_ctx_compose _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite (rename_axcut_ctx_compose _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H7.
      assert (
        (rename_axcut_ctx (downE (rename_axcut_ctx E' swap01)) (up_ren r)) =
        (downE (rename_axcut_ctx (rename_axcut_ctx E' swap01) (up_ren (up_ren r))))
      ).
      {
        unfold downE. rewrite <- axcut_ctx_down_ren_up_ren_commute; auto.
        + apply shift_preserves_bijection; auto.
        + intros [|[|]] ?; exfalso; lia.
        + apply nfv_ctx_01_swap; auto. intro Hfv.
          apply (free_vars_ctx_under_directed_cong _ _ H1) in Hfv; congruence.
      }
      rewrite H8. auto.
  + eapply edc_assoc_cut_l.
    - apply directed_cong_invariant_under_renaming; eauto.
      repeat apply shift_preserves_bijection; auto.
    - apply directed_cong_invariant_under_renaming; eauto.
      repeat apply shift_preserves_bijection; auto.
    - apply IHdirected_congruence_ctx.
      repeat apply shift_preserves_bijection; auto.
    - replace 1 with ((up_ren (up_ren r)) 1) by auto.
      apply nfv_under_renaming; auto. repeat apply shift_preserves_bijection.
      auto.
    - rewrite H3.
      assert (
        rename_process (rename_process P' (up_ren (up_ren r))) swap01 =
        rename_process (rename_process P' swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H7.
      assert (
        (rename_process (down (rename_process P' swap01)) (up_ren r)) =
        (down (rename_process (rename_process P' swap01) (up_ren (up_ren r))))
      ).
      {
        unfold down. rewrite <- (proj1 down_ren_up_ren_commute); auto.
        + apply shift_preserves_bijection; auto.
        + intros [|[|]] ?; exfalso; lia.
        + apply nfv_01_swap; auto. intro Hfv. apply directed_cong_in_struct_cong in H.
          apply c_comm in H. apply ((proj1 free_vars_under_struct_cong) _ _ H) in Hfv; congruence.
      }
      rewrite H8. auto.
    - rewrite H4.
      assert (
        rename_process (rename_process Q' (up_ren (up_ren r))) swap01 =
        rename_process (rename_process Q' swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      auto.
    - rewrite H5.
      assert (
        (rename_axcut_ctx (rename_axcut_ctx (upE E') swap01) (up_ren (up_ren r))) =
        (rename_axcut_ctx (rename_axcut_ctx (upE E') (up_ren (up_ren r))) swap01)
      ).
      {
        rewrite (rename_axcut_ctx_compose _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite (rename_axcut_ctx_compose _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      assert (
        upE (rename_axcut_ctx E' (up_ren r)) =
        rename_axcut_ctx (upE E') (up_ren (up_ren r))
      ).
      {
        unfold upE.
        rewrite axcut_ctx_ren_up_up_ren_commute; auto.
        + apply shift_preserves_bijection; auto.
        + intros. exfalso; lia.
      }
      rewrite H7; rewrite H8; auto.
  + eapply edc_assoc_cut_r.
    - apply directed_cong_invariant_under_renaming; eauto.
      repeat apply shift_preserves_bijection; auto.
    - apply directed_cong_invariant_under_renaming; eauto.
      repeat apply shift_preserves_bijection; auto.
    - apply IHdirected_congruence_ctx.
      repeat apply shift_preserves_bijection; auto.
    - replace 1 with ((up_ren (up_ren r)) 1) by auto.
      apply nfv_under_renaming; auto. repeat apply shift_preserves_bijection.
      auto.
    - rewrite H3.
      assert (
        (rename_axcut_ctx (rename_axcut_ctx (upE E') swap01) (up_ren (up_ren r))) =
        (rename_axcut_ctx (rename_axcut_ctx (upE E') (up_ren (up_ren r))) swap01)
      ).
      {
        rewrite (rename_axcut_ctx_compose _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite (rename_axcut_ctx_compose _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      assert (
        upE (rename_axcut_ctx E' (up_ren r)) =
        rename_axcut_ctx (upE E') (up_ren (up_ren r))
      ).
      {
        unfold upE.
        rewrite axcut_ctx_ren_up_up_ren_commute; auto.
        + apply shift_preserves_bijection; auto.
        + intros. exfalso; lia.
      }
      rewrite H7; rewrite H8; auto.
    - rewrite H4.
      assert (
        rename_process (rename_process P' (up_ren (up_ren r))) swap01 =
        rename_process (rename_process P' swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      auto.
    - rewrite H5.
      assert (
        rename_process (rename_process Q' (up_ren (up_ren r))) swap01 =
        rename_process (rename_process Q' swap01) (up_ren (up_ren r))
      ).
      {
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        rewrite ((proj1 renamings_compose) _ _ _ (Basics.compose swap01 (up_ren (up_ren r)))).
        reflexivity. all: intros[|[|]]; auto.
      }
      rewrite H7.
      assert (
        (rename_process (down (rename_process Q' swap01)) (up_ren r)) =
        (down (rename_process (rename_process Q' swap01) (up_ren (up_ren r))))
      ).
      {
        unfold down. rewrite <- (proj1 down_ren_up_ren_commute); auto.
        + apply shift_preserves_bijection; auto.
        + intros [|[|]] ?; exfalso; lia.
        + apply nfv_01_swap; auto. intro Hfv. apply directed_cong_in_struct_cong in H0.
          apply c_comm in H0. apply ((proj1 free_vars_under_struct_cong) _ _ H0) in Hfv; congruence.
      }
      rewrite H8. auto.
Qed.

Lemma reduce_axcut_invariant_under_congruent_substituent' :
  forall n E M P P',
    n = length_axcut_ctx E ->
    well_formed_axcut_ctx 0 E ->
    P ⇛ P' ->
    (reduce_axcut E M P) ⇛ (reduce_axcut E M P').
Proof.
  induction n; intros; destruct E; simpl in H; try congruence.
  + repeat rewrite reduce_axcut_equation_1.
    apply directed_cong_invariant_under_substitution; auto.
    intro. apply dc_cong_reflM.
  + repeat rewrite reduce_axcut_equation_2.
    apply directed_cong_invariant_under_substitution; auto.
    intro. apply dc_cong_reflM.
  + repeat rewrite reduce_axcut_equation_3.
    apply dc_cong_cut.
    - apply directed_cong_invariant_under_downshifting.
      apply directed_cong_invariant_under_renaming.
      apply directed_cong_reflexive.
      apply swap01_is_bijective.
      inversion H0; apply nfv_01_swap; auto.
    - apply IHn.
      rewrite <- rename_axcut_ctx_preserves_length; inversion H; auto.
      replace 0 with (swap01 1); replace swap01 with (up_ren_n 0 swap01); auto;
      apply well_formedness_preserved_under_swap01; inversion H0; auto.
      apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
      apply directed_cong_invariant_under_upshifting; auto.
  + repeat rewrite reduce_axcut_equation_4.
    apply dc_cong_cut.
    - apply IHn.
      rewrite <- rename_axcut_ctx_preserves_length; inversion H; auto.
      replace 0 with (swap01 1); replace swap01 with (up_ren_n 0 swap01); auto;
      apply well_formedness_preserved_under_swap01; inversion H0; auto.
      apply directed_cong_invariant_under_renaming; try apply swap01_is_bijective.
      apply directed_cong_invariant_under_upshifting; auto.
    - apply directed_cong_invariant_under_downshifting.
      apply directed_cong_invariant_under_renaming.
      apply directed_cong_reflexive.
      apply swap01_is_bijective.
      inversion H0; apply nfv_01_swap; auto.
Qed.

Lemma reduce_axcut_invariant_under_congruent_substituent :
  forall E M P P',
    P ⇛ P' ->
    well_formed_axcut_ctx 0 E ->
    (reduce_axcut E M P) ⇛ (reduce_axcut E M P').
Proof.
  intros. eapply reduce_axcut_invariant_under_congruent_substituent'; auto.
Qed.
