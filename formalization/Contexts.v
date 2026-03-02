From Stdlib Require Import List.
From Stdlib Require Import Lia.

From FD Require Import Types.

Definition ctx A := list (option A).

(* lookup and insert operations *)
Definition empty_ctx {A} : ctx A := nil.

Fixpoint lookup {A} (k : nat) (Γ : ctx A) : option A :=
  match Γ, k with
  | nil, _ => None
  | t :: _, 0 => t
  | _ :: Γ', S x => lookup x Γ'
  end.

Fixpoint insert_option {A} (k : nat) (e : option A) (Γ : ctx A) : ctx A :=
  match k, Γ with
  | 0, _ => e :: Γ
  | S k', e' :: Γ' => e' :: (insert_option k' e Γ')
  | S k', nil => None :: (insert_option k' e Γ)
  end.

Definition insert {A} (k : nat) (t : A) (Γ : ctx A) : ctx A := 
  insert_option k (Some t) Γ.

Notation "A '.:' Γ" := (insert 0 A Γ) (no associativity, at level 61).

(* context splits *)
Reserved Notation "Γ ≜ Γ1 ∘ Γ2" (no associativity, at level 61).

Inductive split_entry {A} : option A -> option A -> option A -> Prop :=
  | split_none  : split_entry None None None
  | split_left  : forall (v : A), split_entry (Some v) (Some v) None
  | split_right : forall (v : A), split_entry (Some v) None (Some v).

Inductive context_split {A} : ctx A -> ctx A -> ctx A -> Prop :=
  | split_nil  : nil ≜ nil ∘ nil
  | split_cons : forall Γ Γ1 Γ2 e e1 e2,
                  (split_entry e e1 e2) ->
                  Γ ≜ Γ1 ∘ Γ2 ->
                  (e :: Γ) ≜ (e1 :: Γ1) ∘ (e2 :: Γ2)

where
  "Γ '≜' Γ1 '∘' Γ2" := (context_split Γ Γ1 Γ2).

(* context equality is extensional *)
Definition ctx_eq {A} (Γ Δ : ctx A) : Prop :=
  forall n, lookup n Γ = lookup n Δ.

(******************************************************************************)
(* Properties about contexts                                                  *)
(******************************************************************************)
Lemma ctx_comm :
  forall {A} (Γ Γ1 Γ2 : ctx A), Γ ≜ Γ1 ∘ Γ2 -> Γ ≜ Γ2 ∘ Γ1.
Proof.
  intros.
  induction H; econstructor.
  - inversion H; repeat econstructor.
  - assumption.
Qed.

Lemma ctx_assoc :
  forall {A} (Γ Γ1 Γ2 Δ1 Δ2 : ctx A),
    Γ ≜ Γ1 ∘ Γ2 -> Γ1 ≜ Δ1 ∘ Δ2 ->
      exists Δ, Δ ≜ Δ2 ∘ Γ2 /\ Γ ≜ Δ1 ∘ Δ.
Proof.
  intros A.
  intros Γ Γ1. generalize dependent Γ.
  induction Γ1; intros.
  + inversion H; inversion H0; subst; exists nil; split; econstructor.
  + destruct Γ2, Δ1, Δ2, Γ; inversion H0; inversion H; subst.
    destruct (IHΓ1 _ _ _ _ H16 H8) as [Δ [? ?]].
    inversion H4; inversion H12; subst; try discriminate.
    - exists (None :: Δ); split; econstructor; eauto.
    - exists (Some v :: Δ); split; econstructor; eauto.
    - exists (None :: Δ); split; econstructor; eauto; econstructor.
    - inversion H9; subst; exists (Some v :: Δ); split; econstructor; eauto.
Qed.

Lemma lookup_ctx_nil : forall {A} (Γ : ctx A),
  Γ = nil -> forall n, lookup n Γ = None.
Proof.
  intros. induction n; subst; reflexivity.
Qed.

(* Decide in which partition an element of a context split lies *)
Lemma decide_ctx_split_partition :
  forall {A} (Γ Γ1 Γ2 : ctx A) n e,
    Γ ≜ Γ1 ∘ Γ2 -> e = lookup n Γ ->
    (lookup n Γ1 = e /\ lookup n Γ2 = None) \/
    (lookup n Γ1 = None /\ lookup n Γ2 = e).
Proof.
  intros.
  generalize dependent n.
  generalize dependent Γ1.
  generalize dependent Γ2.
  induction Γ; intros; subst.
  + inversion H; subst.
    rewrite (lookup_ctx_nil nil eq_refl).
    auto.
  + inversion H; subst.
    specialize IHΓ with (Γ1 := Γ3) (Γ2 := Γ4).
    destruct n; simpl.
    - inversion H2; auto.
    - inversion H2; auto.
Qed.

Lemma lookup_Sn :
  forall {A} (Δ : ctx A) (n : nat) (a : option A),
    lookup (S n) (a :: Δ) = lookup n Δ.
Proof.
  intros. reflexivity.
Qed.

Lemma firstn_Sn_lookup :
  forall {A} (Δ : ctx A) (n : nat),
    S n <= length Δ -> firstn (S n) Δ = (firstn n Δ) ++ (lookup n Δ :: nil).
Proof.
  intros.
  generalize dependent n.
  induction Δ; intros.
  + inversion H.
  + simpl in H. apply le_S_n in H.
    destruct n.
    - reflexivity.
    - rewrite lookup_Sn.
      specialize IHΔ with (n := n).
      apply IHΔ in H.
      rewrite firstn_cons.
      rewrite firstn_cons.
      rewrite H.
      rewrite app_comm_cons. reflexivity.
Qed.

Lemma ctx_split_distribution :
  forall {A} (Γ Γ1 Γ2 Δ Δ1 Δ2 : ctx A),
    Γ ≜ Γ1 ∘ Γ2 -> Δ ≜ Δ1 ∘ Δ2 -> (Γ ++ Δ) ≜ (Γ1 ++ Δ1) ∘ (Γ2 ++ Δ2).
Proof.
  intros.
  induction H.
  + simpl. assumption.
  + repeat (rewrite <- app_comm_cons).
    inversion H; subst.
    - apply split_cons. apply split_none. assumption.
    - apply split_cons. apply split_left. assumption.
    - apply split_cons. apply split_right. assumption.
Qed.

Lemma ctx_split_preserves_length :
  forall {A} (Γ Γ1 Γ2 : ctx A),
    Γ ≜ Γ1 ∘ Γ2 -> (length Γ = length Γ1) /\ (length Γ = length Γ2).
Proof.
  intros.
  induction H; split; simpl; auto; destruct IHcontext_split; auto.
Qed.

Lemma ctx_lookup_app :
  forall {A} (Γ Δ : ctx A) (n : nat),
    n < length Γ -> lookup n (Γ ++ Δ) = lookup n Γ.
Proof.
  intros.
  generalize dependent n.
  induction Γ; intros.
  + inversion H.
  + destruct n; simpl in *; auto.
    apply IHΓ.
    lia.
Qed.

(* remove n *)
Lemma ctx_lookup_app_length :
  forall {A} (Γ Δ : ctx A) (n : nat),
    lookup (length Γ) (Γ ++ Δ) = lookup 0 Δ.
Proof.
  intros.
  induction Γ; simpl; auto.
Qed.

Lemma ctx_lookup_app_minus :
  forall {A} (Γ Δ : ctx A) (n : nat),
    n >= length Γ -> lookup n (Γ ++ Δ) = lookup (n - length Γ) Δ.
Proof.
  intros.
  generalize dependent n.
  induction Γ; intros.
  + simpl. rewrite PeanoNat.Nat.sub_0_r. reflexivity.
  + simpl. destruct n.
    * inversion H.
    * simpl. apply IHΓ. simpl in H. lia.
Qed.

Lemma ctx_lookup_gt_len :
  forall {A} (Δ : ctx A) (n : nat),
    n >= length Δ -> lookup n Δ = None.
Proof.
  intros.
  generalize dependent Δ.
  induction n; intros.
  + inversion H. apply length_zero_iff_nil in H1; subst.
    reflexivity.
  + inversion H.
    - replace Δ with (Δ ++ nil) at 2.
      rewrite ctx_lookup_app_length; auto.
      apply app_nil_r.
    - destruct Δ; auto; simpl. apply IHn. simpl in H. lia.
Qed.

Lemma ctx_split_lookup_in_partition :
  forall {A} (Γ Γ1 Γ2 : ctx A) n x,
    Γ ≜ Γ1 ∘ Γ2 -> lookup n Γ1 = Some x -> lookup n Γ = Some x.
Proof.
  intros.
  generalize dependent Γ2.
  generalize dependent Γ1.
  generalize dependent Γ.
  induction n; intros.
  - destruct Γ1.
    + inversion H0.
    + simpl in H0; subst.
      inversion H; subst.
      inversion H3; subst.
      reflexivity.
  - destruct Γ1.
    + rewrite lookup_ctx_nil in H0; auto. inversion H0.
    + destruct Γ.
      * inversion H.
      * rewrite lookup_Sn.
        rewrite lookup_Sn in H0.
        destruct Γ2. inversion H.
        specialize IHn with Γ Γ1 Γ2.
        apply IHn; auto.
        inversion H; auto.
Qed.

Lemma ctx_lookup_after_insert :
  forall {A} (Γ : ctx A) n x, lookup n (insert n x Γ) = Some x.
Proof.
  intros.
  generalize dependent Γ.
  induction n; intros; auto.
  destruct Γ; apply IHn.
Qed.

Lemma ctx_lookup_singleton_neq :
  forall {A} (a : A) (n : nat) (i : nat),
    i <> n -> lookup i (insert n a empty_ctx) = None.
Proof.
  intros.
  generalize dependent i.
  induction n; intros.
  + apply PeanoNat.Nat.succ_pred in H. rewrite <- H.
    simpl.
    apply lookup_ctx_nil.
    reflexivity.
  + destruct i.
    - reflexivity.
    - simpl. apply IHn. lia.
Qed.

Lemma ctx_lookup_eq_empty :
  forall {A} (Γ : ctx A), ctx_eq Γ empty_ctx <-> (forall n, lookup n Γ = None).
Proof.
  intros.
  split; intros; unfold ctx_eq in *.
  + rewrite H. apply lookup_ctx_nil. auto.
  + intro n. rewrite H. symmetry. apply lookup_ctx_nil. auto.
Qed.

Lemma ctx_empty_ctx_cons :
  forall {A} (Γ : ctx A), ctx_eq (None :: Γ) empty_ctx <-> ctx_eq Γ empty_ctx.
Proof.
  intros.
  split; intros.
  - intro n.
    unfold ctx_eq in H.
    specialize H with (S n). simpl in H.
    rewrite H. rewrite lookup_ctx_nil; auto.
  - intros [|]; auto. simpl. unfold ctx_eq in H. rewrite H.
    apply lookup_ctx_nil; auto.
Qed.

Lemma ctx_empty_insert_none :
  forall {A} (Γ Δ : ctx A),
    ctx_eq (Γ ++ Δ) empty_ctx <-> ctx_eq (Γ ++ None :: Δ) empty_ctx.
Proof.
  intros.
  induction Γ.
  + split; intros; simpl in *; apply ctx_empty_ctx_cons; auto.
  + split; intros; simpl in *.
    - assert (a = None).
      { unfold ctx_eq in H; specialize H with 0; simpl in H; auto. }
      subst.
      apply (proj1 (ctx_empty_ctx_cons (Γ ++ Δ))) in H.
      apply ctx_empty_ctx_cons.
      apply IHΓ.
      assumption.
    - assert (a = None).
      { unfold ctx_eq in H; specialize H with 0; simpl in H; auto. }
      subst.
      apply (proj1 (ctx_empty_ctx_cons (Γ ++ (None :: Δ)))) in H.
      apply ctx_empty_ctx_cons.
      apply IHΓ.
      assumption.
Qed.

Lemma ctx_lookup_repeat_none :
  forall {A} n l,
    @lookup A n (repeat None l) = None.
Proof.
  intros. generalize dependent n.
  induction l; intros.
  + simpl. apply lookup_ctx_nil. reflexivity.
  + simpl. destruct n; auto.
    simpl. apply IHl.
Qed.

Lemma ctx_split_empty_neutral :
  forall {A} (Γ Γ1 Γ2 : ctx A),
    Γ ≜ Γ1 ∘ Γ2 ->
    ctx_eq Γ1 empty_ctx ->
    Γ = Γ2.
Proof.
  intros.
  induction H; auto.
  inversion H; subst.
  + rewrite IHcontext_split; auto. apply (ctx_empty_insert_none nil).
    assumption.
  + exfalso.
    unfold ctx_eq in H0; specialize H0 with 0; simpl in H0; discriminate.
  + rewrite IHcontext_split; auto. apply (ctx_empty_insert_none nil).
    assumption.
Qed.

Lemma ctx_split_empty_refl :
  forall {A} (Γ Δ : ctx A),
    ctx_eq Δ empty_ctx -> length Δ = length Γ -> Γ ≜ Δ ∘ Γ.
Proof.
  intros. generalize dependent Δ. induction Γ; intros.
  + simpl in H0. apply length_zero_iff_nil in H0; subst. econstructor.
  + simpl in H0. destruct Δ.
    - inversion H0.
    - destruct o.
      * exfalso. unfold ctx_eq in H; specialize H with 0; simpl in H. discriminate.
      * econstructor.
        ** destruct a; econstructor.
        ** apply IHΓ.
           *** apply ctx_empty_ctx_cons. assumption.
           *** simpl in H0. inversion H0. reflexivity.
Qed.

Lemma ctx_split_app_inversion :
  forall {A} (Γ Δ Γ1 Γ2 : ctx A),
    Γ ++ Δ ≜ Γ1 ∘ Γ2 -> exists Γ1' Γ2' Δ1' Δ2',
         Γ1 = Γ1' ++ Δ1'
      /\ Γ2 = Γ2' ++ Δ2'
      /\ Γ ≜ Γ1' ∘ Γ2'
      /\ Δ ≜ Δ1' ∘ Δ2'
      /\ length Γ = length Γ1'
      /\ length Γ = length Γ2'.
Proof.
  intros.
  generalize dependent Γ1.
  generalize dependent Γ2.
  induction Γ.
  + intros. simpl in H. exists nil, nil, Γ1, Γ2.
    try repeat split; auto. econstructor.
  + intros. simpl in H. inversion H; subst.
    pose proof (IHΓ _ _ H5).
    destruct H0 as [Γ1' [Γ2' [Δ1' [Δ2' [? [? [? [? [? ?]]]]]]]]].
    subst.
    exists (e1 :: Γ1'), (e2 :: Γ2'), Δ1', Δ2'.
    try repeat split; auto.
    - econstructor; auto.
    - simpl. rewrite H6; auto.
    - simpl. rewrite H7; auto.
Qed.

Lemma ctx_split_with_empty :
  forall {A} (Γ Γ1 Γ2 : ctx A),
    ctx_eq Γ1 empty_ctx -> Γ ≜ Γ1 ∘ Γ2 -> Γ = Γ2.
Proof.
  intros.
  induction H0; auto.
  inversion H0; subst.
  + f_equal. apply IHcontext_split. apply (proj2 (ctx_empty_insert_none nil _)).
    auto.
  + exfalso.
    unfold ctx_eq in H.
    specialize H with O. simpl in H. discriminate.
  + f_equal. apply IHcontext_split. apply (proj2 (ctx_empty_insert_none nil _)).
    auto.
Qed.

Lemma ctx_eq_single_empty :
  forall {A} (Γ : ctx A) t,
    ctx_eq (Some t :: Γ) (Some t :: empty_ctx) ->
    Γ = repeat None (length Γ).
Proof.
  intros.
  induction Γ; auto.
  assert (a = None).
  { unfold ctx_eq in H; apply (H 1). }
  rewrite H0.
  simpl. f_equal.
  apply IHΓ. intro n. induction n; auto.
  simpl. unfold ctx_eq in H.
  specialize H with (S (S n)).
  simpl in H. rewrite (lookup_ctx_nil empty_ctx); auto.
Qed.
