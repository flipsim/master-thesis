From Stdlib Require Import ssreflect.
From Stdlib Require Import List.

(******************************************************************************)
(* Syntax                                                                     *)
(******************************************************************************)
Inductive process : Type :=
  | link : message -> message -> process
  | cut : process -> process -> process
  | seq : process -> statement -> process
  | stop : process

with message :=
  | future : nat -> message
  | prefix : statement -> message

with statement :=
  | choose_left : process -> statement
  | choose_right : process -> statement
  | offer_choice : process -> process -> statement
  | send : process -> process -> statement
  | receive : process -> statement
  | close : statement
  | wait : process -> statement.

(* Proper (mutually inductive) induction principle *)
Scheme process_rec_ind   := Induction for process Sort Prop
  with message_rec_ind   := Induction for message Sort Prop
  with statement_rec_ind := Induction for statement Sort Prop.
Combined Scheme syntax_ind from process_rec_ind, message_rec_ind, statement_rec_ind.

(******************************************************************************)
(* Lifting                                                                    *)
(******************************************************************************)
Definition relocate (i k n : nat) : nat :=
  match (Nat.leb k i) with
  | true => n + i
  | false => i
  end.

Fixpoint lift_process (p : process) (k n : nat) : process :=
  match p with
  | link ml mr => link (lift_message ml k n) (lift_message mr k n)
  | cut pl pr => cut (lift_process pl (S k) n) (lift_process pr (S k) n)
  | seq p s => seq (lift_process p (S k) n) (lift_statement s k n)
  | stop => stop
  end
with lift_message (m : message) (k n : nat) : message :=
  match m with
  | future i => future (relocate i k n)
  | prefix s => prefix (lift_statement s k n)
  end
with lift_statement (s : statement) (k n : nat) : statement :=
  match s with
  | choose_left p => choose_left (lift_process p (S k) n)
  | choose_right p => choose_right (lift_process p (S k) n)
  | offer_choice p1 p2 => offer_choice (lift_process p1 (S k) n) (lift_process p2 (S k) n)
  | send p1 p2 => send (lift_process p1 (S k) n) (lift_process p2 (S k) n)
  | receive p => receive (lift_process p (S (S k)) n)
  | close => close
  | wait p => wait (lift_process p k n)
  end.

(* shift up by n *)
Definition shift m n := lift_message m 0 n.

(* shift up by one *)
Definition up  p := lift_process p 0 1.
Definition upM m := lift_message m 0 1.
Definition upS s := lift_statement s 0 1.

(******************************************************************************)
(* Downshifting                                                               *)
(******************************************************************************)
(* The semantics of Free Deduction lift subterms that are nested more deeply
   outwards which requires free variables to be downshifted accordingly *)
(* down_* downshift all free variables that are *greater* than k by one *)
Fixpoint down1_process (p : process) (k : nat) : process :=
  match p with
  | link ml mr => link (down1_message ml k) (down1_message mr k)
  | cut pl pr => cut (down1_process pl (S k)) (down1_process pr (S k))
  | seq p s => seq (down1_process p (S k)) (down1_statement s k)
  | stop => stop
  end
with down1_message (m : message) (k : nat) : message :=
  match m with
  | future i => if (Nat.ltb k i) then future (pred i) else future i
  | prefix s => prefix (down1_statement s k)
  end
with down1_statement (s : statement) (k : nat) : statement :=
  match s with
  | choose_left p => choose_left (down1_process p (S k))
  | choose_right p => choose_right (down1_process p (S k))
  | offer_choice p1 p2 => offer_choice (down1_process p1 (S k)) (down1_process p2 (S k))
  | send p1 p2 => send (down1_process p1 (S k)) (down1_process p2 (S k))
  | receive p => receive (down1_process p (S (S k)))
  | close => close
  | wait p => wait (down1_process p k)
  end.

(* Shorthands for downshifting *)
Definition down  p := down1_process p 0.
Definition downM m := down1_message m 0.
Definition downS s := down1_statement s 0.

(******************************************************************************)
(* Free occurences                                                            *)
(******************************************************************************)
Inductive occurs_free_process : nat -> process -> Prop :=
  | fv_link_l : forall ml mr n,
                  occurs_free_message n ml ->
                  occurs_free_process n (link ml mr)
  | fv_link_r : forall ml mr n,
                  occurs_free_message n mr ->
                  occurs_free_process n (link ml mr)
  | fv_cut_l : forall pl pr n,
                  occurs_free_process (S n) pl ->
                  occurs_free_process n (cut pl pr)
  | fv_cut_r : forall pl pr n,
                  occurs_free_process (S n) pr ->
                  occurs_free_process n (cut pl pr)
  | fv_seq_l : forall p s n,
                  occurs_free_process (S n) p ->
                  occurs_free_process n (seq p s)
  | fv_seq_r : forall p s n,
                  occurs_free_statement n s ->
                  occurs_free_process n (seq p s)
with occurs_free_message : nat -> message -> Prop :=
  | fv_future : forall n,
                  occurs_free_message n (future n)
  | fv_prefix : forall s n,
                  occurs_free_statement n s ->
                  occurs_free_message n (prefix s)
with occurs_free_statement : nat -> statement -> Prop :=
  | fv_choose_left : forall p n,
                      occurs_free_process (S n) p ->
                      occurs_free_statement n (choose_left p)
  | fv_choose_right : forall p n,
                      occurs_free_process (S n) p ->
                      occurs_free_statement n (choose_right p)
  | fv_choice_l : forall pl pr n,
                    occurs_free_process (S n) pl ->
                    occurs_free_statement n (offer_choice pl pr)
  | fv_choice_r : forall pl pr n,
                    occurs_free_process (S n) pr ->
                    occurs_free_statement n (offer_choice pl pr)
  | fv_send_l : forall pl pr n,
                  occurs_free_process (S n) pl ->
                  occurs_free_statement n (send pl pr)
  | fv_send_r : forall pl pr n,
                  occurs_free_process (S n) pr ->
                  occurs_free_statement n (send pl pr)
  | fv_receive : forall p n,
                  occurs_free_process (S (S n)) p ->
                  occurs_free_statement n (receive p)
  | fv_wait : forall p n,
                occurs_free_process n p ->
                occurs_free_statement n (wait p).

Notation "n '∈' P" := (occurs_free_process n P) (no associativity, at level 60).

Scheme fv_process_ind   := Induction for occurs_free_process Sort Prop
  with fv_message_ind   := Induction for occurs_free_message Sort Prop
  with fv_statement_ind := Induction for occurs_free_statement Sort Prop.
Combined Scheme fv_ind from fv_process_ind, fv_message_ind, fv_statement_ind.

(******************************************************************************)
(* Parallel Substitution                                                      *)
(******************************************************************************)
Definition substitution := nat -> message.

Definition scons (x : message) (f : substitution) : substitution :=
  fun (i : nat) =>
    match i with
    | O   => x
    | S j => f j
    end.

Notation "M ⋅ τ" := (scons M τ) (at level 60).

Definition up_subst (τ : substitution) : substitution :=
  (future 0) ⋅ (fun i => upM (τ i)).

Definition id_subst : substitution := fun i => future i.

Fixpoint subst_process (p : process) (σ : substitution) : process :=
  match p with
  | link ml mr => link (subst_message ml σ) (subst_message mr σ)
  | cut pl pr => cut (subst_process pl (up_subst σ)) (subst_process pr (up_subst σ))
  | seq p s => seq (subst_process p (up_subst σ)) (subst_statement s σ)
  | stop => stop
  end
with subst_message (m : message) (σ : substitution) : message :=
  match m with
  | future i => σ i
  | prefix s => prefix (subst_statement s σ)
  end
with subst_statement (s : statement) (σ : substitution) : statement :=
  match s with
  | choose_left p => choose_left (subst_process p (up_subst σ))
  | choose_right p => choose_right (subst_process p (up_subst σ))
  | offer_choice p1 p2 => offer_choice (subst_process p1 (up_subst σ)) (subst_process p2 (up_subst σ))
  | send p1 p2 => send (subst_process p1 (up_subst σ)) (subst_process p2 (up_subst σ))
  | receive p => receive (subst_process p (up_subst (up_subst σ)))
  | close => close
  | wait p => wait (subst_process p σ)
  end.

(******************************************************************************)
(* Single Substitution                                                        *)
(******************************************************************************)
(* Definition insert_future (m : message) (i k : nat) : message :=
  match Nat.compare k i with
  | Lt => future (pred i)
  | Eq => shift m k
  | Gt => future i
  end.

Fixpoint subst_process (p : process) (m : message) (k : nat) : process :=
  match p with
  | link ml mr => link (subst_message ml m k) (subst_message mr m k)
  | cut pl pr => cut (subst_process pl (upM m) (S k)) (subst_process pr (upM m) (S k))
  | seq p s => seq (subst_process p (upM m) (S k)) (subst_statement s m k)
  | stop => stop
  end
with subst_message (m' m : message) (k : nat) : message :=
  match m' with
  | future i => insert_future m i k
  | prefix s => prefix (subst_statement s m k)
  end
with subst_statement (s : statement) (m : message) (k : nat) : statement :=
  match s with
  | choose_left p => choose_left (subst_process p (upM m) (S k))
  | choose_right p => choose_right (subst_process p (upM m) (S k))
  | offer_choice p1 p2 => offer_choice (subst_process p1 (upM m) (S k)) (subst_process p2 (upM m) (S k))
  | send p1 p2 => send (subst_process p1 (upM m) (S k)) (subst_process p2 (upM m) (S k))
  | receive p => receive (subst_process p (shift m 2) (S (S k)))
  | close => close
  | wait p => wait (subst_process p m k)
  end.

Definition subst p m := subst_process p m 0. *)

(******************************************************************************)
(* Renamings                                                                  *)
(******************************************************************************)
Definition renaming := nat -> nat.

Definition up_ren  (r : renaming) : renaming :=
  fun k =>
    match k with
    | O   => O
    | S x => S (r x)
    end.

Fixpoint rename_process (p : process) (r : renaming) : process :=
  match p with
  | link ml mr => link (rename_message ml r) (rename_message mr r)
  | cut pl pr => cut (rename_process pl (up_ren r)) (rename_process pr (up_ren r))
  | seq p s => seq (rename_process p (up_ren r)) (rename_statement s r)
  | stop => stop
  end
with rename_message (m : message) (r : renaming) : message :=
  match m with
  | future i => future (r i)
  | prefix s => prefix (rename_statement s r)
  end
with rename_statement (s : statement) (r : renaming) : statement :=
  match s with
  | choose_left p => choose_left (rename_process p (up_ren r))
  | choose_right p => choose_right (rename_process p (up_ren r))
  | offer_choice p1 p2 => offer_choice (rename_process p1 (up_ren r)) (rename_process p2 (up_ren r))
  | send p1 p2 => send (rename_process p1 (up_ren r)) (rename_process p2 (up_ren r))
  | receive p => receive (rename_process p (up_ren (up_ren r)))
  | close => close
  | wait p => wait (rename_process p r)
  end.

(* In FD, we sometimes reassociate the order of bindings which requires
   swapping De-Bruijn indicies 0 and 1 *)
Definition swap01 : nat -> nat :=
  fun k =>
    match k with
    | O => 1
    | 1 => O
    | x => x
    end.

(******************************************************************************)
(* Properties of bijections                                                   *)
(******************************************************************************)
(* in general, renamings have to be bijections to preserve typing *)
Definition cancel {A B : Type} (f : A -> B) g :=
  forall x, g (f x) = x.

Variant bijective {A B : Type} (f : B -> A) : Type :=
  Bijective : forall g, cancel f g -> cancel g f -> bijective f.

Definition bijection {A B : Type} (f : B -> A) :=
  forall y, { x : B | f x = y /\ (forall z, f z = y -> x = z) }.

Definition inverse_of_bijective {A B : Type} (f : A -> B) :
  bijective f -> { g : B -> A | cancel f g /\ cancel g f }.
Proof.
  intros [g cancel_fg cancel_gf].
  now exists g.
Defined.

Lemma shift_preserves_bijection :
  forall (r : renaming),
    bijective r -> bijective (up_ren r).
Proof.
  intros r Hbij.
  destruct Hbij as [r_inv Hcancel0 Hcancel1].
  pose (shift_r_inv := fun k => match k with
                                | O => O
                                | S x => S (r_inv x)
                                end).
  apply Bijective with shift_r_inv.
  + intros [|]; simpl; auto.
  + intros [|]; simpl; auto.
Qed.

(* swap01 is bijective *)
Lemma swap01_is_bijective : bijective swap01.
Proof.
  apply Bijective with swap01; intros [|[|]]; auto.
Qed.
