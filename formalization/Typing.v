From FD Require Import Syntax.
From FD Require Import Types.
From FD Require Import Contexts.

From Stdlib Require List.
Open Scope list_scope.

Reserved Notation "Γ '⊢' M ':!' A" (no associativity, at level 61).
Reserved Notation "Γ '⊢' s ':$' A" (no associativity, at level 61).
Reserved Notation "Γ '⊢' P ':#'" (no associativity, at level 61).

(*
  Typing rules for
  - processes P (TypingP):  Γ ⊢ P :#
  - statements s (TypingS): Γ ⊢ s :$ A
  - messages M (TypingM):   Γ ⊢ M :! A
*)

(* Process Typing *)
Inductive TypingP : ctx type -> process -> Prop :=
  | t_ax : forall Γ Γ1 Γ2 A M1 M2,
            (Γ ≜ Γ1 ∘ Γ2) ->
            (Γ1 ⊢ M1 :! A) ->
            (Γ2 ⊢ M2 :! (dual A)) ->
            (Γ ⊢ link M1 M2 :#)
  | t_cut : forall Γ Γ1 Γ2 P Q A,
              (Γ ≜ Γ1 ∘ Γ2) ->
              (A .: Γ1) ⊢ P :# ->
              ((dual A) .: Γ2) ⊢ Q :# ->
              Γ ⊢ (cut P Q) :#
  | t_seq : forall Γ Γ1 Γ2 P s A,
              (Γ ≜ Γ1 ∘ Γ2) ->
              (A .: Γ1) ⊢ P :# ->
              Γ2 ⊢ s :$ A ->
              Γ ⊢ (seq P s) :#
  | t_stop : forall Γ,
              ctx_eq Γ empty_ctx ->
              Γ ⊢ stop :#
where
  "Γ '⊢' P ':#'" := (TypingP Γ P)

(* Message Typing *)
with TypingM : ctx type -> message -> type -> Prop :=
  | t_id : forall i A Γ,
            ctx_eq Γ (insert i A empty_ctx) ->
            Γ ⊢ (future i) :! A
  | t_prefix : forall Γ s A,
                (Γ ⊢ s :$ A) ->
                (Γ ⊢ (prefix s) :! A)
where
  "Γ '⊢' M ':!' A" := (TypingM Γ M A)

(* Statement Typing *)
with TypingS : ctx type -> statement -> type -> Prop :=
  | t_plus_l : forall Γ Q A B,
                ((dual A) .: Γ) ⊢ Q :# ->
                Γ ⊢ (choose_left Q) :$ (A ⊕ B)
  | t_plus_r : forall Γ Q A B,
                ((dual B) .: Γ) ⊢ Q :# ->
                Γ ⊢ (choose_right Q) :$ (A ⊕ B)
  | t_with : forall Γ A B Q1 Q2,
              ((dual A) .: Γ) ⊢ Q1 :# ->
              ((dual B) .: Γ) ⊢ Q2 :# ->
              Γ ⊢ (offer_choice Q1 Q2) :$ (A & B)
  | t_tensor : forall Γ Γ1 Γ2 A B Q R,
                Γ ≜ Γ1 ∘ Γ2 ->
                ((dual A) .: Γ1) ⊢ Q :# ->
                ((dual B) .: Γ2) ⊢ R :# ->
                Γ ⊢ (send Q R) :$ (A ⊗ B)
  | t_par : forall Γ A B Q,
              ((dual A) .: ((dual B) .: Γ)) ⊢ Q :# ->
              Γ ⊢ (receive Q) :$ (A ⅋ B)
  | t_one : forall Γ,
              ctx_eq Γ empty_ctx ->
              Γ ⊢ close :$ 𝟙
  | t_bot : forall Γ Q,
              Γ ⊢ Q :# ->
              Γ ⊢ (wait Q) :$ ⊥
where
  "Γ '⊢' s ':$' A" := (TypingS Γ s A).

(* Mutual induction principle for the typing relation *)
Scheme process_typing_ind   := Induction for TypingP Sort Prop
  with message_typying_ind  := Induction for TypingM Sort Prop
  with statement_typing_ind := Induction for TypingS Sort Prop.
Combined Scheme typing_ind from process_typing_ind, message_typying_ind, statement_typing_ind.
