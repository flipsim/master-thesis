From FD Require Import Syntax.
From FD Require Import StructCong.
From FD Require Import Typing.
From FD Require Import Reduction.
From FD Require Import Preservation.
From FD Require Import FinalProcess.
From FD Require Import Progress.

(******************************************************************************)
(* Main Results                                                               *)
(******************************************************************************)

(* Preservation for Structural Congruence:
   Given two structurally congruent processes P and P' (P ≡ P'),
   then P is well-typed under context Γ (Γ ⊢ P :#) iff P' is well-typed
   under context Γ (Γ ⊢ P' :#).
*)

Theorem preservation_for_structural_congruence :
  forall P P' Γ, P ≡ P' -> Γ ⊢ P :# <-> Γ ⊢ P' :#.
Proof. intros ? ? Γ H. exact (proj1 struct_cong_preserves_typing _ _ H Γ). Qed.

Print Assumptions preservation_for_structural_congruence.

(* Preservation:
   Given that a process P is well-typed under context Γ (Γ ⊢ P) and
   P performs a reductions step P ⊳ P', then the reduct is well-typed under
   context Γ (Γ ⊢ P')
*)
Theorem preservation :
  forall Γ P P', Γ ⊢ P :# -> P ⊳ P' -> Γ ⊢ P' :#.
Proof. intros ? ? ? Hwt Hred. exact (preservation _ _ _ Hwt Hred). Qed.

Print Assumptions preservation.

(* Progress:
   Given a process P that is well-typed under context Γ (Γ ⊢ P :#),
   then P is a final process or there exists a process P' such that
   P reduces to P' (P ⊳ P').
*)
Theorem progress :
  forall Γ P, Γ ⊢ P :# -> (exists P', P ⊳ P') \/ final P.
Proof. exact progress. Qed.

Print Assumptions progress.

