From FD Require Import Syntax.
From FD Require Import StructCong.
From FD Require Import Contexts.
From FD Require Import Typing.
From FD Require Import Reduction.
From FD Require Import Preservation.
From FD Require Import FinalProcess.
From FD Require Import Progress.
From FD Require Import Irreducibility.
From FD Require Import ConfluenceDefs.
From FD Require Import DirectedCong.
From FD Require Import ParallelReduction.
From FD Require Import Confluence.

From Stdlib Require Import Relations.

(******************************************************************************)
(* Main Results                                                               *)
(******************************************************************************)

(*** Type Safety **************************************************************)

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
  forall Γ P, Γ ⊢ P :# -> (exists P', P ⊳ P') \/ is_final P.
Proof. exact progress. Qed.

Print Assumptions progress.

(* Progress for closed processes:
   Given a closed process P, then there exists a process P' such that P reduces
   to P' or P is the nil process (stop).
*)
Corollary progress_for_closed_processes :
  forall Γ P, ctx_eq Γ empty_ctx -> Γ ⊢ P :# -> (exists P', P ⊳ P') \/ (P = stop).
Proof. exact progress_for_closed_processes. Qed.

Print Assumptions progress_for_closed_processes.

(* Given a well-typed process P under some context Γ (Γ ⊢ P :#),
   then P is final iff P is irreducible.
*)
Theorem final_iff_irreducible :
  forall Γ P, Γ ⊢ P :# -> is_final P <-> irreducible P.
Proof. exact final_iff_irreducible. Qed.

Print Assumptions final_iff_irreducible.

(*** Church-Rosser ************************************************************)

(* Well-typed processes enjoy Church-Rosser
*)
Lemma church_rosser :
  forall Γ P Q1 Q2, Γ ⊢ P :# -> P ▶ Q1 -> P ▶ Q2 ->
    exists R, Q1 ▶ R /\ Q2 ▶ R.
Proof. exact church_rosser. Qed.

Print Assumptions church_rosser.
