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
  forall Γ P, Γ ⊢ P :# -> (exists P', P ⊳ P') \/ final P.
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
  forall Γ P, Γ ⊢ P :# -> final P <-> irreducible P.
Proof. exact final_iff_irreducible. Qed.

Print Assumptions final_iff_irreducible.

(*** Church-Rosser ************************************************************)

(* Directed congruence possesses the diamond property.
*)
Lemma diamond_property_for_directed_congruence : diamond_property directed_congruence.
Proof. exact directed_cong_diamond. Qed.

Print Assumptions diamond_property_for_directed_congruence.

(* ≡ is contained in the transitive closure of ⇛
*)
Lemma struct_cong_subset_trans_clos_directed_cong :
  forall P Q, P ≡ Q -> clos_trans_1n _ directed_congruence P Q.
Proof. exact (proj1 struct_cong_in_trans_directed_cong). Qed.

Print Assumptions struct_cong_subset_trans_clos_directed_cong.

(* ⇛ is contained in ≡
*)
Lemma directed_cong_subset_struct_cong :
  forall P Q, P ⇛ Q -> P ≡ Q.
Proof. exact (proj1 directed_cong_in_struct_cong). Qed.

Print Assumptions directed_cong_subset_struct_cong.

(* ⊵* = ▶
*)
Lemma par_reds_clos_trans_multi_step_red_coincide :
  forall P Q, (clos_trans _ par_reduces) P Q <-> P ▶ Q.
Proof. exact par_reds_clos_trans_multi_step_red_coincide. Qed.

Print Assumptions par_reds_clos_trans_multi_step_red_coincide.

(* If ⊵ is confluent, then ▶ is too.
*)
Lemma diamond_par_red_imp_diamond_multistep :
  diamond_property par_reduces -> diamond_property multi_step_reduction.
Proof. exact diamond_par_red_imp_diamond_multistep. Qed.

Print Assumptions diamond_par_red_imp_diamond_multistep.
