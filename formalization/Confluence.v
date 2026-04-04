From FD Require Import Syntax.
From FD Require Import FreeVars.
From FD Require Import Renaming.
From FD Require Import FreeVars.
From FD Require Import StructCong.
From FD Require Import ConfluenceDefs.
From FD Require Import DirectedCong.
From FD Require Import Reduction.
From FD Require Import ParallelReduction.

Lemma diamond_par_red_imp_diamond_multistep :
  diamond_property par_reduces -> diamond_property multi_step_reduction.
Proof.
  intros. apply diamond_R_diamond_clos_trans_R in H.
  eapply diamond_preserved_under_eq; eauto.
  apply par_reds_clos_trans_multi_step_red_coincide.
Qed.

Lemma link_directed_cong_par_red_confluent :
  forall ml mr P Q, (link ml mr) ⇛ P -> (link ml mr) ⊵ Q ->
    exists R, P ⊵ R /\ Q ⇛ R.
Proof.
  intros. inversion H; subst.
  { exists Q; split; auto; econstructor. }
  inversion H0; subst.
  + inversion H1; subst.
    - eexists; split; repeat econstructor; auto.
    - apply directed_cong_symm in H. exists (link ml mr). split. (econstructor; eauto).
      econstructor; apply directed_cong_symm; auto.
  + inversion H3; subst.
    - admit.
Admitted.


Lemma confluence_directed_cong_par_red :
  forall P Q1 Q2, P ⇛ Q1 -> P ⊵ Q2 -> exists R, Q1 ⊵ R /\ Q2 ⇛ R.
Proof.
  intros. generalize dependent Q2.
  induction H; intros.
  + exists Q2. split; auto. econstructor.
  + admit.
  + inversion H1; subst.
    - admit.
    - (* downM M' requires well-typedness of M to conclude that 0 is not in free vars of M' *)
      admit.
    - admit.
    - inversion H0; subst.
      * (* cut (cut (link (future 1) M) R) P2
           not covered by parallel reduction
           NB: try approach below before adding addtional reduction rules and
               see how far we can go. However, we will likely need all
               rp_cut_assoc rules up to symmetry (see original approach)
               with this addtional premise
        *)
        (* add a premise:
            L ⇛ (cut (link (future 1) M) R)
           to rp_ax_cut_assoc rules so that
           cut P L ⊵ cut (subst_process P'' ((downM M'' ⋅ id_subst))) R''
        *)
        admit.
      * admit.
      * (* congruences allows to perform association more than once !!!!! *)
        admit.
    - inversion H; subst.
      * admit.
      * admit. (* should work easily with new premise *)
      * admit.
    - admit.
  + inversion H6; subst.
    - exists Q2; split; try (now econstructor).
      admit.
    - (* dont bother doing an inversion on H9; try to use invariances instead *)
      admit.
    - (* in R1, up results in future 2 but swap01 is also uped ->
         future 1 remains in R1 ->
         via cut_cong, the left side may still reduce via cut assoc
         use H9 and invariances too conclude result
         *)
      admit.
    - admit.
    - admit.
  + admit.
  + admit.
Admitted.

(* invariance for ⊵ under renaming, shifting, substitution must follow by induction on depth *)
(* for invariance under subst: show that subst compose then argue by extensionality on composition 
   (NB: always remember which variables occur bound/free; after traversing binder
   substitutions may commute (consider M ⋅ id and (up_subst σ))
*)