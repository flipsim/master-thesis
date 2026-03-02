From FD Require Import Syntax.
From FD Require Import StructCong.

(* \vartriangleright *)
Reserved Notation "P ⊳ Q" (no associativity, at level 61).

Inductive reduces : process -> process -> Prop :=
  | r_tensor_par : forall P Q R P',
                    P' = rename_process (up P) swap01 ->
                    link (prefix (send P Q)) (prefix (receive R))
                      ⊳ cut (cut R P') Q
  | r_plus_with_l : forall P Q R,
                      link (prefix (choose_left P)) (prefix (offer_choice Q R))
                        ⊳ cut P Q
  | r_plus_with_r : forall P Q R,
                      link (prefix (choose_right P)) (prefix (offer_choice Q R))
                        ⊳ cut P R
  | r_one_bot : forall P, link (prefix close) (prefix (wait P)) ⊳ P
  | r_ax_cut : forall M P,
                cut (link (future 0) M) P ⊳ subst_process P ((downM M) ⋅ id_subst)
  | r_seq : forall P s, seq P s ⊳ subst_process P ((prefix s) ⋅ id_subst)
  | r_cong_cut : forall P P' Q,
                  P ⊳ P' -> cut P Q ⊳ cut P' Q
  | r_cong_seq : forall P P' s,
                  P ⊳ P' -> seq P s ⊳ seq P' s
  | r_struct : forall P P' Q Q',
                P ≡ P' -> P' ⊳ Q' -> Q' ≡ Q -> P ⊳ Q
where
  "P ⊳ Q" := (reduces P Q).
