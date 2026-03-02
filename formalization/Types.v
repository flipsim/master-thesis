Inductive type : Type :=
  | plus_ty : type -> type -> type
  | tensor_ty : type -> type -> type
  | with_ty : type -> type -> type
  | par_ty : type -> type -> type
  | one_ty : type
  | bot_ty : type.

Fixpoint dual (t : type) : type :=
  match t with
  | one_ty        => bot_ty
  | bot_ty        => one_ty
  | plus_ty a b   => with_ty (dual a) (dual b)
  | with_ty a b   => plus_ty (dual a) (dual b)
  | tensor_ty a b => par_ty (dual a) (dual b)
  | par_ty a b    => tensor_ty (dual a) (dual b)
  end.

(* \upand for par *)
(* \Bbbone for 1*)
Notation "A ⅋ B" := (par_ty A B) (left associativity, at level 61).
Notation "A & B" := (with_ty A B) (left associativity, at level 61).
Notation "A ⊗ B" := (tensor_ty A B) (left associativity, at level 61).
Notation "A ⊕ B" := (plus_ty A B) (left associativity, at level 61).
Notation "⊥" := bot_ty.
Notation "𝟙" := one_ty.

Lemma dual_involutive : forall A, dual (dual A) = A.
Proof.
  induction A; auto; try (
    simpl; rewrite IHA1, IHA2; reflexivity
  ).
Qed.
