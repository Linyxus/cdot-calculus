(*
This file presents how our added inversion rules can be used to invert an equality of complex types (like tuple) to equality of their components.
Exactly the same technique can be used for inverting equalities of GADTs, in fact in this context we can treat a tuple as a special case of a GADT Tuple[A,B].
*)
Require Import Helpers.
Require Import Library.
Require Import TestHelpers.

Lemma destruct_tuple_lemma : forall G A B C D,
    G ⊢ (pvar lib) ↓ Tuple ∧ {T1 == A} ∧ {T2 == B} =:= (pvar lib) ↓ Tuple ∧ {T1 == C} ∧ {T2 == D} ->
    G ⊢ A == C.
Proof.
Admitted.
