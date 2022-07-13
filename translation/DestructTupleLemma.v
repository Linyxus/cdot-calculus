(*
This file presents how our added inversion rules can be used to invert an equality of complex types (like tuple) to equality of their components.
Exactly the same technique can be used for inverting equalities of GADTs, in fact in this context we can treat a tuple as a special case of a GADT Tuple[A,B].
*)
Require Import Helpers.
Require Import Library.

Lemma destruct_tuple_lemma : forall G TT A B C D,
    G ⊢ (pvar lib) ↓ Tuple =:= μ(TT) ->
    G ⊢ (pvar lib) ↓ Tuple ∧ {T1 == A} ∧ {T2 == B} =:= (pvar lib) ↓ Tuple ∧ {T1 == C} ∧ {T2 == D} ->
    G ⊢ A =:= C.
Proof.
  introv libEQ EQ.
  assert (disjoint \{ Target.label_typ T1} \{ Target.label_typ T2}).
  1: {
    apply fset_extens; intros x H.
    - rewrite in_inter in H.
      destruct H as [H1 H2].
      rewrite in_singleton in H1.
      rewrite in_singleton in H2.
      subst.
      inversion H2.
      lets* : diff.
    - rewrite in_empty in H.
      contradiction.
  }
  assert (EQ2:
            G ⊢ (μ(TT)) ∧ {T1 == A} ∧ {T2 == B} =:= (μ(TT)) ∧ {T1 == C} ∧ {T2 == D}).
  - apply eq_transitive with ((pvar lib) ↓ Tuple ∧ {T1 == A} ∧ {T2 == B}).
    + apply eq_and_merge; auto.
      apply eq_and_merge; auto.
      apply~ eq_symmetry.
    + apply eq_transitive with ((pvar lib) ↓ Tuple ∧ {T1 == C} ∧ {T2 == D}); auto.
      * apply eq_and_merge; auto.
        apply eq_and_merge; auto.
  - eapply eq_inv.
    + exact EQ2.
    + econstructor.
      eapply rcd_andl; auto.
      * eapply rcd_andr; auto.
        cbv.
        apply inter_empty_l.
      * rewrite~ union_empty_l.
    + econstructor.
      eapply rcd_andl; auto.
      * eapply rcd_andr; auto.
        cbv.
        apply inter_empty_l.
      * rewrite~ union_empty_l.
Qed.
