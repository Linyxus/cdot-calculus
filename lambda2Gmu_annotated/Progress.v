Require Import GMuAnnot.Prelude.
Require Import GMuAnnot.Infrastructure.
Require Import GMuAnnot.Regularity.
Require Import GMuAnnot.CanonicalForms.
Require Import GMuAnnot.Equations.

#[export] Hint Resolve binds_empty_inv.

Ltac empty_binding :=
  match goal with
  | H: binds ?x ?v empty |- _ => apply binds_empty_inv in H; contradiction
  | _ => fail "no empty bindings found"
  end.

Ltac IHT e :=
  match goal with
  | Ht: {?Σ, ?D, ?E} ⊢(?TT) e ∈ ?T |- _ =>
    match goal with
    | IH: forall T, ?P0 -> {Σ, D, E} ⊢(?TT2) e ∈ T -> ?P |- _ =>
      let H := fresh "IHt" in
      assert P as H; eauto
    end
  end.

Ltac generalize_typings :=
  match goal with
  | [ H: {?Σ, ?D, ?E} ⊢(?TT) ?e ∈ ?T |- _ ] =>
    match TT with
    | Tgen => fail 1
    | Treg => fail 1
    | _ => apply Tgen_from_any in H
    end
  end.

(* TODO: move to Equations *)
Lemma empty_eq_is_equivalent : forall Σ T1 T2,
  entails_semantic Σ emptyΔ (T1 ≡ T2) ->
  T1 = T2.
  introv Sem.
  cbn in *.
  lets M: Sem (@nil (var * typ)).
  forwards * : M.
  constructor.
Qed.

#[export] Hint Constructors value red.
Theorem progress_thm : progress.
  unfold progress.
  introv Typ.
  assert (Hterm: term e).
  1: {
    eapply typing_implies_term; eauto.
  }
  apply Tgen_from_any in Typ. clear TT.

  gen T Hterm.
  induction e using trm_ind;
    introv TypGen Hterm;
    lets [T2 [TypReg EQ]]: inversion_typing_eq TypGen;
    inversion TypReg;
    inversion Hterm;
    subst;
    try solve [
          left*
        | repeat generalize_typings;
          forwards* [Hv1 | [e1' Hred1]]: IHe1;
          forwards* [Hv2 | [e2' Hred2]]: IHe2
        ]; clear TypGen EQ T; try rename T2 into T.
  - empty_binding.
  - repeat generalize_typings.
    forwards * [Hval | [? ?]]: IHe.
  - generalize_typings.
    forwards * [Hval | [? ?]]: IHe.
    lets [T' [Typ2 EQ]]: inversion_typing_eq H0.
    apply empty_eq_is_equivalent in EQ. subst.
    lets* [v1 [v2 ?]]: CanonicalFormTuple Typ2; subst.
    right*.
  - generalize_typings.
    forwards * [Hval | [? ?]]: IHe.
    lets [T' [Typ2 EQ]]: inversion_typing_eq H0.
    apply empty_eq_is_equivalent in EQ. subst.
    lets* [v1 [v2 ?]]: CanonicalFormTuple Typ2; subst.
    right*.
  - repeat generalize_typings.
    forwards * [Hval1 | [? ?]]: IHe1.
    forwards * [Hval2 | [? ?]]: IHe2.
    right.
    lets [T' [Typ2 EQ]]: inversion_typing_eq H5.
    apply empty_eq_is_equivalent in EQ. subst.
    lets* [v1 ?]: CanonicalFormAbs Typ2; subst.
    eexists.
    apply* red_beta.
  - repeat generalize_typings.
    forwards * [Hval1 | [? ?]]: IHe.
    right.
    lets [T' [Typ2 EQ]]: inversion_typing_eq H1.
    apply empty_eq_is_equivalent in EQ. subst.
    lets* [v1 ?]: CanonicalFormTAbs Typ2; subst.
    eexists.
    apply* red_tbeta.
  - repeat generalize_typings.
    right.
    eexists.
    eauto.
  - right.
    rename l into branches.
    repeat generalize_typings.
    forwards * [Hval1 | [? ?]]: IHe.
    lets [T' [Typ2 EQ]]: inversion_typing_eq H3.
    apply empty_eq_is_equivalent in EQ; subst.
    lets* [GCargs [cid [ctor_e ?]]]: CanonicalFormGadt Typ2; subst.
    inversions Typ2.
    match goal with
    | [ H1: binds ?g ?A Σ, H2: binds ?g ?B Σ |- _ ] =>
      let H := fresh "H" in
      lets H: binds_ext H1 H2;
        inversions H
    end.
    match goal with
    | [ Hnth: List.nth_error ?As ?i = Some ?A |- _ ] =>
      match goal with
      | [ Hlen: length As = length ?Bs |- _ ] =>
        lets* [[clA clT] [nth_cl inzip]]: nth_error_implies_zip Hnth Hlen
      end
    end.
    assert (clA = length GCargs).
    * match goal with
      | [ H: forall def clause, List.In (def, clause) ?A -> clauseArity clause = Carity def |- _ ] =>
        lets*: H inzip
      end.
    * subst.
      eexists.
      eauto.
Qed.
