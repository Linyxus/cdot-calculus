Require Import GMu.Definitions.
Require Import GMu.Infrastructure.
Require Import GMu.Equations.
Require Import TLC.LibTactics.
Require Import TLC.LibEnv.
Require Import TLC.LibLN.

  (* Ht : {Σ, empty}⊢ trm_constructor Tparams Name e1 ∈ T1 ** T2 *)
Lemma CanonicalConstructorType : forall Σ Δ E Tparams Name Ctor e1 T,
    {Σ, Δ, E} ⊢(Treg) trm_constructor Tparams (Name, Ctor) e1 ∈ T ->
    exists Typs, T = typ_gadt Typs Name.
Proof.
  introv Htyp.
  inversions Htyp.
  rewrite rewrite_open_tt_many_gadt.
  eexists.
  f_equal.
Qed.

Lemma CanonicalConstructorTypeGen : forall Σ Δ E Tparams Ctor e1 T,
    {Σ, Δ, E} ⊢(Treg) trm_constructor Tparams Ctor e1 ∈ T ->
    exists Typs Name, T = typ_gadt Typs Name.
Proof.
  intros.
  destruct Ctor.
  apply CanonicalConstructorType in H; auto.
  destruct H as [Typs Heq].
  eexists. eexists. eauto.
Qed.

Local Hint Resolve CanonicalConstructorTypeGen.

Ltac contradictory_constructor_type :=
  lazymatch goal with
  | H: {?S, ?D, ?E} ⊢(?TT) trm_constructor ?Ts ?C ?e ∈ ?T |- _ =>
    apply CanonicalConstructorTypeGen in H;
    let Hcontradict := fresh "contradict" in
    destruct H as [? [? Hcontradict]];
    inversion Hcontradict
  end.

Lemma CanonicalFormTuple : forall Σ Δ e T1 T2,
    value e ->
    {Σ, Δ, empty} ⊢(Treg) e ∈ T1 ** T2 ->
    exists v1 v2, e = trm_tuple v1 v2.
Proof.
  introv Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; try congruence.
  inversions H6.
  - false* binds_empty_inv.
  - contradictory_constructor_type.
Qed.

Lemma CanonicalFormAbs : forall Σ Δ e T1 T2,
    value e ->
    {Σ, Δ, empty} ⊢(Treg) e ∈ T1 ==> T2 ->
    exists v1, e = trm_abs T1 v1.
Proof.
  introv Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; try congruence.
  - false* binds_empty_inv.
  - contradictory_constructor_type.
Qed.

Lemma CanonicalFormTAbs : forall Σ Δ e T,
    value e ->
    {Σ, Δ, empty} ⊢(Treg) e ∈ typ_all T ->
    exists v1, e = trm_tabs v1.
Proof.
  introv Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; try congruence.
  - false* binds_empty_inv.
  - contradictory_constructor_type.
Qed.

Lemma CanonicalFormUnit : forall Σ Δ e,
    value e ->
    {Σ, Δ, empty} ⊢(Treg) e ∈ typ_unit ->
    e = trm_unit.
Proof.
  introv Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; try congruence.
  - false* binds_empty_inv.
  - contradictory_constructor_type.
Qed.

Lemma CanonicalFormGadt : forall Σ Δ e Ts N,
    value e ->
    {Σ, Δ, empty} ⊢(Treg) e ∈ typ_gadt Ts N ->
    exists Ts' C v, e = trm_constructor Ts' (N, C) v.
Proof.
  introv Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; try congruence.
  - false* binds_empty_inv.
  - rewrite rewrite_open_tt_many_gadt in H8.
    inversions H8.
    inversions H13.
    repeat eexists.
Qed.
