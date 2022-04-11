Require Export Predefs.
Require Export TLC.LibTactics.
Require Export TLC.LibLN.
Require Export GMu.Prelude.
Require Export Definitions.


Require Export Lists.List.
Export ListNotations.
Require Export ExampleTactics.

Notation "'{' A '==' T '}'" := (dec_typ A T T).
Coercion typ_rcd : dec >-> Target.typ.
Notation "'{(' a , .. , c ')}'" := (defs_cons (.. (defs_cons defs_nil a) ..) c).
Coercion trm_val  : val >-> trm.

Coercion defp : path >-> def_rhs.
Coercion defv : val >-> def_rhs.

Lemma intersection_order : forall G A1 B1 A2 B2,
    G ⊢ A1 <: A2 ->
    G ⊢ B1 <: B2 ->
    G ⊢ A1 ∧ B1 <: A2 ∧ B2.
Proof.
  intros.
  apply subtyp_and2.
  - apply subtyp_trans with A1; auto.
  - apply subtyp_trans with B1; auto.
Qed.

Notation "G ⊢ A =:= B" := (G ⊢ A <: B /\ G ⊢ B <: A) (at level 40, A at level 59).

Lemma eq_transitive : forall G A B C,
    G ⊢ A =:= B ->
    G ⊢ B =:= C ->
    G ⊢ A =:= C.
Proof.
  intros G X Y Z [] [].
  constructor;
    eapply subtyp_trans; eauto.
Qed.

Lemma eq_symmetry : forall G A B,
    G ⊢ A =:= B ->
    G ⊢ B =:= A.
Proof.
  intros G X Y [].
  constructor; auto.
Qed.

Lemma eq_reflexive : forall G A,
    G ⊢ A =:= A.
Proof.
  constructor;
    apply subtyp_refl.
Qed.

Lemma swap_typ : forall G X Y L T,
    G ⊢ trm_path (pvar Y) : {{pvar X}} ->
    G ⊢ trm_path (pvar X) : T ->
    G ⊢ pvar X ↓ L =:= pvar Y ↓ L.
Proof.
  intros.
  constructor.
  - eapply subtyp_sngl_qp with (p := pvar Y) (q := pvar X); eauto.
    assert (HR: pvar X = (pvar X) •• []) by crush.
    rewrite HR at 2.
    assert (HR2: pvar Y = (pvar Y) •• []) by crush.
    rewrite HR2 at 2.
    apply rpath.
  - eapply subtyp_sngl_pq with (p := pvar Y) (q := pvar X); eauto.
    assert (HR: pvar X = (pvar X) •• []) by crush.
    rewrite HR at 2.
    assert (HR2: pvar Y = (pvar Y) •• []) by crush.
    rewrite HR2 at 2.
    apply rpath.
Qed.

Lemma eq_sel : forall G p A T,
    G ⊢ trm_path p : typ_rcd { A == T } ->
    G ⊢ T =:= (p ↓ A).
Proof.
  intros.
  constructor.
  - eapply subtyp_sel2; eauto.
  - eapply subtyp_sel1; eauto.
Qed.

Lemma sub_and_assoc : forall G A B C,
    G ⊢ A ∧ (B ∧ C) <: (A ∧ B) ∧ C.
Proof.
  intros.
  apply subtyp_and2.
  + apply subtyp_and2.
    * apply subtyp_and11.
    * eapply subtyp_trans.
      -- apply subtyp_and12.
      -- apply subtyp_and11.
  + eapply subtyp_trans;
      apply subtyp_and12.
Qed.

Lemma sub_and_assoc2 : forall G A B C,
    G ⊢ (A ∧ B) ∧ C <: A ∧ (B ∧ C).
Proof.
  intros.
  apply subtyp_and2.
  + eapply subtyp_trans;
      apply subtyp_and11.
  + apply subtyp_and2.
    * eapply subtyp_trans.
      -- apply subtyp_and11.
      -- apply subtyp_and12.
    * apply subtyp_and12.
Qed.

Lemma eq_and_assoc : forall G A B C,
    G ⊢ A ∧ (B ∧ C) =:= (A ∧ B) ∧ C.
Proof.
  intros.
  constructor.
  - apply sub_and_assoc.
  - apply sub_and_assoc2.
Qed.

Lemma sub_and_comm : forall G A B,
    G ⊢ A ∧ B <: B ∧ A.
Proof.
  intros.
  apply subtyp_and2.
  - apply subtyp_and12.
  - apply subtyp_and11.
Qed.

Lemma eq_and_comm : forall G A B,
    G ⊢ A ∧ B =:= B ∧ A.
Proof.
  constructor; apply sub_and_comm.
Qed.

Lemma sub_and_merge : forall G A B C D,
    G ⊢ A <: B ->
    G ⊢ C <: D ->
    G ⊢ A ∧ C <: B ∧ D.
Proof.
  intros.
  apply subtyp_and2.
  - eapply subtyp_trans.
    + apply subtyp_and11.
    + auto.
  - eapply subtyp_trans.
    + apply subtyp_and12.
    + auto.
Qed.

Lemma eq_and_merge : forall G A B C D,
    G ⊢ A =:= B ->
    G ⊢ C =:= D ->
    G ⊢ A ∧ C =:= B ∧ D.
Proof.
  introv [] [].
  constructor; apply~ sub_and_merge.
Qed.

Lemma eq_and_bot : forall G A,
    G ⊢ A ∧ ⊥ =:= ⊥.
  auto.
Qed.

Lemma eq_and_top : forall G A,
    G ⊢ A ∧ ⊤ =:= A.
  auto.
Qed.

Lemma eq_and_self : forall G A,
    G ⊢ A ∧ A =:= A.
  auto.
Qed.

Lemma eq_and_bot_exfalso : forall G A B,
    G ⊢ A ∧ ⊥ =:= B ∧ ⊥.
Proof.
  constructor.
  - eapply subtyp_trans.
    + apply subtyp_and12.
    + apply subtyp_bot.
  - eapply subtyp_trans.
    + apply subtyp_and12.
    + apply subtyp_bot.
Qed.

Lemma sub_exfalso : forall G X Y,
    G ⊢ ⊤ <: ⊥ ->
    G ⊢ X <: Y.
Proof.
  intros.
  apply* subtyp_trans.
Qed.

Lemma eq_exfalso : forall G X Y,
    G ⊢ ⊤ =:= ⊥ ->
    G ⊢ X =:= Y.
Proof.
  introv [].
  constructor;
    apply~ sub_exfalso.
Qed.

Lemma eq_inv : forall G X1 X2 T1 T2 A,
    G ⊢ X1 =:= X2 ->
    X1 ↘ {A >: T1 <: T1} ->
    X2 ↘ {A >: T2 <: T2} ->
    G ⊢ T1 =:= T2.
Proof.
  introv [S1 S2]; intros.
  constructor.
  - lets*: subtyp_rcd_inv1.
  - lets*: subtyp_rcd_inv2.
Qed.

Lemma eq_inv_direct : forall G T1 T2 A,
    G ⊢ typ_rcd { A >: T1 <: T1 } =:= typ_rcd { A >: T2 <: T2 } ->
    G ⊢ T1 =:= T2.
Proof.
  introv EQ; intros.
  lets*: eq_inv EQ.
Qed.

