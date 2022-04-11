Require Import TestCommon.
Require Import Regularity.

Open Scope L2GMu.
Definition id := Λ => (λ (##0) => (#0)).
Definition id_typ := ∀ (##0 ==> ##0).

Ltac simpl_op := cbn; try case_if; auto.
(* Ltac solve_simple_type := repeat ((* let L := gather_vars in try apply typing_abs with L; *) intros; econstructor; eauto; cbn; try case_if; eauto). *)
Ltac crush_simple_type := repeat (cbv; (try case_if); econstructor; eauto).

Lemma well_typed_id : {empty, emptyΔ, empty} ⊢(Treg) id ∈ id_typ.
  cbv; autotyper1.
Qed.

Lemma well_formed_id :
  term id
  /\ type id_typ
  /\ wft empty emptyΔ id_typ.
  destruct* (typing_regular well_typed_id).
Qed.



Definition id_app := (id <|| typ_unit <| trm_unit).
Lemma id_app_types : {empty, emptyΔ, empty} ⊢(Treg) id_app ∈ typ_unit.
Proof.
  cbv.
  autotyper1.
  instantiate (1 := (##0 ==> ##0)).
  auto.
  autotyper1.
  auto.
Qed.

Ltac crush_eval := repeat (try (apply eval_finish; eauto); econstructor; simpl_op).

Lemma id_app_evals : evals id_app trm_unit.
Proof.
  crush_eval.
  Unshelve. fs. fs. fs. fs.
Qed.

Require Import Preservation.
Lemma preservation_evals : forall Σ e T TT e',
    {Σ, emptyΔ, empty} ⊢(TT) e ∈ T ->
    evals e e' ->
    {Σ, emptyΔ, empty} ⊢(Tgen) e' ∈ T.
Proof.
  introv Typ Ev.
  eapply Tgen_from_any in Typ.
  induction Ev.
  - apply* IHEv.
    lets HP: preservation_thm.
    unfold preservation in HP.
    apply* HP.
  - auto.
Qed.

Eval cbn in (preservation_evals _ _ _ _ _ id_app_types id_app_evals).

Definition let_id_app := trm_let (id) (#0 <|| typ_unit <| trm_unit).
Lemma let_id_app_types : {empty, emptyΔ, empty} ⊢(Treg) let_id_app ∈ typ_unit.
Proof.
  cbv.
  autotyper1.
  4: {
    instantiate (1 := (##0 ==> ##0)).
    cbn. autotyper1.
  }
  autotyper1.
  autotyper1.
  autotyper1.
  auto.
Qed.

Lemma let_id_app_evals : evals let_id_app trm_unit.
Proof.
  crush_eval.
  Unshelve.
  fs. fs. fs. fs. fs. fs. fs. fs. fs. fs. fs.
Qed.

Definition loop := fixs (typ_unit ==> typ_unit) => λ typ_unit => (#1 <| #0).

Lemma loop_type : {empty, emptyΔ, empty} ⊢(Treg) loop ∈ (typ_unit ==> typ_unit).
Proof.
  cbv.
  autotyper1.
Qed.

Definition divergent := loop <| trm_unit.

Lemma divergent_type : {empty, emptyΔ, empty} ⊢(Treg) divergent ∈ typ_unit.
Proof.
  cbv. autotyper1.
Qed.

Compute divergent_type.

Lemma divergent_diverges : evals divergent divergent.
Proof.
  cbv.
  econstructor.
  - crush_eval.
  - unfold open_ee. cbn; repeat case_if.
    econstructor.
    + crush_eval.
    + repeat case_if.
      apply eval_finish.

      Unshelve.
      fs. fs. fs. fs. fs. fs. fs.
Qed.
