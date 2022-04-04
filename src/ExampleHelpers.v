(** * Example Helpers *)

(** Helpers for examples. *)

Require Import ExampleTactics.
Require Import String.

Variable HelperAny : typ_label.
Variable Helperloop : trm_label.

Notation HelperType :=
  (typ_rcd {HelperAny >: ⊤ <: ⊤} ∧
   typ_rcd {Helperloop ⦂ Lazy ⊥}).

Definition helper_term :=
  trm_val (ν [this ↘ HelperAny] (HelperType)
             defs_nil Λ
             { HelperAny ⦂= ⊤ } Λ
             { Helperloop := defv (λ (⊤) (trm_app (super•Helperloop) (super•Helperloop)))}).

Lemma helper_typing :
  empty ⊢ helper_term : μ HelperType.
Proof.
  fresh_constructor. repeat apply ty_defs_cons; crush.
  - Case "helper.loop"%string.
    constructor. fresh_constructor.
    crush.
    assert (Heq: ⊥ = open_typ_p ((pvar z) • Helperloop) ⊥) by trivial.
    rewrite Heq. apply ty_all_elim with (S:=⊤).
    + rewrite <- Heq.
      clear Heq.
      assert (Heq: (p_sel (avar_f z) (Helperloop :: nil)) = (pvar z) • Helperloop) by trivial.
      rewrite -> Heq. apply ty_new_elim. eapply ty_sub.
      * apply ty_var. eauto.
      * apply subtyp_and12.
    + eapply ty_sub.
      * apply ty_new_elim. eapply ty_sub.
        ** apply ty_var. eauto.
        ** apply subtyp_and12.
      * eauto.
 - Case "helper tag"%string.
   eapply ty_sub.
   + auto.
   + eapply subtyp_trans.
     * apply subtyp_top.
     * apply subtyp_sel2 with (T:=⊤).
       eapply ty_sub.
       crush.
       apply subtyp_and11.
Qed.

Definition three_question_marks_strict_term :=
  (trm_let helper_term (trm_app (this•Helperloop) this)).

Notation "???t" := (three_question_marks_strict_term).

Lemma three_question_marks_strict_term_typing :
  empty ⊢ ???t : ⊥.
Proof.
  unfold three_question_marks_strict_term.
  fresh_constructor.
  - apply* helper_typing.
  - crush.
    assert (Heq: ⊥ = open_typ_p (pvar z) ⊥) by trivial.
    rewrite Heq.
    apply ty_all_elim with (S:=⊤).
    * rewrite <- Heq. clear Heq.
      assert (Heq: (p_sel (avar_f z) (Helperloop :: nil) = (pvar z) • Helperloop)) by eauto.
      rewrite -> Heq. clear Heq.
      apply ty_new_elim. eapply ty_sub.
      ** apply ty_rec_elim. eauto.
      ** crush.
    * eapply ty_sub. eauto.
      apply subtyp_top.
Qed.

Definition three_question_marks_lazy_value :=
  λ(⊤) ???t.

Notation "???v" := (three_question_marks_lazy_value).

Lemma three_question_marks_typing :
  empty ⊢ trm_val ???v : Lazy ⊥.
Proof.
  fresh_constructor. crush.
  lets H: (three_question_marks_strict_term_typing).
  unfold three_question_marks_strict_term, helper_term in H.
  simpl in H.
  apply* weaken_ty_trm.
Qed.
