(** * Subtype constraint Example *)

(** Encoding the recursive list library from Amin et al. (2016) *)

Require Import ExampleTactics.
Require Import String.
Require Import ExampleHelpers.
Require Import Replacement.

Section SubExample.

Variable A B C X : typ_label.

Hypothesis CT1: A <> B.
Hypothesis CT2: A <> C.
Hypothesis CT3: B <> C.
Hypothesis CT7: X <> A.
Hypothesis CT8: X <> B.
Hypothesis CT9: X <> C.

Variable Any SUB Refl : typ_label.

Hypothesis CT4: Any <> SUB.
Hypothesis CT5: Any <> Refl.
Hypothesis CT6: SUB <> Refl.

Variable mkRefl coerce : trm_label.

Hypothesis Ct1: mkRefl <> coerce.

Definition SUBType :=
  (typ_rcd { A >: ⊥ <: ⊤ } ∧ typ_rcd { B >: ⊥ <: ⊤ }).

Definition ReflType :=
  (typ_rcd { A >: ⊥ <: this↓C } ∧
   typ_rcd { B >: this↓C <: ⊤ } ∧
   typ_rcd { C >: ⊥ <: ⊤}).

Definition TightReflType c :=
  (typ_rcd { A >: c <: c } ∧
   typ_rcd { B >: c <: c } ∧
   typ_rcd { C >: c <: c}).

Definition EnvType :=
  (typ_rcd { Any >: ⊤ <: ⊤ } ∧
   typ_rcd { SUB >: μ SUBType <: μ SUBType} ∧
   typ_rcd { Refl >: μ ReflType <: μ ReflType } ∧
   typ_rcd { mkRefl ⦂ ∀(typ_rcd { X >: ⊥ <: ⊤ }) (super↓Refl) } ∧
   typ_rcd { coerce ⦂ ∀(this↓SUB)∀(this↓A) (super↓B) }).

Definition t :=
  (ν[this↘Any](EnvType)
    defs_nil Λ
    { Any ⦂= ⊤ } Λ
    { SUB ⦂= μ SUBType } Λ
    { Refl ⦂= μ ReflType } Λ
    { mkRefl :=v λ(typ_rcd { X >: ⊥ <: ⊤ })
                 trm_let
                 (trm_val
                  (ν[ssuper↘Refl](TightReflType (super↓X))
                   defs_nil Λ
                   { A ⦂= super↓X } Λ
                   { B ⦂= super↓X } Λ
                   { C ⦂= super↓X }))
                 (trm_path this)
    } Λ
    { coerce :=v λ(this↓SUB)
                 trm_val (λ(this↓A)
                           case super of ssuper ↘ Refl ⇒ trm_path super else ???t) }).

Theorem sub_typing :
  empty ⊢ trm_val t : μ EnvType.
Proof.
  fresh_constructor. repeat apply ty_defs_cons; crush.
  - Case "mkRefl"%string.
    constructor.
    fresh_constructor.
    (* typing the lambda *)
    crush.
    apply ty_sub with (T := μ ReflType).
    + SCase "typing the result"%string.
      fresh_constructor.
      fresh_constructor.
      repeat apply ty_defs_cons; crush.
      * crush.
        apply ty_sub with (T := μ ReflType).
        ** apply ty_rec_intro. crush.
           apply ty_and_intro; try apply ty_and_intro.
           {
             var_subtyp.
             - eauto.
             - eapply subtyp_trans. apply subtyp_and11.
               eapply subtyp_trans. apply subtyp_and11.
               eauto.
           }
           {
             var_subtyp.
             - eauto.
             - eapply subtyp_trans. apply subtyp_and11.
               eapply subtyp_trans. apply subtyp_and12.
               eauto.
           }
           {
             var_subtyp.
             - eauto.
             - eapply subtyp_trans. apply subtyp_and12.
               eauto.
           }
       ** eapply subtyp_sel2. var_subtyp.
          *** eauto.
          *** eapply subtyp_trans. apply subtyp_and11.
              eapply subtyp_trans. apply subtyp_and11.
              apply subtyp_and12.
      * crush. apply ty_rec_intro. crush.
        Ltac var_rec_subtyp :=
          match goal with
          | [ |- ?G ⊢ tvar ?x : ?T ] =>
            match goal with
            | [ |- context [x ~ μ ?BT] ] =>
              apply ty_sub with BT
            end
          end.
        apply ty_and_intro; try apply ty_and_intro.
        {
          var_rec_subtyp.
          - eauto.
          - eapply subtyp_trans. apply subtyp_and11.
            eapply subtyp_trans. apply subtyp_and11.
            apply subtyp_typ; auto. eapply subtyp_sel2.
            var_rec_subtyp.
            + eauto.
            + apply subtyp_and12.
        }
        {
          var_rec_subtyp.
          - eauto.
          - eapply subtyp_trans. apply subtyp_and11.
            eapply subtyp_trans. apply subtyp_and12.
            apply subtyp_typ; auto. eapply subtyp_sel1.
            var_rec_subtyp.
            + eauto.
            + apply subtyp_and12.
        }
        {
          var_rec_subtyp.
          - eauto.
          - eapply subtyp_trans. apply subtyp_and12.
            eauto.
        }
    + SCase "subtyping between the result and the tag"%string.
      eapply subtyp_sel2.
      var_subtyp.
      * eauto.
      * eapply subtyp_trans. apply subtyp_and11.
        eapply subtyp_trans. apply subtyp_and11.
        apply subtyp_and12.
 - Case "coerce"%string.
   constructor. fresh_constructor. crush.
   fresh_constructor. crush.
   fresh_constructor; crush.
   + SCase "matched"%string.
     apply ty_sub with (T := pvar y ↓ A).
     * eauto.
     * Ltac remember_ctx_sub G :=
        match goal with
            | H: _ |- ?G' ⊢ _ <: _ =>
              remember G' as G
        end.
       remember_ctx_sub G.
       assert (Hs: G ⊢ pvar y1 ↓ A <: pvar y1 ↓ B).
       {
         apply subtyp_trans with (T := pvar y1 ↓ C).
         - crush. eapply subtyp_sel1.
           assert (Hy1: G ⊢ tvar y1 : μ ReflType). {
             subst. var_subtyp.
             - eauto.
             - eapply subtyp_trans. apply subtyp_and12.
               eapply subtyp_sel1.
               var_subtyp.
               + eauto.
               + eapply subtyp_trans. apply subtyp_and11.
                 eapply subtyp_trans. apply subtyp_and11.
                 apply subtyp_and12.
           }
           apply ty_rec_elim in Hy1.
           unfold open_typ_p in Hy1. simpl in Hy1. cases_if.
           eapply ty_sub. exact Hy1.
           eapply subtyp_trans. apply subtyp_and11.
           apply subtyp_and11.
         - crush. eapply subtyp_sel2.
           assert (Hy1: G ⊢ tvar y1 : μ ReflType). {
             subst. var_subtyp.
             - eauto.
             - eapply subtyp_trans. apply subtyp_and12.
               eapply subtyp_sel1.
               var_subtyp.
               + eauto.
               + eapply subtyp_trans. apply subtyp_and11.
                 eapply subtyp_trans. apply subtyp_and11.
                 apply subtyp_and12.
           }
           apply ty_rec_elim in Hy1.
           unfold open_typ_p in Hy1. simpl in Hy1. cases_if.
           eapply ty_sub. exact Hy1.
           eapply subtyp_trans. apply subtyp_and11.
           apply subtyp_and12.
       }
       apply subtyp_trans with (T := pvar y1 ↓ A).
       ** apply subtyp_sngl_qp with (p := pvar y1) (q := pvar y) (U:=⊤).
          *** subst. var_subtyp. eauto. apply subtyp_and11.
          *** subst. var_subtyp. eauto. eauto.
          *** apply repl_intro_path_sel.
       ** apply subtyp_trans with (T := pvar y1 ↓ B); auto.
          *** apply subtyp_sngl_pq with (p := pvar y1) (q := pvar y) (U:=⊤).
              **** subst. var_subtyp. eauto. apply subtyp_and11.
              **** subst. var_subtyp. eauto. eauto.
              **** apply repl_intro_path_sel.
   + SCase "else"%string.
     repeat apply* weaken_ty_trm.
     lets Htqm: (three_question_marks_strict_term_typing).
     unfold three_question_marks_strict_term, helper_term in Htqm.
     simpl in Htqm.
     apply ty_sub with (T:=⊥); auto.
 - apply ty_sub with (T:=⊤).
   + var_subtyp; auto.
   + crush. apply subtyp_sel2 with (T:=⊤). var_subtyp. eauto. solve_subtyp_and.
Qed.

End SubExample.
