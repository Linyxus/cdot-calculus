
(** * Expr Example *)

(** Encoding the recursive list library from Amin et al. (2016) *)

Require Import ExampleTactics.
Require Import String.
Require Import ExampleHelpers.
Require Import Replacement.

Section ExprExample.

Variable X Int Any Expr LitInt : typ_label.
Variable data mkLitInt eval : trm_label.

Hypothesis HT1: Any <> Int.
Hypothesis HT2: Any <> Expr.
Hypothesis HT3: Any <> LitInt.
Hypothesis HT4: Int <> Expr.
Hypothesis HT5: Int <> LitInt.
Hypothesis HT6: Expr <> LitInt.
Hypothesis Ct1: mkLitInt <> eval.

Notation ExprType := (typ_rcd { X >: ⊥ <: ⊤ }).

Definition LitIntType env senv :=
  (typ_rcd { X >: env ↓ Int <: env ↓ Int } ∧
   typ_rcd { data ⦂ Lazy (senv ↓ Int) }).

Definition EnvType :=
  (typ_rcd { Any >: ⊤ <: ⊤ } ∧
   typ_rcd { Int >: this↓Int <: this↓Int } ∧
   typ_rcd { Expr >: μ ExprType <: μ ExprType } ∧
   typ_rcd { LitInt >: μ (LitIntType super ssuper) <: μ (LitIntType super ssuper) } ∧
   typ_rcd { mkLitInt ⦂ ∀(this↓Int) (super↓LitInt) } ∧
   typ_rcd { eval ⦂ ∀(this↓Expr) (this↓X) }).

Definition t :=
  (ν[this↘Any](EnvType)
   defs_nil Λ
   { Any ⦂= ⊤ } Λ
   { Int ⦂= this↓Int } Λ
   { Expr ⦂= μ ExprType } Λ
   { LitInt ⦂= μ (LitIntType super ssuper) } Λ
   { mkLitInt :=v λ(this↓Int)
                  trm_val (ν[ssuper↘LitInt](LitIntType ssuper sssuper)
                  defs_nil Λ
                  { X ⦂= ssuper ↓ Int } Λ
                  { data :=v λ(⊤) (trm_path ssuper) })
   } Λ
   { eval :=v λ(this↓Expr)
              (case this of super↘LitInt ⇒ trm_app (this•data) this else ???t)
   }
  ).

Ltac normalize_psel :=
  match goal with
  | |- context [ p_sel (avar_f ?x) (?a :: nil) ] =>
      idtac x; idtac a;
      assert (HPS: p_sel (avar_f x) (a :: nil) = (pvar x) • a) by trivial;
      rewrite -> HPS; clear HPS
  end.

Ltac cleanup :=
  repeat
    match goal with
    | [ H: ?x <> ?y |- _ ] => clear H
    | [ H: ?x = ?y |- _ ] =>
      match x with
      | y => clear H
      end
    end.

Ltac var_subtyp :=
  match goal with
  | [ |- ?G ⊢ tvar ?x : ?T ] =>
    match goal with
    | [ |- context [x ~ ?BT] ] =>
      apply ty_sub with BT
    end
  end.

Ltac solve_bind :=
  repeat progress (
    lazymatch goal with
    | |- binds ?Var ?What (?Left & ?Right) =>
          match goal with
          | |- binds Var What (Left & Var ~ ?Sth) =>
            apply~ binds_concat_right; apply~ binds_single_eq
          | _ => apply~ binds_concat_left
          end
    end).

Ltac solve_subtyp_and :=
repeat
  match goal with
  | [ |- ?G ⊢ ?A ∧ ?B <: ?C ] =>
    match B with
    | C =>
      apply subtyp_and12
    | _ =>
      eapply subtyp_trans; try apply subtyp_and11
    end
  end.

Ltac var_subtyp_bind :=
  var_subtyp;
  [ apply ty_var; solve_bind
  | solve_subtyp_and].

Ltac false_typing :=
  match goal with
  | |- _ ⊢ _ : ?TT =>
      apply ty_sub with (T:=⊥); try apply subtyp_bot
  end.

Lemma expr_typing:
  empty ⊢ trm_val t : μ EnvType.
Proof.
  fresh_constructor. repeat apply ty_defs_cons; crush.
  - Case "mkLitInt"%string.
    apply ty_def_all. fresh_constructor.
    crush. eapply ty_sub.
    + fresh_constructor. repeat apply ty_defs_cons; crush.
      * SCase "data"%string. constructor.
        fresh_constructor. crush.
      * SCase "tag"%string. crush.
        eapply ty_sub.
        ** remember_ctx G.
          assert (Hy: G ⊢ tvar y0: (typ_rcd {X >: pvar z ↓ Int <: pvar z ↓ Int} ∧ typ_rcd {data ⦂ Lazy (pvar z ↓ Int)})).
          {
            subst. auto.
          }
          apply ty_rec_intro.
          assert (open_typ_p (pvar y0) (typ_rcd {X >: pvar z ↓ Int <: pvar z ↓ Int} ∧ typ_rcd {data ⦂ Lazy (pvar z ↓ Int)}) = typ_rcd {X >: pvar z ↓ Int <: pvar z ↓ Int} ∧ typ_rcd {data ⦂ Lazy (pvar z ↓ Int)}) by trivial.
          rewrite <- H in Hy. exact Hy.
        ** eapply subtyp_sel2.
           eapply ty_sub.
           {
             auto.
           }
           {
             eapply subtyp_trans.
             apply subtyp_and11.
             eapply subtyp_trans.
             apply subtyp_and11.
             apply subtyp_and12.
           }
    + eapply subtyp_sel2.
        eapply ty_sub.
        {
          auto.
        }
        {
          eapply subtyp_trans.
          apply subtyp_and11.
          eapply subtyp_trans.
          apply subtyp_and11.
          apply subtyp_and12.
        }
 - Case "eval"%string.
   constructor.
   fresh_constructor.
   fresh_constructor.
   + crush.
   + crush.
   + crush.
     apply ty_sub with (T:=(pvar z)↓Int).
     * assert (Heq: pvar z ↓ Int = open_typ_p (pvar y0) (pvar z ↓ Int)) by trivial.
       rewrite -> Heq.
       apply ty_all_elim with (S:=⊤).
       { (* func type *)
         normalize_psel.
         apply ty_new_elim.
         rewrite <- Heq. clear Heq.
         remember_ctx G.
         assert (Hy1: G ⊢ tvar y0 : μ LitIntType (pvar z) (pvar z)).
         {
           eapply ty_sub.
           - subst G. auto.
           - eapply subtyp_trans.
             apply subtyp_and12.
             eapply subtyp_sel1.
             eapply ty_sub.
             + subst G. auto.
             + eapply subtyp_trans.
               apply subtyp_and11.
               eapply subtyp_trans.
               apply subtyp_and11.
               apply subtyp_and12.
         }
         assert (Hy2: G ⊢ tvar y0 : LitIntType (pvar z) (pvar z)).
         {
           assert (Heq: LitIntType (pvar z) (pvar z) = open_typ_p (pvar y0) (LitIntType (pvar z) (pvar z))) by trivial.
           rewrite -> Heq.
           apply ty_rec_elim. clear Heq.
           auto.
         }
         eapply ty_sub.
         - exact Hy2.
         - apply subtyp_and12.
       }
       { (* argument type *)
         eapply ty_sub.
         - auto.
         - auto.
       }
     * apply subtyp_trans with (T := pvar y0 ↓ X).
       {
         eapply subtyp_sel2.
         remember_ctx G.
         assert (Hy0: G ⊢ tvar y0 : μ LitIntType (pvar z) (pvar z)). {
           subst. var_subtyp.
           + eauto.
           + eapply subtyp_trans.
             apply subtyp_and12.
             eapply subtyp_sel1.
             var_subtyp.
             * eauto.
             * eauto 3.
         }
         apply ty_rec_elim in Hy0. unfold open_typ_p in Hy0.
         simpl in Hy0.
         eapply ty_sub.
         exact Hy0. apply subtyp_and11.
       }
       {
        apply subtyp_sngl_pq with (p := pvar y0) (q := pvar y) (U:=⊤).
        ** eauto.
        ** eauto.
        ** apply repl_intro_path_sel.
       }
   + crush. repeat apply* weaken_ty_trm.
     lets Ht: (three_question_marks_strict_term_typing).
     false_typing.
     unfold three_question_marks_strict_term, helper_term in Ht.
     simpl in Ht. auto.
 - Case "tag"%string.
   var_subtyp.
   + eauto.
   + eapply subtyp_trans. apply subtyp_top.
     eapply subtyp_sel2. crush.
     var_subtyp.
     * eauto.
     * solve_subtyp_and.
Qed.

End ExprExample.
