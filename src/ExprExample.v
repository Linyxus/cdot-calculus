
(** * Expr Example *)

(** Encoding the recursive list library from Amin et al. (2016) *)

Require Import ExampleTactics.
Require Import String.
Require Import ExampleHelpers.

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
              (case this of super↘LitInt ⇒ trm_app (this•data) this else ???)
   }
  ).

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
       }


End ExprExample.
