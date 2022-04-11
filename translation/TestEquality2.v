(*
This file shows typing of functions using the Eq GADT defined in TestEqualityEnv.v.

The functions are:
destruct : forall a b c d, Eq (a * b) (c * d) -> Eq a c
*)
Require Import Helpers.
Require Import Library.
Require Import TestHelpers.
Require Import GMu.TestEquality.
Require Import Translation.
Require Import Top.TestEqualityEnv.

Definition p_destruct_typ : typ :=
  translateTyp0 destruct_typ.

Eval cbv in p_destruct_typ.
(*
  = ∀ ({GenT >: ⊥ <: ⊤}) (∀ ({GenT >: ⊥ <: ⊤})
    (∀ ({GenT >: ⊥ <: ⊤}) (∀ ({GenT >: ⊥ <: ⊤})
     (∀ (((pvar env ↓ GN Eq) ∧
           {Ai 1 == ((pvar lib ↓ Tuple) ∧ {T1 == ssuper ↓ GenT}) ∧ {T2 == this ↓ GenT}})
         ∧ {Ai 2 == ((pvar lib ↓ Tuple) ∧ {T1 == sssuper ↓ GenT}) ∧ {T2 == super ↓ GenT}})
      (((pvar env ↓ GN Eq) ∧ {Ai 1 == sssuper ↓ GenT}) ∧ {Ai 2 == ssssuper ↓ GenT})))))
     : typ
 *)

Definition p_destruct_trm : trm :=
  λ (*A*) ({GenT >: ⊥ <: ⊤}) λ (*B*) ({GenT >: ⊥ <: ⊤})
    λ (*C*) ({GenT >: ⊥ <: ⊤}) λ (*D*) ({GenT >: ⊥ <: ⊤})
    λ (*eq1*) (((pvar env ↓ GN Eq) ∧
           {Ai 1 == ((pvar lib ↓ Tuple) ∧ {T1 == (ref 2) ↓ GenT}) ∧ {T2 == (ref 0) ↓ GenT} })
         ∧ {Ai 2 == ((pvar lib ↓ Tuple) ∧ {T1 == (ref 3) ↓ GenT}) ∧ {T2 == (ref 1) ↓ GenT} })
    trm_let
    (* TL = *)
    (TLgen (((pvar env ↓ GN Eq) ∧ {Ai 1 == (* B *) ref 3 ↓ GenT}) ∧ {Ai 2 == (* A *) ref 4 ↓ GenT}))
    (let_trm (
      (ref 1) • pmatch $ ref 0 $
              (λ (*eq1_ev *) (pvar env ↓ GC Eq 0 ∧ {{ ref 1 }})
                 ((pvar env) • refl $$ (let_trm (ν({Bi 1 == ref 6 ↓ GenT}) {( {Bi 1 ⦂= ref 6 ↓ GenT} )} )))
              )
    ))
.

Lemma p_destruct_types :
  empty & lib ~ libType
  & env ~ (open_typ_p (pvar lib) env_typ)
        ⊢
        p_destruct_trm : p_destruct_typ.
Proof.
  remember lib as lib.
  remember env as env.
  intros.
  cbv.
  crush.
  apply_fresh ty_all_intro as A; crush.
  apply_fresh ty_all_intro as B; crush.
  cleanup.
  apply_fresh ty_all_intro as C; crush.
  apply_fresh ty_all_intro as D; crush.
  cleanup.
  rewrite <- Heqlib.
  rewrite <- Heqenv.
  apply_fresh ty_all_intro as eq; crush.
  apply_fresh ty_let as TL.
  1: {
    apply_fresh ty_let as TLres.
    - apply_fresh ty_new_intro as TLself.
      crush.
    - cbn. case_if.
      match goal with
      | [ |- context [ TLres ~ μ ?T ] ] =>
        instantiate (1:=T);
          assert (HR: T = open_typ_p (pvar TLres) T) by crush;
          rewrite HR;
          clear HR
      end.
      apply ty_rec_elim; crush.
  }
  crush.

  apply_fresh ty_let as res.
  - apply_fresh ty_let as app_tmp1.
    + eapply ty_all_elim.
      * fold ((pvar eq) • pmatch).
        apply ty_new_elim.
        instantiate (1:=(∀ (∀ ((pvar env ↓ GC Eq 0) ∧ {{pvar eq}})
                              (super ↓ GenT)) (super ↓ GenT))).
        instantiate (1:={GenT >: ⊥ <: ⊤}).
        cleanup.
        match goal with
        | [ |- context [{GN Eq == μ ?T}] ] =>
          apply ty_sub with (open_typ_p (pvar eq) (open_rec_typ_p 1 (pvar env) T))
        end.
        -- apply ty_rec_elim. crush.
           apply ty_sub with (pvar env ↓ GN Eq).
           ++ var_subtyp2.
              solve_subtyp_and.
           ++ subsel1.
              var_subtyp_mu2.
              solve_subtyp_and.
        -- crush.
      * var_subtyp2.
        auto.
    + crush.
      apply_fresh ty_let as case0.
      * apply_fresh ty_all_intro as eq_ev.
        instantiate (1:=(pvar TL ↓ GenT)).
        crush.
        cleanup.
        apply_fresh ty_let as BTL.
        1: {
          apply_fresh ty_let as BTLtmp.
          - apply_fresh ty_new_intro as BTLself.
            crush.
          - instantiate (1:={Bi 1 == pvar B ↓ GenT}).
            crush. var_subtyp_mu2.
        }

        crush. cleanup.
        apply_fresh ty_let as res.
        -- eapply ty_all_elim.
           fold ((pvar env) • refl).
           apply ty_new_elim.
           var_subtyp_mu2.
           var_subtyp2.
           apply subtyp_typ; auto.
        -- crush.

           match goal with
           | [ |- ?GG ⊢ ?t : ?T ] =>
             remember GG as G
           end.

           assert (EB: G ⊢ pvar BTL ↓ Bi 1 =:= pvar B ↓ GenT).
           1: {
             constructor;
             [ subsel1 | subsel2 ];
             rewrite HeqG;
             auto.
           }

           assert (Heqev: G ⊢ pvar eq_ev : (((((pvar env ↓ GN Eq) ∧ {Bi 1 >: ⊥ <: ⊤}) ∧ {Ai 1 == pvar eq_ev ↓ Bi 1}) ∧ {Ai 2 == pvar eq_ev ↓ Bi 1}) ∧ {data ⦂ pvar lib ↓ Unit})).
           1: {
             rewrite HeqG.
             match goal with
             | [ |- ?G ⊢ ?t : ?T ] =>
               match goal with
               | [ |- context [{GC Eq 0 == μ ?U}] ] =>
                 assert (HR: T = open_typ_p (pvar eq_ev) (open_rec_typ_p 1 (pvar env) U)) by crush
               end
             end.
             rewrite HR.
             apply ty_rec_elim. crush.
             apply ty_sub with (pvar env ↓ GC Eq 0).
             - var_subtyp; crush; apply ty_var; solve_bind.
             - subsel1.
               match goal with
               | [ |- context [ env ~ μ ?T ] ] =>
                 apply ty_sub with (open_typ_p (pvar env) T)
               end.
               + apply ty_rec_elim. apply ty_var.
                 solve_bind.
               + crush.
                 solve_subtyp_and.
           }

           assert (EQA1A2: G ⊢ pvar eq ↓ Ai 1 =:= pvar eq ↓ Ai 2).
           1: {
             apply eq_transitive with (pvar eq_ev ↓ Ai 1).
             1: {
               rewrite HeqG.
               eapply swap_typ.
               - var_subtyp2.
                 solve_subtyp_and.
               - apply ty_var. solve_bind.
             }

             apply eq_transitive with (pvar eq_ev ↓ Ai 2).
             2: {
               apply eq_symmetry.
               rewrite HeqG.
               eapply swap_typ.
               - var_subtyp2.
                 solve_subtyp_and.
               - apply ty_var. solve_bind.
             }

             apply eq_transitive with (pvar eq_ev ↓ Bi 1).
             - apply eq_symmetry.
               apply eq_sel.
               eapply ty_sub.
               + apply Heqev.
               + solve_subtyp_and.
             - apply eq_sel.
               eapply ty_sub.
               + apply Heqev.
               + solve_subtyp_and.
           }

           match goal with
           | [ _: context [eq ~ ((?T ∧ typ_rcd {Ai 1 == ?X}) ∧ typ_rcd {Ai 2 == ?Y})] |- _ ] =>
             assert (EQ_TUP: G ⊢ X =:= Y)
           end.
           1: {

             apply eq_transitive with (pvar eq ↓ Ai 1).
             1: {
               apply eq_sel.
               rewrite HeqG.
               var_subtyp2.
               solve_subtyp_and.
             }

             apply eq_transitive with (pvar eq ↓ Ai 2).
             2: {
               apply eq_symmetry.
               apply eq_sel.
               rewrite HeqG.
               var_subtyp2.
               solve_subtyp_and.
             }

             apply EQA1A2.
           }

           match goal with
           | _: context [{Tuple == ?T}] |- _ =>
             remember T as TupleDef
           end.


           assert (LIB_EQ: G ⊢ pvar lib ↓ Tuple =:= TupleDef).
           1: {
             apply eq_symmetry.
             apply eq_sel.
             rewrite HeqTupleDef in *.
             rewrite HeqG.
             var_subtyp_mu2.
             - rewrite Heqlib; rewrite Heqenv. clear; lets*: neq_lib_env.
             - solve_subtyp_and.
           }

           assert (EQ2: G ⊢ (TupleDef ∧ {T1 == pvar B ↓ GenT}) ∧ {T2 == pvar D ↓ GenT} =:=
                            (TupleDef ∧ {T1 == pvar A ↓ GenT}) ∧ {T2 == pvar C ↓ GenT}).
           1: {
             rewrite HeqTupleDef in *.

             eapply eq_transitive with (((pvar lib ↓ Tuple) ∧ {T1 == pvar B ↓ GenT}) ∧ {T2 == pvar D ↓ GenT}).
             - eapply eq_transitive.
               + apply eq_symmetry; apply eq_and_assoc.
               + apply eq_symmetry.
                 eapply eq_transitive.
                 apply eq_symmetry.
                 apply eq_and_assoc.
                 apply~ eq_and_merge.
             - eapply eq_transitive with (((pvar lib ↓ Tuple) ∧ {T1 == pvar A ↓ GenT}) ∧ {T2 == pvar C ↓ GenT}); auto.
               eapply eq_transitive.
               + apply eq_symmetry.
                 apply eq_and_assoc.
               + apply eq_symmetry.
                 eapply eq_transitive.
                 apply eq_symmetry.
                 apply eq_and_assoc.
                 apply~ eq_and_merge.
                 apply~ eq_symmetry.
           }

           rewrite HeqTupleDef in *.

           assert (G ⊢ pvar A ↓ GenT =:= pvar B ↓ GenT).
           1: {
             apply eq_symmetry.
             lets INV: eq_inv EQ2.
             apply INV.
             - eexists.
               apply~ rcd_andl.
               + apply~ rcd_andr.
                 unfold disjoint.
                 apply fset_extens; intros x H.
                 * rewrite in_inter in H.
                   destruct H as [H1 H2].
                   trivial.
                 * rewrite in_empty in H.
                   contradiction.
               + unfold disjoint.
                 apply fset_extens; intros x H.
                 * rewrite in_inter in H.
                   destruct H as [H1 H2].
                   rewrite in_union in H1.
                   destruct H1; auto.
                   rewrite in_singleton in H.
                   rewrite in_singleton in H2.
                   subst.
                   lets*: diff.
                 * rewrite in_empty in H.
                   contradiction.
             - eexists.
               apply~ rcd_andl.
               + apply~ rcd_andr.
                 unfold disjoint.
                 apply fset_extens; intros x H.
                 * rewrite in_inter in H.
                   destruct H as [H1 H2].
                   trivial.
                 * rewrite in_empty in H.
                   contradiction.
               + unfold disjoint.
                 apply fset_extens; intros x H.
                 * rewrite in_inter in H.
                   destruct H as [H1 H2].
                   rewrite in_union in H1.
                   destruct H1; auto.
                   rewrite in_singleton in H.
                   rewrite in_singleton in H2.
                   subst.
                   lets*: diff.
                 * rewrite in_empty in H.
                   contradiction.
           }

           assert (EA: G ⊢ pvar BTL ↓ Bi 1 =:= pvar A ↓ GenT).
           1: {
             apply eq_transitive with (pvar B ↓ GenT);
             auto using eq_symmetry.
           }

           rewrite HeqG.
           var_subtyp2.
           subsel2.
           var_subtyp2.
           rewrite <- HeqG.
           destruct EA; destruct EB.
           apply subtyp_typ;
             repeat apply intersection_order; auto.
      * crush.
        cleanup.
        instantiate (1:=(pvar TL ↓ GenT)).
        assert (HR: (pvar TL ↓ GenT) = open_typ_p (pvar case0) (pvar TL ↓ GenT)) by crush.
        rewrite HR.
        eapply ty_all_elim; crush.
  - crush. cleanup.
    var_subtyp2.
    subsel1.
    apply ty_var; solve_bind.
Qed.
