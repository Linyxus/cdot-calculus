(*
This file shows typing of functions using the Eq GADT defined in TestEqualityEnv.v.

The functions are:
coerce : forall a b, Eq a b -> a -> b
transitivity : forall a b c, Eq a b -> Eq b c -> Eq a c
*)
Require Import Helpers.
Require Import Library.
Require Import TestHelpers.
Require Import GMu.TestEquality.
Require Import Translation.
Require Import Top.TestEqualityEnv.

Definition p_coerce_typ : typ :=
  translateTyp0 coerce_typ.


(* lib and env cannot escape, but then we cannot really type the outer program... *)

(*
Definition coerce_trm : trm :=
  Λ (* A *) => Λ (* B *) =>
  λ (* eq: Eq A B *) γ(##1, ##0) Eq =>
  λ (* x : A *) ##1 =>
  case #1 (* eq *) as Eq of {
                   (* a' *) 1 (* _: unit *) => #1 (* x *)
                }.
 *)
Eval cbv in p_coerce_typ.
(*
     = ∀ ({GenT >: ⊥ <: ⊤}) (∀ ({GenT >: ⊥ <: ⊤}) (
         ∀ (((pvar env ↓ GN Eq) ∧ {Ai 1 == this ↓ GenT}) ∧ {Ai 2 == super ↓ GenT})
           (∀ (ssuper ↓ GenT) (ssuper ↓ GenT))))
     : typ
 *)


Definition p_coerce_trm : trm :=
  λ ({GenT >: ⊥ <: ⊤}) λ ({GenT >: ⊥ <: ⊤})
    λ (((pvar env ↓ GN Eq) ∧ {Ai 1 == this ↓ GenT}) ∧ {Ai 2 == super ↓ GenT})
    λ (ssuper ↓ GenT)
    trm_let
    (TLgen (ref 2 ↓ GenT))
    (trm_path ssuper • pmatch $ trm_path this $ (λ (pvar env ↓ GC Eq 0 ∧ {{ssuper}}) trm_path ssuper)).

Lemma p_coerce_types :
  empty & lib ~ libType
  & env ~ (open_typ_p (pvar lib) env_typ)
        ⊢
        p_coerce_trm : p_coerce_typ.
Proof.
  remember lib as lib.
  remember env as env.
  intros.
  cbv.
  crush.
  apply_fresh ty_all_intro as A; crush.
  apply_fresh ty_all_intro as B; crush.
  apply_fresh ty_all_intro as eq; crush.
  apply_fresh ty_all_intro as x; crush.
  apply_fresh ty_let as TL; crush.
  - instantiate (1:= {GenT == pvar B ↓ GenT}).
    apply_fresh ty_let as μt.
    + apply_fresh ty_new_intro as μs; crush.
    + crush.
      assert (HR: open_typ_p (pvar μt) {GenT == pvar B ↓ GenT} = {GenT == pvar B ↓ GenT}) by crush.
      rewrite <- HR at 2.
      apply ty_rec_elim. crush.
  - cleanup.
    apply_fresh ty_let as app_tmp1; crush.
    + instantiate (1:= open_typ_p (pvar TL) (∀ ( ∀ (pvar env ↓ GC Eq 0 ∧ {{pvar eq}} ) (super ↓ GenT) ) (super ↓ GenT))).

      eapply ty_all_elim.
      2: {
        apply ty_var. crush.
      }
      assert (HR: p_sel (avar_f eq) [pmatch] = (pvar eq) • pmatch) by crush.
        rewrite HR.

        match goal with
        | [ |- ?G ⊢ ?t : ∀ (?T) ?U ] =>
          apply ty_sub with (∀ ({GenT >: ⊥ <: ⊤}) U)
        end.
        --
          apply ty_new_elim.
          apply ty_sub with (open_typ_p (pvar eq) (({Ai 1 >: ⊥ <: ⊤} ∧ {Ai 2 >: ⊥ <: ⊤})
        ∧ {pmatch
          ⦂ ∀ ({GenT >: ⊥ <: ⊤}) (∀ (∀ ((pvar env ↓ GC Eq 0) ∧ {{super}})
                                       (super ↓ GenT)) (super ↓ GenT) ) })).
          ++ apply ty_rec_elim.
             apply ty_sub with (pvar env ↓ GN Eq).
             ** var_subtyp; crush.
                repeat rewrite <- Heqenv.
                solve_subtyp_and.
             ** eapply subtyp_sel1.
                match goal with
                | [ |- context [ env ~ μ ?T ] ] =>
                  apply ty_sub with (open_typ_p (pvar env) T)
                end.
                *** apply ty_rec_elim. apply ty_var.
                    solve_bind.
                *** crush.
                    eapply subtyp_trans; try apply subtyp_and11.
          ++ crush.
        -- apply_fresh subtyp_all as TLL; crush.
    + apply_fresh ty_let as c0case; crush.
      1: {
        instantiate (1:= ∀ (pvar env ↓ GC Eq 0 ∧ {{pvar eq}} ) (pvar TL ↓ GenT) ).
        repeat rewrite <- Heqenv.
        apply_fresh ty_all_intro as eq_ev; crush.
        apply ty_sub with (pvar A ↓ GenT).
        * apply ty_var. crush.
        * apply subtyp_trans with (pvar B ↓ GenT).
          2: {
            eapply subtyp_sel2.
            crush.
          }
          apply subtyp_trans with (pvar eq_ev ↓ Bi 1).
          -- apply subtyp_trans with (pvar eq ↓ Ai 2).
             ++ eapply subtyp_sel2.
                var_subtyp; crush.
                apply ty_var. solve_bind.
             ++ apply subtyp_trans with (pvar eq_ev ↓ Ai 2).
                ** eapply subtyp_sngl_qp with (p := pvar eq_ev) (q := pvar eq);
                     try solve [var_subtyp; crush; apply ty_var; solve_bind].
                   assert (HR: pvar eq_ev = (pvar eq_ev) •• []) by crush.
                   rewrite HR at 2.
                   assert (HR2: pvar eq = (pvar eq) •• []) by crush.
                   rewrite HR2 at 2.
                   apply rpath.
                ** eapply subtyp_sel1.
                   apply ty_sub with (((((pvar env ↓ GN Eq) ∧ {Bi 1 >: ⊥ <: ⊤}) ∧ {Ai 1 == pvar eq_ev ↓ Bi 1}) ∧ {Ai 2 == pvar eq_ev ↓ Bi 1}) ∧ {data ⦂ pvar lib ↓ Unit}).
                   ---
                     assert (HR:
                               ((((pvar env ↓ GN Eq) ∧ {Bi 1 >: ⊥ <: ⊤}) ∧ {Ai 1 == pvar eq_ev ↓ Bi 1})
                                ∧ {Ai 2 == pvar eq_ev ↓ Bi 1}) ∧ {data ⦂ pvar lib ↓ Unit}
                                                                 =
                                                                 open_typ_p (pvar eq_ev) (((((pvar env ↓ GN Eq) ∧ {Bi 1 >: ⊥ <: ⊤}) ∧ {Ai 1 == this ↓ Bi 1}) ∧ {Ai 2 == this ↓ Bi 1}) ∧ {data ⦂ pvar lib ↓ Unit})) by crush.
                     rewrite HR.
                     apply ty_rec_elim.
                     apply ty_sub with (pvar env ↓ GC Eq 0).
                     +++ var_subtyp; crush.
                     +++ eapply subtyp_sel1.
                         match goal with
                         | [ |- context [ env ~ μ ?T ] ] =>
                           apply ty_sub with (open_typ_p (pvar env) T)
                         end.
                         *** apply ty_rec_elim. apply ty_var.
                             solve_bind.
                         *** crush.
                             eapply subtyp_trans; try apply subtyp_and11.
                             apply subtyp_and12.
                   --- eapply subtyp_trans; try apply subtyp_and11.
                       apply subtyp_and12.
          -- apply subtyp_trans with (pvar eq ↓ Ai 1).
             ++ apply subtyp_trans with (pvar eq_ev ↓ Ai 1).
                ** subsel2.
                   apply ty_sub with (((((pvar env ↓ GN Eq) ∧ {Bi 1 >: ⊥ <: ⊤}) ∧ {Ai 1 == pvar eq_ev ↓ Bi 1}) ∧ {Ai 2 == pvar eq_ev ↓ Bi 1}) ∧ {data ⦂ pvar lib ↓ Unit}).
                   ---
                     assert (HR:
                               ((((pvar env ↓ GN Eq) ∧ {Bi 1 >: ⊥ <: ⊤}) ∧ {Ai 1 == pvar eq_ev ↓ Bi 1})
                                ∧ {Ai 2 == pvar eq_ev ↓ Bi 1}) ∧ {data ⦂ pvar lib ↓ Unit}
                                                                 =
                                                                 open_typ_p (pvar eq_ev) (((((pvar env ↓ GN Eq) ∧ {Bi 1 >: ⊥ <: ⊤}) ∧ {Ai 1 == this ↓ Bi 1}) ∧ {Ai 2 == this ↓ Bi 1}) ∧ {data ⦂ pvar lib ↓ Unit})) by crush.
                     rewrite HR.
                     apply ty_rec_elim.
                     apply ty_sub with (pvar env ↓ GC Eq 0).
                     +++ var_subtyp; crush.
                     +++ eapply subtyp_sel1.
                         match goal with
                         | [ |- context [ env ~ μ ?T ] ] =>
                           apply ty_sub with (open_typ_p (pvar env) T)
                         end.
                         *** apply ty_rec_elim. apply ty_var.
                             solve_bind.
                         *** crush.
                             eapply subtyp_trans; try apply subtyp_and11.
                             apply subtyp_and12.
                   --- solve_subtyp_and.
                ** eapply subtyp_sngl_pq with (p := pvar eq_ev) (q := pvar eq);
                     try solve [var_subtyp; crush; apply ty_var; solve_bind].
                   assert (HR: pvar eq_ev = (pvar eq_ev) •• []) by crush.
                   rewrite HR at 2.
                   assert (HR2: pvar eq = (pvar eq) •• []) by crush.
                   rewrite HR2 at 2.
                   apply rpath.
             ++ eapply subtyp_sel1.
                var_subtyp; crush; try (apply ty_var; solve_bind).
                eapply subtyp_trans; try apply subtyp_and11.
                apply subtyp_and12.
      }

      crush.
      apply ty_sub with (pvar TL ↓ GenT); crush.
      * assert (HR: open_typ_p (pvar c0case) (pvar TL ↓ GenT) = pvar TL ↓ GenT) by crush.
        rewrite <- HR.
        eapply ty_all_elim; crush.
      * crush.
        eapply subtyp_sel1.
        crush.
Qed.

Definition p_transitivity_typ : typ := translateTyp0 transitivity_typ.

Eval cbv in p_transitivity_typ.
(*
     = ∀ ({GenT >: ⊥ <: ⊤}) (∀ ({GenT >: ⊥ <: ⊤}) (∀ ({GenT >: ⊥ <: ⊤})
        (∀ (((pvar env ↓ GN Eq) ∧ {Ai 1 == super ↓ GenT}) ∧ {Ai 2 == ssuper ↓ GenT})
         (∀ (((pvar env ↓ GN Eq) ∧ {Ai 1 == super ↓ GenT}) ∧ {Ai 2 == ssuper ↓ GenT})
           (((pvar env ↓ GN Eq) ∧ {Ai 1 == ssuper ↓ GenT}) ∧ {Ai 2 == ssssuper ↓ GenT})))))
     : Target.typ
 *)

Definition p_transitivity_trm : trm :=
  λ (*A*) ({GenT >: ⊥ <: ⊤}) λ (*B*) ({GenT >: ⊥ <: ⊤}) λ (*C*) ({GenT >: ⊥ <: ⊤})
    λ (*eq1*) (((pvar env ↓ GN Eq) ∧ {Ai 1 == (* B *) ref 1 ↓ GenT}) ∧ {Ai 2 == (* A *) ref 2 ↓ GenT})
    λ (*eq2*) (((pvar env ↓ GN Eq) ∧ {Ai 1 == (* C *) ref 1 ↓ GenT}) ∧ {Ai 2 == (* B *) ref 2 ↓ GenT})
    trm_let
    (* TL = *)
    (TLgen (((pvar env ↓ GN Eq) ∧ {Ai 1 == (* C *) ref 2 ↓ GenT}) ∧ {Ai 2 == (* A *) ref 4 ↓ GenT}))
    (let_trm (
      (ref 2) • pmatch $ ref 0 $
              (λ (*eq1_ev *) (pvar env ↓ GC Eq 0 ∧ {{ ref 2 }})
                 (ref 2) • pmatch $ ref 1 $
                 (λ (*eq2_ev *) (pvar env ↓ GC Eq 0 ∧ {{ ref 2 }})
                    ((pvar env) • refl $$ (let_trm (ν({Bi 1 == ref 6 ↓ GenT}) {( {Bi 1 ⦂= ref 6 ↓ GenT} )} )))
                 )
              )
    ))
.

Lemma p_transitivity_types :
  empty & lib ~ libType
  & env ~ (open_typ_p (pvar lib) env_typ)
        ⊢
        p_transitivity_trm : p_transitivity_typ.
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
  apply_fresh ty_all_intro as eq1; crush.
  apply_fresh ty_all_intro as eq2; crush.
  apply_fresh ty_let as TL; crush.
  1: {
    instantiate (1:= {GenT == (pvar env ↓ GN Eq) ∧ {Ai 1 == pvar C ↓ GenT} ∧ {Ai 2 == (pvar A) ↓ GenT } }).
    apply_fresh ty_let as TLlet.
    - apply_fresh ty_new_intro as TLself; crush.
    - crush.
      match goal with
      | [ |- ?G ⊢ ?t : ?T ] =>
        assert (HR: open_typ_p (pvar TLlet) T = T) by crush;
          rewrite <- HR;
          clear HR
      end.
      apply ty_rec_elim.
      rewrite <- Heqenv.
      apply ty_var.
      solve_bind.
  }

  apply_fresh ty_let as res.
  - apply_fresh ty_let as e1app1; crush.
    1: {
      eapply ty_all_elim.
      - assert (HR: p_sel (avar_f eq1) [pmatch] = (pvar eq1) • pmatch) by crush.
        rewrite HR.
        apply ty_new_elim.
        apply ty_sub with (open_typ_p (pvar eq1) (({Ai 1 >: ⊥ <: ⊤} ∧ {Ai 2 >: ⊥ <: ⊤})
                                                 ∧ {pmatch
                                                      ⦂ ∀ ({GenT >: ⊥ <: ⊤}) (∀ (∀ ((pvar env ↓ GC Eq 0) ∧ {{super}})
                                                                                   (super ↓ GenT)) (super ↓ GenT) ) })).
        + apply ty_rec_elim.
          apply ty_sub with (pvar env ↓ GN Eq).
          * var_subtyp; crush.
            repeat rewrite <- Heqenv.
            eapply subtyp_trans; apply subtyp_and11.
          * eapply subtyp_sel1.
            match goal with
            | [ |- context [ env ~ μ ?T ] ] =>
              apply ty_sub with (open_typ_p (pvar env) T)
            end.
            -- apply ty_rec_elim. apply ty_var.
               solve_bind.
            -- crush. solve_subtyp_and.
        + crush.
      - eapply ty_sub.
        + apply ty_var. solve_bind.
        + apply~ subtyp_typ.
    }

    crush.
    apply_fresh ty_let as case1.
    + match goal with
      | [ |- context [ e1app1 ~ ∀ (?A) ?B ] ] =>
        instantiate (1:=A)
      end.
      rewrite <- Heqenv.
      apply_fresh ty_all_intro as eq_ev1.
      crush.
      apply_fresh ty_let as e2app1.
      1: {
        eapply ty_all_elim.
        - assert (HR: p_sel (avar_f eq2) [pmatch] = (pvar eq2) • pmatch) by crush.
          rewrite HR.
          apply ty_new_elim.
          apply ty_sub with (open_typ_p (pvar eq2) (({Ai 1 >: ⊥ <: ⊤} ∧ {Ai 2 >: ⊥ <: ⊤})
                                                    ∧ {pmatch
                                                         ⦂ ∀ ({GenT >: ⊥ <: ⊤}) (∀ (∀ ((pvar env ↓ GC Eq 0) ∧ {{super}})
                                                                                      (super ↓ GenT)) (super ↓ GenT) ) })).
          + apply ty_rec_elim.
            apply ty_sub with (pvar env ↓ GN Eq).
            * var_subtyp; crush.
              repeat rewrite <- Heqenv.
              solve_subtyp_and.
            * eapply subtyp_sel1.
              match goal with
              | [ |- context [ env ~ μ ?T ] ] =>
                apply ty_sub with (open_typ_p (pvar env) T)
              end.
              -- apply ty_rec_elim. apply ty_var.
                 solve_bind.
              -- crush.
                 solve_subtyp_and.
          + crush.
        - eapply ty_sub.
          + apply ty_var. solve_bind.
          + apply~ subtyp_typ.
      }

      crush.
      apply_fresh ty_let as case2.
      * match goal with
        | [ |- context [ e2app1 ~ ∀ (?A) ?B ] ] =>
          instantiate (1:=A)
        end.
        apply_fresh ty_all_intro as eq_ev2.
        crush.
        apply_fresh ty_let as BLT.
        1: {
          instantiate (1:={Bi 1 == pvar C ↓ GenT}).
          apply_fresh ty_let as BLTlet.
          - apply_fresh ty_new_intro as BLTself.
            crush.
          - crush.
            match goal with
            | [ |- ?G ⊢ ?t : ?T ] =>
              assert (HR: open_typ_p (pvar BLTlet) T = T) by crush;
                rewrite <- HR;
                clear HR
            end.
            apply ty_rec_elim.
            apply ty_var.
            solve_bind.
        }

        crush.
        apply_fresh ty_let as res.
        1: {
          eapply ty_all_elim.
          - match goal with
            | [ |- context [ { refl ⦂ ∀ (?T) ?U } ]] =>
              instantiate (1:=open_rec_typ_p 1 (pvar env) U);
                instantiate (1:=T);
                crush
            end.
            assert (HR: p_sel (avar_f env) [refl] = (pvar env) • refl) by crush;
              rewrite HR;
              clear HR.
            apply ty_new_elim.
            match goal with
            | [ |- context [ env ~ μ ?T ] ] =>
              apply ty_sub with (open_typ_p (pvar env) T)
            end.
            + apply ty_rec_elim.
              apply ty_var; solve_bind.
            + crush.
          - apply ty_sub with ({Bi 1 == pvar C ↓ GenT}).
            + assert (HR: typ_rcd {Bi 1 == pvar C ↓ GenT} = open_typ_p (pvar BLT) ({Bi 1 == pvar C ↓ GenT})) by crush.
              rewrite HR.
              apply ty_rec_elim.
              crush.
            + apply~ subtyp_typ.
        }

        crush.
        apply ty_sub with ((pvar env ↓ GN Eq) ∧ {Ai 1 == pvar C ↓ GenT} ∧ {Ai 2 == pvar A ↓ GenT}).
        -- var_subtyp; crush.
           match goal with
           | [ |- ?GG ⊢ ?A <: ?T ] =>
             remember GG as G
           end.
           assert (HBLTC: G ⊢ pvar BLT ↓ Bi 1 =:= pvar C ↓ GenT).
           1: {
             rewrite HeqG.
             constructor.
             - subsel1. apply ty_var; solve_bind.
             - subsel2. apply ty_var; solve_bind.
           }

           destruct HBLTC.
           repeat apply~ intersection_order.

           assert (G ⊢ pvar A ↓ GenT =:= pvar B ↓ GenT).
           1: {
             assert (Hev1: G ⊢ pvar eq_ev1 : (((((pvar env ↓ GN Eq) ∧ {Bi 1 >: ⊥ <: ⊤}) ∧ {Ai 1 == pvar eq_ev1 ↓ Bi 1}) ∧ {Ai 2 == pvar eq_ev1 ↓ Bi 1}) ∧ {data ⦂ pvar lib ↓ Unit})).
             1: {
               rewrite HeqG.
               match goal with
               | [ |- ?G ⊢ ?t : ?T ] =>
                 match goal with
                 | [ |- context [{GC Eq 0 == μ ?U}] ] =>
                   assert (HR: T = open_typ_p (pvar eq_ev1) (open_rec_typ_p 1 (pvar env) U)) by crush
                 end
               end.
               rewrite HR.
               apply ty_rec_elim. crush.
               apply ty_sub with (pvar env ↓ GC Eq 0).
               - var_subtyp; crush; apply ty_var; solve_bind.
               - subsel1.
                 var_subtyp_mu2.
                 solve_subtyp_and.
             }

             assert (G ⊢ pvar A ↓ GenT =:= pvar eq_ev1 ↓ Bi 1).
             1: {
               apply eq_transitive with (pvar eq1 ↓ Ai 2).
               - apply eq_sel.
                 rewrite HeqG; var_subtyp_bind.
               - apply eq_transitive with (pvar eq_ev1 ↓ Ai 2).
                 + rewrite HeqG.
                   eapply swap_typ.
                   * var_subtyp_bind.
                   * apply ty_var; solve_bind.
                 + apply eq_symmetry.
                   apply eq_sel.
                   eapply ty_sub.
                   * apply Hev1.
                   * solve_subtyp_and.
             }

             assert (G ⊢ pvar eq_ev1 ↓ Bi 1 =:= pvar B ↓ GenT).
             1: {
               apply eq_transitive with (pvar eq1 ↓ Ai 1).
               - apply eq_transitive with (pvar eq_ev1 ↓ Ai 1).
                 + apply eq_sel.
                   eapply ty_sub.
                   * apply Hev1.
                   * solve_subtyp_and.
                 + rewrite HeqG.
                   apply eq_symmetry.
                   eapply swap_typ.
                   * var_subtyp_bind.
                   * apply ty_var; solve_bind.
               - apply eq_symmetry.
                 apply eq_sel.
                 rewrite HeqG; var_subtyp_bind.
             }

             eapply eq_transitive with (pvar eq_ev1 ↓ Bi 1); auto.
           }

           assert (G ⊢ pvar B ↓ GenT =:= pvar C ↓ GenT).
           1: {
             assert (Hev2: G ⊢ pvar eq_ev2 : (((((pvar env ↓ GN Eq) ∧ {Bi 1 >: ⊥ <: ⊤}) ∧ {Ai 1 == pvar eq_ev2 ↓ Bi 1}) ∧ {Ai 2 == pvar eq_ev2 ↓ Bi 1}) ∧ {data ⦂ pvar lib ↓ Unit})).
             1: {
               rewrite HeqG.
               match goal with
               | [ |- ?G ⊢ ?t : ?T ] =>
                 match goal with
                 | [ |- context [{GC Eq 0 == μ ?U}] ] =>
                   assert (HR: T = open_typ_p (pvar eq_ev2) (open_rec_typ_p 1 (pvar env) U)) by crush
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

             assert (G ⊢ pvar B ↓ GenT =:= pvar eq_ev2 ↓ Bi 1).
             1: {
               apply eq_transitive with (pvar eq2 ↓ Ai 2).
               - apply eq_sel.
                 rewrite HeqG; var_subtyp_bind.
               - apply eq_transitive with (pvar eq_ev2 ↓ Ai 2).
                 + rewrite HeqG.
                   eapply swap_typ.
                   * var_subtyp_bind.
                   * apply ty_var; solve_bind.
                 + apply eq_symmetry.
                   apply eq_sel.
                   eapply ty_sub.
                   * apply Hev2.
                   * solve_subtyp_and.
             }

             assert (G ⊢ pvar eq_ev2 ↓ Bi 1 =:= pvar C ↓ GenT).
             1: {
               apply eq_transitive with (pvar eq2 ↓ Ai 1).
               - apply eq_transitive with (pvar eq_ev2 ↓ Ai 1).
                 + apply eq_sel.
                   eapply ty_sub.
                   * apply Hev2.
                   * solve_subtyp_and.
                 + rewrite HeqG.
                   apply eq_symmetry.
                   eapply swap_typ.
                   * var_subtyp_bind.
                   * apply ty_var; solve_bind.
               - apply eq_symmetry.
                 apply eq_sel.
                 rewrite HeqG; var_subtyp_bind.
             }

             eapply eq_transitive with (pvar eq_ev2 ↓ Bi 1); auto.
           }

           assert (Hfin: G ⊢ pvar BLT ↓ Bi 1 =:= pvar A ↓ GenT).
           1: {
             apply eq_transitive with (pvar C ↓ GenT); auto.
             apply eq_transitive with (pvar B ↓ GenT); auto using eq_symmetry.
           }

           destruct Hfin.
           apply~ subtyp_typ.
        -- eapply subtyp_sel2.
           apply ty_var; solve_bind.
      * crush.
        match goal with
        | [ |- ?G ⊢ ?e : ?T ] =>
          assert (HR: T = open_typ_p (pvar case2) T) by crush;
            rewrite HR;
            clear HR
        end.
        eapply ty_all_elim;
          apply ty_var; solve_bind.
    + crush.
      match goal with
      | [ |- context [ e1app1 ~ ∀ (?A) ?B ] ] =>
        instantiate (1:=B)
      end.
      match goal with
      | [ |- ?G ⊢ ?e : ?T ] =>
        assert (HR: T = open_typ_p (pvar case1) T) by crush;
          rewrite HR;
          clear HR
      end.
      eapply ty_all_elim;
        apply ty_var; solve_bind.
  - crush.
    eapply ty_sub.
    + apply ty_var; solve_bind.
    + eapply subtyp_sel1.
      rewrite <- Heqenv.
      crush.
Qed.
