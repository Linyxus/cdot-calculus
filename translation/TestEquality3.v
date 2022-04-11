(*
This file shows typing of functions using the Eq GADT defined in TestEqualityEnv.v.

The functions are:
construct : forall a b c d, Eq a c -> Eq b d -> Eq (a * b) (c * d)
*)
Require Import Helpers.
Require Import Library.
Require Import TestHelpers.
Require Import GMu.TestEquality.
Require Import Translation.
Require Import Top.TestEqualityEnv.

Lemma construct_tuple_lemma : forall G A B C D,
    G ⊢ A =:= C ->
    G ⊢ B =:= D ->
    G ⊢ (pvar lib) ↓ Tuple ∧ {T1 == A} ∧ {T2 == B} =:= (pvar lib) ↓ Tuple ∧ {T1 == C} ∧ {T2 == D}.
Proof.
  introv [] [].
  repeat apply~ eq_and_merge.
Qed.

Definition p_construct_typ : typ :=
  translateTyp0 construct_typ.

Eval cbv in p_construct_typ.
(*
	 = ∀ ({GenT >: ⊥ <: ⊤}) (∀ ({GenT >: ⊥ <: ⊤})
                             (∀ ({GenT >: ⊥ <: ⊤})
                              (∀ ({GenT >: ⊥ <: ⊤})
                               (∀ (((pvar env ↓ GN Eq)
                                    ∧ {Ai 1 == ssuper ↓ GenT})
                                   ∧ {Ai 2 == sssuper ↓ GenT})
                                (∀ (((pvar env ↓ GN Eq)
                                     ∧ {Ai 1 == super ↓ GenT})
                                    ∧ {Ai 2 == ssuper ↓ GenT})
                                 (((pvar env ↓ GN Eq)
                                   ∧ {Ai 1 ==
                                     ((pvar lib ↓ Tuple)
                                      ∧ {T1 == ssssuper ↓ GenT})
                                     ∧ {T2 == ssuper ↓ GenT}})
                                  ∧ {Ai 2 ==
                                    ((pvar lib ↓ Tuple)
                                     ∧ {T1 == sssssuper ↓ GenT})
                                    ∧ {T2 == sssuper ↓ GenT}}))))))
     : typ
*)

Definition p_construct_trm : trm :=
  λ (*A*) ({GenT >: ⊥ <: ⊤}) λ (*B*) ({GenT >: ⊥ <: ⊤}) λ (*C*) ({GenT >: ⊥ <: ⊤}) λ (*D*) ({GenT >: ⊥ <: ⊤})
    λ (*eq1*) (((pvar env ↓ GN Eq) ∧ {Ai 1 == ssuper ↓ GenT}) ∧ {Ai 2 == sssuper ↓ GenT})
    λ (*eq2*) (((pvar env ↓ GN Eq) ∧ {Ai 1 == super ↓ GenT}) ∧ {Ai 2 == ssuper ↓ GenT})
    trm_let
    (* TL = *)
    (TLgen
      (((pvar env ↓ GN Eq)
      ∧ {Ai 1 ==
        ((pvar lib ↓ Tuple)
        ∧ {T1 == ssssuper ↓ GenT})
        ∧ {T2 == ssuper ↓ GenT} })
    ∧ {Ai 2 ==
      ((pvar lib ↓ Tuple)
        ∧ {T1 == sssssuper ↓ GenT})
      ∧ {T2 == sssuper ↓ GenT} })
    )
    (let_trm (
      (ref 2) • pmatch $ ref 0 $
              (λ (*eq1_ev *) (pvar env ↓ GC Eq 0 ∧ {{ ref 2 }})
                 (ref 2) • pmatch $ ref 1 $
                 (λ (*eq2_ev *) (pvar env ↓ GC Eq 0 ∧ {{ ref 2 }})
                    ((pvar env) • refl $$ (let_trm
                    (let retT := (((pvar lib ↓ Tuple) ∧ {T1 == ref 8 ↓ GenT}) ∧ {T2 == ref 6 ↓ GenT}) in
                    ν({Bi 1 == retT}) {( {Bi 1 ⦂= retT} )} )))
                 )
              )
    ))
.

Lemma p_construct_types :
  empty & lib ~ libType
  & env ~ (open_typ_p (pvar lib) env_typ)
        ⊢
        p_construct_trm : p_construct_typ.
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
  apply_fresh ty_all_intro as eq1; crush.
  apply_fresh ty_all_intro as eq2; crush.
  apply_fresh ty_let as TL; crush.
  1: {
    instantiate (1:=
    {GenT ==
    (((pvar env ↓ GN Eq)
    ∧ {Ai 1 ==
      ((pvar lib ↓ Tuple)
      ∧ {T1 == pvar B ↓ GenT})
      ∧ {T2 == pvar D ↓ GenT} })
  ∧ {Ai 2 ==
    ((pvar lib ↓ Tuple)
      ∧ {T1 == pvar A ↓ GenT})
    ∧ {T2 == pvar C ↓ GenT} })
    }
    ).
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
      rewrite <- Heqlib.
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
          instantiate (1:={Bi 1 == ((pvar Library.lib ↓ Tuple)
          ∧ {T1 == pvar B ↓ GenT})
         ∧ {T2 == pvar D ↓ GenT} }).
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
          - var_subtyp_bind.
            eauto.
        }

        crush.
        match goal with
        | |- context[TL ~ typ_rcd {GenT == ?T} ] =>
          apply ty_sub with T
        end.
        -- var_subtyp; crush.
           match goal with
           | [ |- ?GG ⊢ ?A <: ?T ] =>
             remember GG as G
           end.
           match goal with
           | _: context[BLT ~ typ_rcd {Bi 1 == ?T} ] |- _ =>
           assert (HBLTC: G ⊢ pvar BLT ↓ Bi 1 =:= T)
           end.
           1: {
             rewrite HeqG.
             constructor.
             - subsel1. apply ty_var; solve_bind.
             - subsel2. apply ty_var; solve_bind.
           }
           rewrite <- Heqlib in HBLTC.
           destruct HBLTC.
           repeat apply~ intersection_order.

           assert (G ⊢
                  (pvar lib ↓ Tuple) ∧ (typ_rcd {T1 == pvar B ↓ GenT}) ∧ (typ_rcd {T2 == pvar D ↓ GenT})
                  =:=
                  (pvar lib ↓ Tuple) ∧ (typ_rcd {T1 == pvar A ↓ GenT}) ∧ (typ_rcd {T2 == pvar C ↓ GenT})).
          1: {
            assert (G ⊢ pvar B ↓ GenT =:= pvar A ↓ GenT).
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

             apply eq_symmetry.
             eapply eq_transitive with (pvar eq_ev1 ↓ Bi 1); auto.
            }

            assert (G ⊢ pvar D ↓ GenT =:= pvar C ↓ GenT).
            1: {
              assert (Hev1: G ⊢ pvar eq_ev2 : (((((pvar env ↓ GN Eq) ∧ {Bi 1 >: ⊥ <: ⊤}) ∧ {Ai 1 == pvar eq_ev2 ↓ Bi 1}) ∧ {Ai 2 == pvar eq_ev2 ↓ Bi 1}) ∧ {data ⦂ pvar lib ↓ Unit})).
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
                 var_subtyp_mu2.
                 solve_subtyp_and.
             }

             assert (G ⊢ pvar C ↓ GenT =:= pvar eq_ev2 ↓ Bi 1).
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
                   * apply Hev1.
                   * solve_subtyp_and.
             }

             assert (G ⊢ pvar eq_ev2 ↓ Bi 1 =:= pvar D ↓ GenT).
             1: {
               apply eq_transitive with (pvar eq2 ↓ Ai 1).
               - apply eq_transitive with (pvar eq_ev2 ↓ Ai 1).
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

             apply eq_symmetry.
             eapply eq_transitive with (pvar eq_ev2 ↓ Bi 1); auto.
            }

            rewrite Heqlib.
            apply~ construct_tuple_lemma.
          }

          assert (Hfin: G ⊢ pvar BLT ↓ Bi 1 =:= (pvar lib ↓ Tuple) ∧ (typ_rcd {T1 == pvar A ↓ GenT}) ∧ (typ_rcd {T2 == pvar C ↓ GenT})).
          1: {
            apply eq_transitive with ((pvar lib ↓ Tuple) ∧ (typ_rcd {T1 == pvar B ↓ GenT}) ∧ (typ_rcd {T2 == pvar D ↓ GenT})); auto.
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
     rewrite <- Heqlib.
     crush.
Qed.
