(*
An example showing typing of the `env` term encoding the Eq[A,B] GADT with a single constructor refl[C] extends Eq[C,C].
*)

Require Import Helpers.
Require Import Library.
Require Import TestHelpers.
Require Import GMu.TestEquality.
Require Import Translation.

Axiom gngc_simple : forall x y i, GN x <> GC y i.
Axiom AiBi : forall i j, Ai i <> Bi j.
Axiom AiAi : forall i j, i <> j -> Ai i <> Ai j.
Axiom BiBi : forall i j, i <> j -> Bi i <> Bi j.
Axiom pmatch_data : pmatch <> data.
Parameter snglhelper : trm_label.
Parameter refl : trm_label.

Definition env_pretyp : typ :=
      { GN Eq ==
        μ
          {Ai 1 >: ⊥ <: ⊤} ∧ {Ai 2 >: ⊥ <: ⊤}
        ∧ {pmatch ⦂ ∀ ({GenT >: ⊥ <: ⊤})
                        ∀ ( ∀ (ssuper ↓ GC Eq 0 ∧ {{super}} ) (super ↓ GenT))
                          (super ↓ GenT)
          }
      }
      ∧ { GC Eq 0 ==
          μ
            super ↓ GN Eq
          ∧ {Bi 1 >: ⊥ <: ⊤}
          ∧ {Ai 1 == this ↓ Bi 1} ∧ {Ai 2 == this ↓ Bi 1}
          ∧ {data ⦂ ssuper ↓ Unit}
        }
      ∧ { refl ⦂  ∀ ({Bi 1 >: ⊥ <: ⊤}) ((super ↓ GN Eq) ∧ {Ai 1 == this ↓ Bi 1} ∧ {Ai 2 == this ↓ Bi 1}) }
    (* original construction would require to also take unit here, as the data arg, but that seems unnecessary in this case so we skip it for clarity *)
.

Definition env_typ : typ :=
  μ (env_pretyp).

Definition env_trm : trm :=
  let_trm
    (ν (env_pretyp)
       {(
           { GN Eq ⦂=
             μ
               {Ai 1 >: ⊥ <: ⊤} ∧ {Ai 2 >: ⊥ <: ⊤}
             ∧ {pmatch ⦂ ∀ ({GenT >: ⊥ <: ⊤})
                             ∀ ( ∀ (ssuper ↓ GC Eq 0 ∧ {{super}} ) (super ↓ GenT))
                               (super ↓ GenT)
               }
           },
           { GC Eq 0 ⦂=
             μ
               super ↓ GN Eq
             ∧ {Bi 1 >: ⊥ <: ⊤}
             ∧ {Ai 1 == this ↓ Bi 1} ∧ {Ai 2 == this ↓ Bi 1}
             ∧ {data ⦂ ssuper ↓ Unit}
           },
           { refl :=
               λ ({Bi 1 >: ⊥ <: ⊤}) let_trm (
                   ν(
                       {Ai 1 == this ↓ Bi 1} ∧ {Ai 2 == this ↓ Bi 1}
                       ∧ {pmatch ⦂ ∀ ({GenT >: ⊥ <: ⊤})
                                       ∀ ( ∀ ((ref 3) ↓ GC Eq 0 ∧ {{super}} ) (super ↓ GenT))
                                         (super ↓ GenT)
                         }
                       ∧ {Bi 1 == super ↓ Bi 1}
                       ∧ {data ⦂ {{(ref 3) • mkUnit}} }
                     ) {(
                           {Ai 1 ⦂= this ↓ Bi 1}, (* TODO this or super *)
                           {Ai 2 ⦂= this ↓ Bi 1},
                           {pmatch :=
                              λ ({GenT >: ⊥ <: ⊤})
                                λ ( ∀ ((ref 3) ↓ GC Eq 0 ∧ {{super}} ) (super ↓ GenT))
                                (* TODO may need a let for self *)
                                trm_let
                                (ν({snglhelper ⦂ {{ref 3}} }) {( {snglhelper := ref 3} )})
                                (trm_app super (this • snglhelper))
                           },
                           {Bi 1 ⦂= super ↓ Bi 1},
                           {data := (ref 3) • mkUnit}
                       )}
                 )
           }
       )}
    ).

Lemma env_types : forall lib,
    empty & lib ~ libType ⊢ open_trm_p (pvar lib) env_trm : open_typ_p (pvar lib) env_typ.
Proof.
  intros.
  cbv. crush.
  apply_fresh ty_let as env.
  - apply_fresh ty_new_intro as self_env.
    crush.
    repeat apply ty_defs_cons; try apply ty_defs_one;
      crush.
    1: {
      invert_label.
      false* gngc_simple.
    }

    apply ty_def_all.
    apply_fresh ty_all_intro as BTL. crush.
    cleanup.
    apply_fresh ty_let as res.
    1: {
      apply_fresh ty_new_intro as self_res.
      crush.
      repeat apply ty_defs_cons; try apply ty_defs_one;
        crush.
      - invert_label.
        false* AiAi.
      - apply ty_def_all.
        apply_fresh ty_all_intro as pmTL; crush.
        apply_fresh ty_all_intro as case_refl; crush.
        apply_fresh ty_let as Pself.
        + apply_fresh ty_new_intro as self_helper.
          apply ty_defs_one.
          eapply ty_def_path.
          cbn. apply ty_var. solve_bind.
        + crush.
          fold ((pvar Pself) • snglhelper).
          assert (HR: pvar pmTL ↓ GenT = open_typ_p ((pvar Pself) • snglhelper) (pvar pmTL ↓ GenT)) by crush.
          rewrite HR.
          eapply ty_all_elim.
          * apply ty_var; solve_bind.
          * match goal with
            | [ |- ?G ⊢ ?t : ?A ∧ ?B ] =>
              assert (G ⊢ t : B)
            end.
            1: {
              apply ty_new_elim.
              match goal with
              | [ |- ?G ⊢ ?t : ?T ] =>
                assert (HR2: T = open_typ_p (pvar Pself) T) by crush
              end.
              rewrite HR2.
              apply ty_rec_elim.
              apply ty_var. solve_bind.
            }
            cleanup.
            apply ty_and_intro; auto.
            crush.
            fold ((pvar Pself) • snglhelper).
            apply ty_sngl with (pvar self_res); auto.
            match goal with
            | [ |- context [ {GC Eq 0 == ?T} ] ] =>
              apply ty_sub with T
            end.
            2: {
              subsel2.
              var_subtyp.
              - apply ty_var; solve_bind.
              - solve_subtyp_and.
            }

            apply ty_rec_intro.
            crush.
            repeat apply ty_and_intro;
              try solve [var_subtyp2; solve_subtyp_and].
            -- match goal with
               | [ |- context [ {GN Eq == ?T} ] ] =>
                 apply ty_sub with T
               end.
               ++ apply ty_rec_intro.
                  crush.
                  var_subtyp2.
                  eapply subtyp_trans; try apply subtyp_and11.
                  eapply subtyp_trans; try apply subtyp_and11.
                  repeat apply intersection_order; auto.
               ++ subsel2.
                  var_subtyp.
                  ** apply ty_var; solve_bind.
                  ** solve_subtyp_and.
            -- var_subtyp2.
               eapply subtyp_trans; try apply subtyp_and11.
               eapply subtyp_trans; try apply subtyp_and12.
               apply subtyp_typ; auto.
            -- apply ty_rcd_intro.
               fold ((pvar lib) • mkUnit).
               apply ty_sngl with ((pvar lib) • mkUnit).
               ++ apply ty_new_elim.
                  var_subtyp2.
                  solve_subtyp_and.
               ++ apply ty_new_elim.
                  var_subtyp_mu2.
                  solve_subtyp_and.
      - invert_label.
        false* AiBi.
      - invert_label.
        false* AiBi.
      - eapply ty_def_path.
        fold ((pvar lib) • mkUnit).
        apply ty_new_elim.
        var_subtyp_mu2.
        eapply subtyp_trans; try apply subtyp_and11.
        apply subtyp_and12.
      - invert_label.
        false* pmatch_data.
    }

    crush.
    repeat apply ty_and_intro.
    + match goal with
      | [ |- context [ {GN Eq == ?T} ] ] =>
        apply ty_sub with T
      end.
      * apply ty_rec_intro.
        crush.
        var_subtyp_mu2.
        eapply subtyp_trans; try apply subtyp_and11.
        eapply subtyp_trans; try apply subtyp_and11.
        repeat apply intersection_order; auto.
      * subsel2.
        var_subtyp.
        -- apply ty_var; solve_bind.
        -- solve_subtyp_and.
    + var_subtyp_mu2.
      solve_subtyp_and.
      apply subtyp_typ;
        [subsel2 | subsel1];
        var_subtyp_mu2;
        solve_subtyp_and.
    + var_subtyp_mu2.
      repeat
        match goal with
        | [ |- ?G ⊢ ?A ∧ ?B <: ?C ] =>
          match B with
          | typ_rcd {?N == ?T} =>
            match C with
            | typ_rcd {N == ?U} =>
              eapply subtyp_trans; try apply subtyp_and12
            | _ =>
              eapply subtyp_trans; try apply subtyp_and11
            end
          | C =>
            apply subtyp_and12
          | _ =>
            eapply subtyp_trans; try apply subtyp_and11
          end
        end.
      apply subtyp_typ;
        [subsel2 | subsel1];
        var_subtyp_mu2;
        solve_subtyp_and.
  - crush.
Qed.
