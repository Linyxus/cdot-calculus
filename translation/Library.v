(*
This file shows typing of the `lib` term encoding the primitives of the source calculus into iDOT.
*)
Require Import Helpers.

Parameter Any : typ_label.
Parameter Unit : typ_label.
Parameter Tuple : typ_label.
Parameter GenT : typ_label.
Parameter Ai : nat -> typ_label.
Parameter Bi : nat -> typ_label.
Parameter T1 : typ_label.
Parameter T2 : typ_label.
Parameter fst_v : trm_label.
Parameter snd_v : trm_label.

Parameter GN : Source.GADTName -> typ_label.
Parameter GC : Source.GADTName -> nat -> typ_label.
Parameter data : trm_label.
Parameter mkTuple : trm_label.
Parameter mkUnit : trm_label.
Parameter pmatch : trm_label.
Axiom diff : Unit <> Tuple
             /\ mkUnit <> mkTuple
             /\ T1 <> T2
             /\ fst_v <> snd_v
             /\ Any <> Tuple
             /\ Any <> Unit.

(* Generating some fresh vars *)
Definition lib : var := proj1_sig (var_fresh \{}).
Local Definition envHlp := var_fresh \{lib}.
Definition env : var := proj1_sig envHlp.
Lemma neq_lib_env : lib <> env.
Proof.
  unfold env.
  destruct envHlp.
  cbn.
  auto.
Qed.
#[global] Opaque lib.
#[global] Opaque env.

Definition ref (offset : nat) : path :=
  p_sel (avar_b offset) nil.

Definition tupleTyp : Target.typ :=
  μ (
      { T1 >: ⊥ <: ⊤ } ∧
      { T2 >: ⊥ <: ⊤ } ∧
      { fst_v ⦂ this ↓ T1 } ∧
      { snd_v ⦂ this ↓ T2 }
    ).

Definition GenArgT : Target.typ :=
  typ_rcd { GenT >: ⊥ <: ⊤ }.

Definition libPreTypeHelp (unitDec : dec) : typ :=
  typ_rcd { Any == ⊤ } ∧
  typ_rcd unitDec ∧
  typ_rcd { Tuple == tupleTyp } ∧
  typ_rcd { mkUnit ⦂ this ↓ Unit } ∧
  typ_rcd { mkTuple ⦂
                    ∀ ({ T1 >: ⊥ <: ⊤} ∧ { T2 >: ⊥ <: ⊤ })
                        ∀ ((ref 0) ↓ T1)
                            ∀ ((ref 1) ↓ T2)
                              ((ref 3) ↓ Tuple ∧ { T1 == (ref 2) ↓ T1 } ∧ { T2 == (ref 2) ↓ T2 })
          }.

Definition libPreType : Target.typ :=
  libPreTypeHelp { Unit == { Unit >: ⊥ <: ⊤ } } .

Definition libType : Target.typ :=
  μ (libPreTypeHelp { Unit >: ⊥ <: ⊤ }).

Definition internalTupleTyp :=
  { T1 == (ref 3) ↓ T1 } ∧
  { T2 == (ref 3) ↓ T2 } ∧
  { fst_v ⦂ {{ ref 2 }} } ∧
  { snd_v ⦂ {{ ref 1 }} }.

Definition libInternalType (unitRef : path) :=
  typ_rcd { Any == ⊤ } ∧
  typ_rcd { Unit == { Unit >: ⊥ <: ⊤ } } ∧
  typ_rcd { Tuple == tupleTyp } ∧
  typ_rcd { mkUnit ⦂ μ({Unit == ⊤}) } ∧
  typ_rcd { mkTuple ⦂
                    ∀ ({ T1 >: ⊥ <: ⊤} ∧ { T2 >: ⊥ <: ⊤ })
                        ∀ ((ref 0) ↓ T1)
                            ∀ ((ref 1) ↓ T2)
                              ((ref 3) ↓ Tuple ∧ { T1 == (ref 2) ↓ T1 } ∧ { T2 == (ref 2) ↓ T2 })
          }.

Definition libTrm : Target.trm :=
  (let_trm
     (ν[ref 0 ↘ Any](libInternalType (ref 1)) {(
                           { Any ⦂= ⊤ },
                           { Unit ⦂= { Unit >: ⊥ <: ⊤ } },
                           { Tuple ⦂= tupleTyp },
                           { mkUnit := ν[ref 1 ↘ Unit]({ Unit == ⊤ }) {( {Unit ⦂= ⊤} )} },
                           { mkTuple :=
                               λ ({ T1 >: ⊥ <: ⊤} ∧ { T2 >: ⊥ <: ⊤ })
                                 λ ((ref 0) ↓ T1)
                                 λ ((ref 1) ↓ T2)
                                 let_trm (
                                   ν[ref 4 ↘ Tuple](internalTupleTyp)
                                    {(
                                        {T1 ⦂= (ref 3) ↓ T1},
                                        {T2 ⦂= (ref 3) ↓ T2},
                                        { fst_v := (ref 2) },
                                        { snd_v := (ref 1) }
                                    )}
                                 )
                           }
                        )}
    ))
 .

Lemma libTypes : forall G, G ⊢ libTrm : libType.
Proof.
  intros.
  unfold libTrm. unfold libType.
  let F := gather_vars in
  apply ty_let with F (μ libInternalType this).
  2: {
    unfold libInternalType.
    unfold libPreTypeHelp.
    cbn. case_if.
    introv F.
    apply ty_rec_intro.
    cbn. repeat case_if.
    unfold tupleTyp.
    repeat (apply ty_and_intro; try solve [var_subtyp_mu2; solve_subtyp_and]).
    - var_subtyp_mu2.
      apply subtyp_trans with ({Unit == {Unit >: ⊥ <: ⊤} });
        solve_subtyp_and; auto.
    - apply ty_rcd_intro.
      apply ty_sub with {Unit == ⊤}.
      + cbn.
        assert (HR: typ_rcd {Unit == ⊤} = open_typ_p (p_sel (avar_f x) [mkUnit]) {Unit == ⊤}) by crush;
          rewrite HR; clear HR.
        apply ty_rec_elim.
        assert (HR: (trm_path (pvar x) • mkUnit) = trm_path (p_sel (avar_f x) [mkUnit])) by crush;
          rewrite <- HR; clear HR.
        apply ty_new_elim.
        var_subtyp_mu2. solve_subtyp_and.
      + eapply subtyp_sel2.
        var_subtyp_mu2.
        eapply subtyp_trans; try apply subtyp_and11.
        eapply subtyp_trans; try apply subtyp_and11.
        eapply subtyp_trans; try apply subtyp_and11.
        eapply subtyp_trans; try apply subtyp_and12.
        apply~ subtyp_typ.
  }

  unfold libInternalType.
  cbn.

  apply_fresh ty_new_intro as selfLib;
    cbn; repeat case_if; cleanup.
  2: {
    var_subtyp2.
    apply subtyp_trans with ⊤; auto.
    eapply subtyp_sel2.
    var_subtyp2. solve_subtyp_and.
  }

  repeat constructor; crush;
    try solve [inversions C; lets*: diff].
  - inversions C0; lets*: diff.
  - apply ty_def_new with (pvar selfLib); cbn; auto.
    apply ty_sub with {Unit == ⊤}.
    + assert (HR: typ_rcd {Unit == ⊤} = open_typ_p (p_sel (avar_f selfLib) [mkUnit]) {Unit == ⊤}) by crush;
        rewrite HR; clear HR.
      apply ty_rec_elim.
      assert (HR: (trm_path (pvar selfLib) • mkUnit) = trm_path (p_sel (avar_f selfLib) [mkUnit])) by crush;
        rewrite <- HR; clear HR.
      apply ty_new_elim.
      cbn.
      var_subtyp2. solve_subtyp_and.
    + eapply subtyp_sel2.
      var_subtyp2.
      eapply subtyp_trans; try apply subtyp_and11.
      eapply subtyp_trans; try apply subtyp_and11.
      eapply subtyp_trans; try apply subtyp_and11.
      eapply subtyp_trans; try apply subtyp_and12.
      apply~ subtyp_typ.
  - apply_fresh ty_all_intro as tl.
    apply_fresh ty_all_intro as x1.
    apply_fresh ty_all_intro as x2.
    cbv; repeat case_if; cleanup.
    (* match goal with *)
    (* | [ _: _ |- ?G1 ⊢ ?t : ?T ] => *)
    (*   assert (HTUP: forall tup, *)
    (*       G1 & tup ~ *)
    (*         ((({T1 == pvar tl ↓ T1} ∧ {T2 == pvar tl ↓ T2}) ∧ {fst_v ⦂ {{pvar x1}}}) *)
    (*          ∧ {snd_v ⦂ {{pvar x2}}}) ⊢ tvar tup *)
    (*       : μ (({T1 >: ⊥ <: ⊤} ∧ {T2 >: ⊥ <: ⊤}) ∧ {fst_v ⦂ this ↓ T1}) ∧ {snd_v ⦂ this ↓ T2} *)
    (*     ) *)
    (* end. *)
    eapply ty_let.
    + apply_fresh ty_new_intro as w.
      crush.
      repeat apply ty_defs_cons; try apply ty_defs_one;
        auto; try crush;
          try solve [inversion C; lets*: diff].
      * apply~ ty_def_path.
      * apply~ ty_def_path.
      * crush.
        apply ty_sub with (μ (({T1 >: ⊥ <: ⊤} ∧ {T2 >: ⊥ <: ⊤}) ∧ {fst_v ⦂ this ↓ T1}) ∧ {snd_v ⦂ this ↓ T2}).
        -- apply ty_rec_intro.
           crush.
           repeat apply ty_and_intro.
           ** var_subtyp2.
              solve_subtyp_and.
              apply~ subtyp_typ.
           ** var_subtyp2.
              eapply subtyp_trans; try apply subtyp_and11.
              eapply subtyp_trans; try apply subtyp_and11.
              eapply subtyp_trans; try apply subtyp_and12.
              apply~ subtyp_typ.
           ** apply ty_rcd_intro.
              apply ty_sngl with (pvar x1).
              --- apply ty_new_elim.
                  var_subtyp2.
                  eapply subtyp_trans; try apply subtyp_and11.
                  apply subtyp_and12.
              --- apply ty_sub with (pvar tl ↓ T1); auto.
                  eapply subtyp_sel2.
                  var_subtyp2.
                  eapply subtyp_trans; try apply subtyp_and11.
                  eapply subtyp_trans; apply subtyp_and11.
           ** apply ty_rcd_intro.
              apply ty_sngl with (pvar x2).
              --- apply ty_new_elim.
                  var_subtyp2.
                  apply subtyp_and12.
              --- apply ty_sub with (pvar tl ↓ T2); auto.
                  eapply subtyp_sel2.
                  var_subtyp2.
                  eapply subtyp_trans; try apply subtyp_and11.
                  eapply subtyp_trans; try apply subtyp_and11.
                  eapply subtyp_trans; try apply subtyp_and12.
                  auto.
        -- eapply subtyp_sel2.
           var_subtyp2.
           eapply subtyp_trans; try apply subtyp_and11.
           eapply subtyp_trans; try apply subtyp_and11.
           apply subtyp_and12.
    + crush.
      let F := gather_vars in
      intros tup Frtup;
        instantiate (1:=F) in Frtup.
      repeat apply ty_and_intro.
      * eapply ty_sub with (μ (({T1 >: ⊥ <: ⊤} ∧ {T2 >: ⊥ <: ⊤}) ∧ {fst_v ⦂ this ↓ T1}) ∧ {snd_v ⦂ this ↓ T2}).
        -- apply ty_rec_intro.
           crush.
           repeat apply ty_and_intro.
           ++ var_subtyp_mu2.
              eapply subtyp_trans; try apply subtyp_and11.
              eapply subtyp_trans; try apply subtyp_and11.
              eapply subtyp_trans; try apply subtyp_and11.
              apply~ subtyp_typ.
           ++ var_subtyp_mu2.
              eapply subtyp_trans; try apply subtyp_and11.
              eapply subtyp_trans; try apply subtyp_and11.
              eapply subtyp_trans; try apply subtyp_and12.
              apply~ subtyp_typ.
           ++ apply ty_rcd_intro.
              apply ty_sngl with (pvar x1).
              ** apply ty_new_elim.
                 var_subtyp_mu2.
                 eapply subtyp_trans; try apply subtyp_and11.
                 apply subtyp_and12.
              ** apply ty_sub with (pvar tl ↓ T1).
                 --- auto.
                 --- eapply subtyp_sel2.
                     var_subtyp_mu2.
                     eapply subtyp_trans; try apply subtyp_and11.
                     eapply subtyp_trans; try apply subtyp_and11.
           ++ apply ty_rcd_intro.
              apply ty_sngl with (pvar x2).
              ** apply ty_new_elim.
                 var_subtyp_mu2.
              ** apply ty_sub with (pvar tl ↓ T2); auto.
                 eapply subtyp_sel2.
                 match goal with
                 | [ |- context[tup ~ μ ?T] ] =>
                   apply ty_sub with T
                 end.
                 --- match goal with
                     | [ |- ?G ⊢ tvar tup : ?T ] =>
                       assert (Hre: T = open_typ_p (pvar tup) T) by (cbn; auto);
                         rewrite Hre;
                         clear Hre
                     end.
                     apply ty_rec_elim. cbn. apply~ ty_var.
                 --- eapply subtyp_trans; try apply subtyp_and11.
                     eapply subtyp_trans; try apply subtyp_and11.
                     eapply subtyp_trans; try apply subtyp_and12.
                     auto.
        -- eapply subtyp_sel2.
           var_subtyp2.
           eapply subtyp_trans; try apply subtyp_and11.
           eapply subtyp_trans; try apply subtyp_and11.
           eapply subtyp_trans; try apply subtyp_and12.
           auto.
      * var_subtyp_mu2.
        solve_subtyp_and.
      * var_subtyp_mu2.
        solve_subtyp_and.
Qed.

Definition TupleT (TT1 TT2 : Target.typ) : Target.typ :=
  (pvar lib ↓ Tuple) ∧ { T1 == TT1 } ∧ { T2 == TT2 }.
