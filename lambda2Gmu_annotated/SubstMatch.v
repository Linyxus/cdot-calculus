Set Implicit Arguments.
Require Import GMuAnnot.Prelude.
Require Import GMuAnnot.Infrastructure.
Require Import GMuAnnot.Regularity.
Require Import GMuAnnot.Regularity2.
Require Import GMuAnnot.Equations.
Require Import TLC.LibLN.

Lemma subst_sources_from_match : forall Σ D Θ,
    subst_matches_typctx Σ D Θ ->
    substitution_sources Θ = domΔ D.
  induction 1; cbn; auto.
  fold (from_list (List.map fst Θ)).
  fold (substitution_sources Θ).
  rewrite~ IHsubst_matches_typctx.
Qed.

Lemma subst_match_remove_eq : forall Σ Θ D1 D2 T1 T2,
    subst_matches_typctx Σ (D1 |,| [tc_eq (T1 ≡ T2)]* |,| D2) Θ ->
    subst_matches_typctx Σ (D1 |,| D2) Θ.
  introv Match.
  gen_eq D3: (D1 |,| [tc_eq (T1 ≡ T2)]* |,| D2). gen D1 D2.
  induction Match; introv EQ; subst; eauto.
  - false List.app_cons_not_nil.
    cbn in EQ.
    eauto.
  - destruct D2; inversions EQ.
    constructor; try fold (D1 |,| D2); auto.
    fold_delta.
    repeat rewrite notin_domΔ_eq in *.
    destruct H1 as [[? ?] ?].
    split~.
  - destruct D2; inversions EQ.
    + cbn. auto.
    + constructor; auto.
Qed.

Lemma subst_match_decompose_var : forall Σ D1 D2 Y Θ,
    subst_matches_typctx Σ ((D1 |,| [tc_var Y]*) |,| D2) Θ ->
    exists Θ1 Θ2 U,
      Θ = Θ1 |,| [(Y, U)]* |,| Θ2 /\
      subst_matches_typctx Σ D1 Θ1 /\
      substitution_sources Θ1 = domΔ D1 /\
      substitution_sources Θ2 = domΔ D2 /\
      Y \notin domΔ D1.
  induction D2; introv M; cbn in *.
  - inversions M.
    exists Θ0 (@List.nil (var * typ)) T.
    repeat split~.
    apply* subst_sources_from_match.
  - inversions M.
    + lets [O1 [O2 [U [EQ [M2 [S1 [S2 D]]]]]]]: IHD2 H2. subst.
      exists O1 ((A, T) :: O2) U.
      repeat split~.
      cbn. fold_subst_src.
      rewrite~ S2.
    + lets [O1 [O2 [U [EQ [M2 [S1 [S2 D]]]]]]]: IHD2 H1. subst.
      exists O1 O2 U.
      split~.
Qed.

Lemma subst_match_notin_srcs : forall Σ D O1 X U,
    subst_matches_typctx Σ D (O1 |, (X, U)) ->
    X \notin substitution_sources O1.
  introv M.
  gen_eq O0: (O1 |, (X, U)). gen O1.
  induction M; introv EQ; subst; auto.
  - inversion EQ.
  - inversions EQ. auto.
Qed.

Lemma subst_match_remove_right_var : forall Σ D1 X D2 O1 U O2 Y V,
    subst_matches_typctx Σ ((D1 |,| [tc_var X]*) |,| D2) ((O1 |,| [(X, U)]*) |,| (O2 |, (Y, V))) ->
    exists D3 D4,
      D2 = D3 |,| D4 /\
      subst_matches_typctx Σ ((D1 |,| [tc_var X]*) |,| D3) ((O1 |,| [(X, U)]*) |,| O2).
  induction D2 as [| [Z | [V1 V2]]]; introv M.
  - cbn in *.
    inversions M.
    false.
    apply H6.
    apply~ subst_match_notin_srcs2.
    apply List.in_or_app. cbn. eauto.
  - inversions M.
    exists D2 [tc_var Y]*.
    cbn.
    splits~.
  - inversions M.
    lets [D3 [D4 [EQ M2]]]: IHD2 H3.
    subst.
    exists D3 (D4 |, tc_eq (V1 ≡ V2)).
    cbn.
    splits~.
Qed.

Lemma subst_match_remove_right_var2 : forall Σ D1 X D2 O1 U,
    subst_matches_typctx Σ ((D1 |,| [tc_var X]*) |,| D2) (O1 |, (X, U)) ->
    subst_matches_typctx Σ D1 O1.
  induction D2 as [| [Z | [V1 V2]]]; introv M.
  - cbn in *.
    inversions M.
    auto.
  - inversions M.
    fold_delta.
    repeat rewrite notin_domΔ_eq in *.
    destruct H7 as [[? HF]].
    cbn in HF.
    rewrite notin_union in HF.
    destruct HF as [HF ?].
    false* notin_same.
  - inversions M.
    lets~ IH: IHD2 H3.
Qed.

Lemma equation_weaken_eq:
  forall (Σ : GADTEnv) (D1 D2 : list typctx_elem) (T1 T2 U1 U2 : typ),
    entails_semantic Σ (D1 |,| D2) (T1 ≡ T2) ->
    entails_semantic Σ ((D1 |,| [tc_eq (U1 ≡ U2)]*) |,| D2) (T1 ≡ T2).
Proof.
  introv H.
  cbn in *.
  introv M.
  apply H.
  apply subst_match_remove_eq with U1 U2. auto.
Qed.

Lemma subst_eq_strengthen : forall Θ T1 T2 Y T,
    Y \notin substitution_sources Θ ->
    (forall A U, List.In (A, U) Θ -> Y \notin fv_typ U) ->
    subst_tt' T1 Θ = subst_tt' T2 Θ ->
    subst_tt' (subst_tt Y T T1) Θ = subst_tt' (subst_tt Y T T2) Θ.
  induction Θ as [| [X U]]; introv FrSrc FrTrg EQ.
  - cbn in *.
    f_equal~.
  - cbn in *.
    fold_subst_src.
    assert (Y \notin fv_typ U).
    + eauto with listin.
    + rewrite~ subst_commute.
      rewrite (subst_commute U); auto.
      apply~ IHΘ.
      eauto with listin.
Qed.

Lemma subst_eq_strengthen_gen : forall Θ1 Θ2 X U Σ D1 D2 T1 T2,
    subst_tt' T1 (Θ1 |,| Θ2) = subst_tt' T2 (Θ1 |,| Θ2) ->
    subst_matches_typctx Σ (D1 |,| [tc_var X]* |,| D2) ((Θ1 |,| [(X, U)]*) |,| Θ2) ->
    subst_tt' T1 ((Θ1 |,| [(X, U)]*) |,| Θ2) = subst_tt' T2 ((Θ1 |,| [(X, U)]*) |,| Θ2).
  induction Θ2 as [| [Y V]]; introv EQ M.
  - cbn in *.
    apply~ subst_eq_strengthen.
    + apply* subst_match_notin_srcs.
    + apply* subst_has_no_fv2.
      fold_delta.
      lets*: subst_match_remove_right_var2 M.
  - cbn.
    lets [D3 [D4 [EQ2 M2]]]: subst_match_remove_right_var M.
    apply* IHΘ2.
Qed.

Lemma subst_eq_weaken : forall Θ1 Θ2 T1 T2 X U,
    subst_tt' T1 ((Θ1 |,| [(X, U)]*) |,| Θ2) = subst_tt' T2 ((Θ1 |,| [(X, U)]*) |,| Θ2) ->
    X \notin fv_typ T1 \u fv_typ T2 ->
    (forall A U, List.In (A, U) Θ2 -> fv_typ U = \{}) ->
    subst_tt' T1 (Θ1 |,| Θ2) = subst_tt' T2 (Θ1 |,| Θ2).
  induction Θ2; introv EQ Fr Fr2.
  - cbn in *.
    repeat rewrite~ subst_tt_fresh in EQ.
  - destruct a as [Y P]; cbn in *.
    rewrite notin_union in *. destruct Fr.
    assert (X \notin fv_typ P).
    + rewrite Fr2 with Y P; auto.
    + apply IHΘ2 with X U; auto.
      * rewrite notin_union in *.
        split; apply~ fv_subst_tt.
      * introv Ain. eauto with listin.
Qed.

Lemma subst_match_remove_unused_var : forall Σ Θ1 Θ2 D1 D2 X T,
    subst_matches_typctx Σ (D1 |,| [tc_var X]* |,| D2) (Θ1 |,| [(X, T)]* |,| Θ2) ->
    X \notin fv_delta D2 ->
    subst_matches_typctx Σ (D1 |,| D2) (Θ1 |,| Θ2).
  introv Match.
  gen_eq D3: (D1 |,| [tc_var X]* |,| D2). gen D1 D2.
  gen_eq Θ3: (Θ1 |,| [(X, T)]* |,| Θ2). gen Θ1 Θ2.
  induction Match; introv EQ EQ2 Fr; subst; eauto.
  - false List.app_cons_not_nil.
    cbn in *.
    eauto.
  - destruct D2; inversions EQ;
      cbn in *;
      inversions EQ2.
    + destruct Θ2; inversions H3; auto.
      false H0.
      apply~ substitution_sources_from_in.
      apply List.in_or_app. cbn. auto.
    + destruct Θ2; inversions H3.
      * repeat rewrite notin_domΔ_eq in *.
        cbn in H1.
        rewrite notin_union in H1.
        destruct H1 as [[HF]].
        false HF. apply in_singleton_self.
      * constructor; try fold (Θ1 |,| Θ2); auto.
        -- fold (Θ1 |,| [(X, T)]*) in *.
           repeat rewrite subst_src_app in *.
           repeat rewrite notin_union in *.
           destruct H0 as [[?]].
           split~.
        -- rewrite notin_domΔ_eq in *.
           destruct H1. cbn in H1. rewrite notin_union in H1. destruct H1.
           split~.
  - destruct D2; inversions EQ2.
    cbn in Fr.
    constructor.
    + fold (D1 |,| D2).
      apply~ IHMatch.
    + apply subst_eq_weaken with X T; auto.
      lets FM: subst_has_no_fv Match.
      introv Ain.
      eapply FM.
      apply List.in_or_app; left. apply Ain.
Qed.

Lemma equation_weaken_var:
  forall (Σ : GADTEnv) (D1 D2 : list typctx_elem) (Y : var) (T1 T2 : typ),
    entails_semantic Σ (D1 |,| D2) (T1 ≡ T2) ->
    Y \notin fv_delta D2 ->
    entails_semantic Σ ((D1 |,| [tc_var Y]*) |,| D2) (T1 ≡ T2).
Proof.
  introv Sem YFr.
  cbn in *.
  introv M.
  lets [Θ1 [Θ2 [U [EQ [M1 [S1 S2]]]]]]: subst_match_decompose_var M; subst.
  lets M2: subst_match_remove_unused_var M YFr.
  lets EQ: Sem M2.
  fold_delta.
  apply* subst_eq_strengthen_gen.
Qed.

Lemma subst_match_remove_right_var3 : forall Σ D O X U,
    subst_matches_typctx Σ D (O |, (X, U)) ->
    wft Σ emptyΔ U /\ exists D', subst_matches_typctx Σ D' O /\ X \notin substitution_sources O.
  induction D as [| [Z | [V1 V2]]]; introv M.
  - cbn in *.
    inversions M.
  - inversions M.
    splits~.
    eauto.
  - inversions M.
    lets~ IH: IHD H3.
Qed.

Lemma is_var_defined_dom : forall D X,
    is_var_defined D X <-> X \in domΔ D.
  induction D as [| [|]]; constructor; intros; cbn in *; try solve [false*].
  - apply* in_empty_inv.
  - destruct H as [H|H].
    + inversions H. rewrite in_union; left; apply in_singleton_self.
    + rewrite in_union; right. apply* IHD.
  - rewrite in_union in H.
    destruct H as [H|H].
    + rewrite in_singleton in H.
      subst. auto.
    + right. apply~ IHD.
  - destruct H as [H|H].
    + inversion H.
    + apply~ IHD.
  - right. apply~ IHD.
Qed.

Lemma subst_tt_prime_reduce_typ_fvar_defined : forall Σ O Δ X,
  subst_matches_typctx Σ Δ O ->
  is_var_defined Δ X ->
  exists T, subst_tt' (typ_fvar X) O = T /\ wft Σ emptyΔ T.
  induction O as [| [A U]]; cbn; introv M Def; auto.
  - lets: subst_sources_from_match M.
    cbn in H.
    apply is_var_defined_dom in Def.
    rewrite <- H in Def.
    false* in_empty_inv.
  - lets [W [D1 [M1 Src]]]: subst_match_remove_right_var3 M.
    case_var.
    + exists U; split~.
      apply subst_ttΘ_fresh.
      lets FV: wft_gives_fv W. cbn in FV.
      assert (HE: fv_typ U = \{}).
      * apply* fset_extens.
      * rewrite HE. apply~ inter_empty_r.
    + apply* IHO.
      lets S: subst_sources_from_match M.
      lets S1: subst_sources_from_match M1.
      cbn in S. fold_subst_src.
      rewrite S1 in S.
      apply is_var_defined_dom.
      apply is_var_defined_dom in Def.
      rewrite <- S in Def.
      rewrite in_union in Def.
      destruct~ Def as [H|H].
      rewrite in_singleton in H. false.
Qed.

Lemma subst_tt_prime_reduce_typ_fvar_undefined : forall O X,
  X \notin substitution_sources O ->
  subst_tt' (typ_fvar X) O = typ_fvar X.
  induction O as [| [A U]]; cbn; eauto.
  fold_subst_src.
  introv XFr.
  case_var.
  rewrite~ IHO.
Qed.

Lemma is_var_defined_split : forall A B c,
    is_var_defined (B |,| A) c ->
    (is_var_defined A c \/ is_var_defined B c).
  unfold is_var_defined.
  intros.
  apply~ List.in_app_or.
Qed.

Lemma subst_has_wft : forall Σ O Δ,
  subst_matches_typctx Σ Δ O ->
  forall A P, List.In (A, P) O -> wft Σ emptyΔ P.
  induction O as [| [X U]]; introv M.
  - intros. false~.
  - introv Hin.
    cbn in Hin.
    lets* [? [D' ?]]: subst_match_remove_right_var3 M.
    destruct Hin; subst.
    + inversions H1. auto.
    + apply* IHO.
Qed.

Lemma subst_has_closed : forall Σ O Δ,
  subst_matches_typctx Σ Δ O ->
  forall A P, List.In (A, P) O -> type P.
  introv M Hin.
  lets: subst_has_wft M Hin.
  apply* type_from_wft.
Qed.

Lemma wft_subst_matching_gen : forall Σ T O Δ D2,
  subst_matches_typctx Σ Δ O ->
  wft Σ (Δ |,| D2) T ->
  domΔ Δ \n domΔ D2 = \{} ->
  wft Σ (emptyΔ |,| D2) (subst_tt' T O).
  introv M W.
  gen_eq D: (Δ |,| D2). gen D2.
  induction W; introv EQ FV; subst; repeat rewrite List.app_nil_r in *.
  - rewrite subst_tt_prime_reduce_typ_unit.
    constructor.
  - lets [Def | Def]: is_var_defined_split H.
    + rewrite~ subst_tt_prime_reduce_typ_fvar_undefined.
      lets S: subst_sources_from_match M.
      rewrite S.
      intro HF.
      rewrite is_var_defined_dom in Def.
      eapply in_empty_inv.
      rewrite <- FV.
      rewrite* in_inter.
    + lets [T [? W]]: subst_tt_prime_reduce_typ_fvar_defined M Def.
      subst. rewrite <- (List.app_nil_r D2).
      apply~ wft_weaken_simple.
  - rewrite subst_tt_prime_reduce_arrow.
    forwards ~ : IHW1 M D2.
    forwards ~ : IHW2 M D2.
    repeat rewrite List.app_nil_r in *.
    constructor; auto.
  - rewrite subst_tt_prime_reduce_tuple.
    forwards ~ : IHW1 M D2.
    forwards ~ : IHW2 M D2.
    repeat rewrite List.app_nil_r in *.
    constructor; auto.
  - rewrite subst_tt_prime_reduce_typ_all.
    econstructor.
    let FV := gather_vars in
    introv XFr;
      instantiate (1:=FV) in XFr.
    assert (HE: typ_fvar X = (subst_tt' (typ_fvar X) O)).
    + rewrite~ subst_tt_prime_reduce_typ_fvar_undefined.
      lets R: subst_sources_from_match M.
      rewrite~ R.
    + rewrite HE.
      rewrite <- subst_ttprim_open_tt.
      * forwards * : H0 (D2 |,| [tc_var X]*); auto.
        -- cbn.
           rewrite inter_comm.
           rewrite union_distributes.
           rewrite (inter_comm (domΔ D2)).
           rewrite FV.
           rewrite union_empty_r.
           apply~ fset_extens.
           intros x HF.
           rewrite in_inter in HF.
           destruct HF as [HF1 HF2].
           rewrite in_singleton in HF1. subst.
           assert (HF3: X \notin domΔ Δ); auto.
           false* HF3.
        -- repeat rewrite List.app_nil_r in *.
           auto.
      * apply* subst_has_closed.
  - rewrite subst_tt_prime_reduce_typ_gadt.
    econstructor; eauto.
    + intros T' Inm.
      apply List.in_map_iff in Inm.
      destruct Inm as [T [? In]]; subst.
      forwards*: H0 D2.
      repeat rewrite List.app_nil_r in *.
      auto.
    + rewrite~ List.map_length.
Qed.

Lemma wft_subst_matching : forall Σ T O Δ,
  subst_matches_typctx Σ Δ O ->
  wft Σ Δ T ->
  wft Σ emptyΔ (subst_tt' T O).
  intros.
  rewrite <- (List.app_nil_l emptyΔ).
  apply* wft_subst_matching_gen.
  cbn.
  apply inter_empty_r.
Qed.

Lemma subst_idempotent_simple : forall Σ Δ O T,
    wft Σ Δ T ->
    subst_matches_typctx Σ Δ O ->
    (forall (X : var) (U : typ), List.In (X, U) O -> fv_typ U = \{}) ->
    subst_tt' (subst_tt' T O) O = subst_tt' T O.
  introv W M F.
  lets W2: wft_subst_matching M W.
  lets F2: wft_gives_fv W2.
  cbn in F2.
  rewrite~ subst_ttΘ_fresh.
  assert (FV: fv_typ (subst_tt' T O) = \{}).
  - apply* fset_extens.
  - rewrite FV. apply inter_empty_r.
Qed.

Lemma subst_eq_reorder1_2 : forall Σ Δ1 U O1 X V1 V2,
    wft Σ Δ1 U ->
    subst_matches_typctx Σ Δ1 O1 ->
    (forall X U, List.In (X, U) O1 -> fv_typ U = \{}) ->
    X \notin substitution_sources O1 ->
    subst_tt' (subst_tt X U V1) O1 =
    subst_tt' (subst_tt X U V2) O1 ->
    subst_tt' V1 (O1 |, (X, subst_tt' U O1)) =
    subst_tt' V2 (O1 |, (X, subst_tt' U O1)).
  introv W M F S EQ.
  cbn.
  assert (forall (X0 : var) (U0 : typ), List.In (X0, U0) O1 -> X \notin fv_typ U0).
  - intros A T In.
    rewrite~ (F A).
  - repeat rewrite~ subst_tt_inside.
    rewrite~ (@subst_idempotent_simple Σ Δ1).
    repeat rewrite~ <- subst_tt_inside.
Qed.

Lemma subst_tt_split : forall O1 O2 T,
    subst_tt' T (O1 |,| O2) = subst_tt' (subst_tt' T O2) O1.
  induction O2 as [| [A U]]; cbn; auto.
Qed.

Lemma subst_eq_reorder1 : forall Σ Δ1 U O1 O2 X V1 V2,
    wft Σ Δ1 U ->
    subst_matches_typctx Σ Δ1 O1 ->
    (forall X U, List.In (X, U) (O1 |,| O2) -> fv_typ U = \{}) ->
    X \notin substitution_sources (O1 |,| O2) ->
    substitution_sources O1 \n substitution_sources O2 = \{} ->
    subst_tt' (subst_tt X U V1) (O1 |,| O2) =
    subst_tt' (subst_tt X U V2) (O1 |,| O2) ->
    subst_tt' V1 (O1 |, (X, subst_tt' U O1) |,| O2) =
    subst_tt' V2 (O1 |, (X, subst_tt' U O1) |,| O2).
  introv W M F S SS EQ.
  repeat rewrite subst_tt_split in *.
  rewrite subst_src_app in S. rewrite notin_union in S. destruct S as [S1 S2].
  assert (forall (X0 : var) (U0 : typ), List.In (X0, U0) O2 -> X \notin fv_typ U0).
  1: {
    intros A V In. rewrite* (F A).
    apply~ List.in_or_app.
  }
  rewrite~ subst_tt_inside in EQ.
  rewrite~ (subst_tt_inside O2) in EQ.
  assert (R: subst_tt' U O2 = U).
  1: {
    rewrite~ subst_ttΘ_fresh.
    lets FV: wft_gives_fv W.
    lets SD: subst_sources_from_match M.
    apply~ fset_extens.
    intros x HF.
    rewrite in_inter in HF. destruct HF as [HF1 HF2].
    false.
    rewrite <- SD in FV.
    apply FV in HF2.
    apply~ in_empty_inv.
    rewrite <- SS.
    rewrite in_inter. eauto.
  }
  rewrite R in EQ.
  apply subst_eq_reorder1_2 with Σ Δ1; auto.
  - introv In. rewrite~ (F X0).
    apply~ List.in_or_app.
Qed.

(* TODO these may not need as strong assumptions *)
Lemma subst_eq_reorder2_2 : forall Σ Δ1 U O1 X V1 V2,
    wft Σ Δ1 U ->
    subst_matches_typctx Σ Δ1 O1 ->
    (forall X U, List.In (X, U) O1 -> fv_typ U = \{}) ->
    X \notin substitution_sources O1 ->
    subst_tt' V1 (O1 |,| [(X, subst_tt' U O1)]*) =
    subst_tt' V2 (O1 |,| [(X, subst_tt' U O1)]*) ->
    subst_tt X (subst_tt' U O1) (subst_tt' V1 O1) =
    subst_tt X (subst_tt' U O1) (subst_tt' V2 O1).
  introv W M F S EQ.
  cbn in EQ.
  assert (forall (X0 : var) (U0 : typ), List.In (X0, U0) O1 -> X \notin fv_typ U0).
  - intros A T In.
    rewrite~ (F A).
  - rewrite~ subst_tt_inside in EQ.
    rewrite~ subst_tt_inside in EQ.
    rewrite~ (@subst_idempotent_simple Σ Δ1) in EQ.
Qed.

Lemma subst_eq_reorder2 : forall Σ Δ1 U O1 O2 X V1 V2,
    wft Σ Δ1 U ->
    subst_matches_typctx Σ Δ1 O1 ->
    (forall X U, List.In (X, U) (O1 |,| O2) -> fv_typ U = \{}) ->
    X \notin substitution_sources (O1 |,| O2) ->
    substitution_sources O1 \n substitution_sources O2 = \{} ->
    subst_tt' V1 (O1 |,| [(X, subst_tt' U O1)]* |,| O2) =
    subst_tt' V2 (O1 |,| [(X, subst_tt' U O1)]* |,| O2) ->
    subst_tt X (subst_tt' U (O1 |,| O2))
             (subst_tt' V1 (O1 |,| O2)) =
    subst_tt X (subst_tt' U (O1 |,| O2))
             (subst_tt' V2 (O1 |,| O2)).
  introv W M F S SS EQ.
  repeat rewrite subst_tt_split in *.
  assert (R: subst_tt' U O2 = U).
  1: {
    rewrite~ subst_ttΘ_fresh.
    lets FV: wft_gives_fv W.
    lets SD: subst_sources_from_match M.
    apply~ fset_extens.
    intros x HF.
    rewrite in_inter in HF. destruct HF as [HF1 HF2].
    false.
    rewrite <- SD in FV.
    apply FV in HF2.
    apply~ in_empty_inv.
    rewrite <- SS.
    rewrite in_inter. eauto.
  }
  repeat rewrite R in *.
  apply subst_eq_reorder2_2 with Σ Δ1; auto.
  - introv In. rewrite~ (F X0).
    apply~ List.in_or_app.
  - rewrite subst_src_app in S.
    rewrite~ notin_union in S.
    destruct~ S.
Qed.

Lemma sources_distinct : forall Σ O Δ,
    subst_matches_typctx Σ Δ O ->
    DistinctList (List.map fst O).
  induction O as [| [A U]]; introv M.
  - cbn; constructor.
  - cbn.
    lets [? [D2 [M2 S2]]]: subst_match_remove_right_var3 M.
    constructor; eauto.
    intro HF.
    apply S2.
    apply~ sources_list_fst.
Qed.

Lemma subst_remove_used_var : forall Σ Δ1 Δ2 O1 O2 X U,
    subst_matches_typctx Σ (Δ1 |,| List.map (subst_td X U ) Δ2) (O1 |,| O2) ->
    subst_matches_typctx Σ Δ1 O1 ->
    wft Σ Δ1 U ->
    X \notin substitution_sources (O1 |,| O2) ->
    X \notin domΔ (Δ1 |,| Δ2) ->
    subst_matches_typctx Σ (Δ1 |,| [tc_var X]* |,| Δ2) (O1 |,| [(X, subst_tt' U O1)]* |,| O2).
  induction Δ2 as [| [| [V1 V2]]]; introv M M1 WFT XO XD; cbn in *.
  - destruct O2 as [| [Y T]].
    + cbn in *.
      constructor; auto.
      fold_subst_src.
      apply* wft_subst_matching.
    + rewrite <- List.app_comm_cons in M.
      lets [? [Δ' [? HF]]]: subst_match_remove_right_var3 M.
      false.
      lets HF1: subst_sources_from_match M.
      lets HF2: subst_sources_from_match M1.
      cbn in HF1. fold_subst_src. rewrite <- HF2 in HF1.
      apply HF.
      rewrite subst_src_app. rewrite in_union. left.
      rewrite <- HF1.
      rewrite in_union. left. apply in_singleton_self.
  - inversions M.
    destruct O2.
    + cbn in *; subst.
      false.
      rewrite notin_domΔ_eq in H5.
      destruct H5 as [HF].
      apply HF.
      lets HF1: subst_sources_from_match M1.
      rewrite <- HF1.
      cbn. fold_subst_src. rewrite in_union; left; apply in_singleton_self.
    + destruct p as [A' T'].
      rewrite <- List.app_comm_cons in H1.
      inversions H1.
      constructor; auto; try fold (O1 |, (X, subst_tt' U O1) |,| O2).
      * apply~ IHΔ2.
        cbn in XO. fold_subst_src.
        lets~ : notin_union.
      * fold (O1 |,| [(X, subst_tt' U O1)]*).
        repeat rewrite subst_src_app in *.
        repeat rewrite notin_union in *.
        destruct H4.
        repeat split~.
        cbn.
        rewrite notin_union; split~.
        apply notin_inverse. destruct~ XD.
      * fold_delta.
        repeat rewrite domDelta_app in *.
        repeat rewrite notin_union in *.
        destruct H5 as [? FD2].
        rewrite <- domDelta_subst_td in FD2.
        repeat split~.
        cbn.
        rewrite notin_union; split~.
        apply notin_inverse. destruct~ XD.
  - inversions M.
    constructor.
    + apply* IHΔ2.
    + lets: subst_has_no_fv H3.
      apply* subst_eq_reorder1.
      apply distinct_split1.
      rewrite <- List.map_app.
      apply* sources_distinct.
Qed.

Lemma subst_match_split : forall Σ Δ1 Δ2 O,
    subst_matches_typctx Σ (Δ1 |,| Δ2) O ->
    exists O1 O2, O = O1 |,| O2 /\ subst_matches_typctx Σ Δ1 O1.
  induction Δ2; introv M; cbn in *.
  - exists O (@nil (var*typ)). auto.
  - inversions M.
    + lets [O1 [O2 [EQ M2]]]: IHΔ2 H2; subst.
      exists O1 (O2 |, (A, T)).
      auto.
    + apply IHΔ2.
      auto.
Qed.

Lemma entails_through_subst : forall Σ Δ1 Δ2 Z P T1 T2,
    entails_semantic Σ (Δ1 |,| [tc_var Z]* |,| Δ2) (T1 ≡ T2) ->
    Z \notin domΔ (Δ1 |,| Δ2) ->
    wft Σ Δ1 P ->
    entails_semantic Σ (Δ1 |,| List.map (subst_td Z P) Δ2)
                     (subst_tt Z P T1 ≡ subst_tt Z P T2).
  introv Sem ZFR WFT.
  cbn in *.
  introv M.
  lets [O1 [O2 [? M1]]]: subst_match_split M; subst.
  assert (forall (X : var) (U : typ), List.In (X, U) (O1 |,| O2) -> Z \notin fv_typ U).
  1: {
    introv In.
    lets FV: subst_has_no_fv M.
    rewrite~ (FV X).
  }
  assert (Z \notin substitution_sources (O1 |,| O2)).
  1:{
    lets Src: subst_sources_from_match M.
    rewrite Src.
    rewrite domDelta_app.
    rewrite <- domDelta_subst_td.
    rewrite~ <- domDelta_app.
  }
  forwards~ M2: subst_remove_used_var M M1.
  lets: Sem M2.
  repeat rewrite~ subst_tt_inside.
  lets FV: subst_has_no_fv M.
  apply* subst_eq_reorder2.
  apply distinct_split1.
  rewrite <- List.map_app.
  apply* sources_distinct.
Qed.

Opaque entails_semantic.
Lemma equations_weaken_match : forall Σ Δ As Ts Us T1 T2,
  List.length Ts = List.length Us ->
  entails_semantic Σ Δ (T1 ≡ T2) ->
  entails_semantic Σ
    (Δ |,| tc_vars As |,| equations_from_lists Ts Us)
    (T1 ≡ T2).
  induction Ts as [| T Ts]; introv Len Sem.
  - cbn.
    induction As as [| A As].
    + cbn. auto.
    + cbn.
      fold (tc_vars As).
      fold_delta.
      rewrite <- (List.app_nil_l (Δ |,| tc_vars As |,| [tc_var A]*)).
      apply~ equation_weaken_var; cbn; auto.
  - destruct Us as [| U Us].
    + inversion Len.
    + cbn.
      fold (equations_from_lists Ts Us).
      fold_delta.
      rewrite <- (List.app_nil_l (Δ |,| tc_vars As |,| equations_from_lists Ts Us |,| [tc_eq (T ≡ U)]*)).
      apply equation_weaken_eq.
      rewrite List.app_nil_l.
      apply* IHTs.
Qed.
Transparent entails_semantic.

Lemma teq_open : forall Σ Δ T1 T2 T,
  entails_semantic Σ Δ (T1 ≡ T2) ->
  entails_semantic Σ Δ (open_tt T1 T ≡ open_tt T2 T).
  introv Sem.
  cbn in *.
  introv M.
  lets: subst_has_closed M.
  repeat rewrite~ subst_ttprim_open_tt.
  f_equal.
  apply~ Sem.
Qed.

Lemma subst_eq_weaken2 : forall O1 O2 T1 T2 E D,
    subst_matches_typctx E D (O1 |,| O2) ->
    subst_tt' T1 O1 = subst_tt' T2 O1 ->
    subst_tt' T1 (O1 |,| O2) = subst_tt' T2 (O1 |,| O2).
  induction O2 as [| [A U]]; introv M EQ; cbn in *; auto.
  lets [? [D2 [? Src]]]: subst_match_remove_right_var3 M.
  apply* IHO2.
  assert (forall (X : var) (U0 : typ), List.In (X, U0) O1 -> A \notin fv_typ U0).
  - lets FV: subst_has_no_fv M.
    introv In.
    rewrite~ (FV X).
    cbn. right.
    apply List.in_or_app. right~.
  - rewrite subst_src_app in Src.
    rewrite notin_union in Src.
    destruct Src.
    repeat rewrite* subst_tt_inside.
    f_equal.
    auto.
Qed.

Lemma subst_match_inv_missing_var : forall Σ D1 O D2 A T,
  subst_matches_typctx Σ D1 (O |, (A, T)) ->
  subst_matches_typctx Σ (D1 |,| D2) O ->
  False.
  introv M1 M2.
  lets [? [D0 [? HF]]]: subst_match_remove_right_var3 M1; subst.
  (* lets [? [D0 [D0' [M0 [? ?]]]]]: subst_match_remove_right_var4 M1; subst. *)
  lets S1: subst_sources_from_match M1.
  lets S2: subst_sources_from_match M2.
  cbn in S1. fold_subst_src.
  rewrite domDelta_app in S2.
  apply HF.
  rewrite S2.
  rewrite in_union. left.
  rewrite <- S1.
  rewrite in_union. left.
  apply in_singleton_self.
Qed.

Lemma subst_strengthen_true_eq : forall Σ Δ1 Δ2 O1 O2 U1 U2,
    subst_matches_typctx Σ Δ1 O1 ->
    subst_matches_typctx Σ (Δ1 |,| Δ2) (O1 |,| O2) ->
    subst_tt' U1 O1 = subst_tt' U2 O1 ->
    subst_matches_typctx Σ (Δ1 |,| [tc_eq (U1 ≡ U2)]* |,| Δ2) (O1 |,| O2).
  induction Δ2 as [| [| [V1 V2]]]; introv M1 M2 EQ; cbn in *; fold_delta.
  - constructor; auto.
    apply* subst_eq_weaken2.
  - inversions M2.
    destruct O2.
    + cbn in H1. subst.
      false* subst_match_inv_missing_var.
    + inversions H1.
      econstructor; eauto.
      repeat rewrite notin_domΔ_eq in *;
        destruct H5; repeat split~;
                            cbn; auto.
  - inversions M2.
    econstructor; eauto.
Qed.

Lemma equation_strengthen : forall Σ Δ1 Δ2 U1 U2 T1 T2,
    entails_semantic Σ (Δ1 |,| [tc_eq (U1 ≡ U2)]* |,| Δ2) (T1 ≡ T2) ->
    entails_semantic Σ Δ1 (U1 ≡ U2) ->
    entails_semantic Σ (Δ1 |,| Δ2) (T1 ≡ T2).
  introv SemT SemU.
  cbn in *.
  fold_delta.
  introv M.
  lets [O1 [O2 [? M2]]]: subst_match_split M; subst.
  lets EQ: SemU M2.
  apply SemT.
  apply~ subst_strengthen_true_eq.
Qed.
