Set Implicit Arguments.
Require Import GMuAnnot.Prelude.
Require Import GMuAnnot.Infrastructure.
Require Import GMuAnnot.Regularity.
Require Import GMuAnnot.Regularity2.
Require Import GMuAnnot.SubstMatch.
Require Import GMuAnnot.Equations.
Require Import TLC.LibLN.

#[export] Hint Resolve okt_is_ok.

Lemma typing_weakening_delta_eq:
  forall (u : trm) (Σ : GADTEnv) (D1 D2 : list typctx_elem) (E : env bind) (U : typ) eq TT,
    {Σ, D1 |,| D2, E} ⊢(TT) u ∈ U ->
    {Σ, D1 |,| [tc_eq eq]* |,| D2, E} ⊢(TT) u ∈ U.
Proof.
  introv Typ; gen_eq D': (D1 |,| D2); gen D2.
  induction Typ; introv EQ; subst;
    try solve [
          econstructor; fresh_intros; eauto
        | econstructor; eauto using okt_weakening_delta_eq; eauto using wft_weaken
        ].
  - apply_fresh typing_tabs as Y; auto.
    lets* IH: H1 Y (D2 |,| [tc_var Y]*).
  - econstructor; eauto.
    introv In Alen Adist Afr xfr xAfr.

    lets* IH: H4 In xAfr (D2 |,| tc_vars Alphas |,|
                          equations_from_lists Ts (List.map (open_tt_many_var Alphas) (Crettypes def))).
    repeat rewrite List.app_assoc in *.
    apply~ IH.
  - econstructor; eauto.
    + destruct eq. apply~ equation_weaken_eq.
    + apply~ wft_weaken.
Qed.

Lemma typing_weakening_delta:
  forall (u : trm) (Σ : GADTEnv) (D1 D2 : list typctx_elem) (E : env bind) (U : typ) (Y : var) TT,
    {Σ, D1 |,| D2, E} ⊢(TT) u ∈ U ->
    Y # E ->
    Y \notin domΔ D1 ->
    Y \notin domΔ D2 ->
    Y \notin fv_delta D2 ->
    {Σ, D1 |,| [tc_var Y]* |,| D2, E} ⊢(TT) u ∈ U.
Proof.
  introv Typ FE FD1 FD2 FrD; gen_eq D': (D1 |,| D2); gen D2.
  lets Typ2: Typ.
  induction Typ; introv FD2 FrD EQ; subst;
    try solve [
          econstructor; fresh_intros; eauto
        | econstructor; eauto using okt_weakening_delta; eauto using wft_weaken
        ].
  - econstructor; auto;
    try let envvars := gather_vars in
    instantiate (1:=envvars); auto.
    intros.
    lets* IH: H1 X (D2 |,| [tc_var X]*).
    repeat rewrite <- List.app_assoc in *.
    apply IH; auto.
    rewrite notin_domΔ_eq. split; auto.
    cbn. rewrite notin_union.
    split; auto.
  - econstructor; eauto.
    introv Hin.
    try let envvars := gather_vars in
    introv Hlen Hdist Afresh xfreshL xfreshA;
      instantiate (1:=envvars) in xfreshL.
    lets IH: H4 Hin Hlen (D2 |,| tc_vars Alphas |,| equations_from_lists Ts (List.map (open_tt_many_var Alphas) (Crettypes def))); eauto.
    + introv Ain. lets*: Afresh Ain.
    + eauto.
    + apply~ H3.
      introv Ain. lets*: Afresh Ain.
    + repeat rewrite List.app_assoc in *.
      apply IH; auto.
      rewrite notin_domΔ_eq; split; auto.
      * rewrite notin_domΔ_eq; split; auto.
        -- apply notin_dom_tc_vars.
           intro HF.
           lets HF2: from_list_spec HF.
           lets HF3: LibList_mem HF2.
           lets HF4: Afresh HF3.
           eapply notin_same.
           instantiate (1:=Y).
           eauto.
        -- rewrite equations_have_no_dom; auto.
           apply* equations_from_lists_are_equations.
      * repeat rewrite fv_delta_app.
        repeat rewrite notin_union.
        splits~.
        -- rewrite~ fv_delta_alphas.
        -- lets [? [? WFT]]: typing_regular Typ.
           lets FV: wft_gives_fv WFT.
           cbn in FV.
           apply fv_delta_equations.
           ++ intros T Tin.
              intro HF.
              lets FV2: fold_left_subset fv_typ Tin.
              lets FV3: subset_transitive FV2 FV.
              lets FV4: FV3 HF.
              rewrite domDelta_app in FV4.
              rewrite in_union in FV4.
              destruct FV4; auto.
           ++ intros R Rin.
              assert (OKS: okGadt Σ).
              ** apply~ okt_implies_okgadt.
                 apply* typing_regular.
              ** apply List.in_map_iff in Rin.
                 destruct Rin as [rT [? rTin]]; subst.
                 lets Sub: fv_smaller_many Alphas rT.
                 intro HF.
                 lets HF2: Sub HF.
                 rewrite in_union in HF2.
                 destruct HF2 as [HF2 | HF2].
                 ---
                   destruct OKS as [? OKS].
                   lets [? OKD]: OKS H0.
                   lets Din: fst_from_zip Hin.
                   lets OKC: OKD Din.
                   inversion OKC as [? ? ? ? ? ? ? ? ? FrR]; subst.
                   cbn in rTin.
                   lets FR: FrR rTin.
                   rewrite FR in HF2.
                   false* in_empty_inv.
                 ---
                   lets [A [Ain ?]]: in_from_list HF2; subst.
                   lets: Afresh Ain.
                   assert (A \notin \{ A}); auto.
                   false* notin_same.
  - econstructor.
    + apply~ IHTyp.
    + apply~ equation_weaken_var.
    + apply wft_weaken.
      lets~ [? [? ?]]: typing_regular Typ2.
Qed.

Lemma typing_weakening_delta_many_eq : forall Σ Δ E Deqs u U TT,
    {Σ, Δ, E} ⊢(TT) u ∈ U ->
    (forall eq, List.In eq Deqs -> exists ϵ, eq = tc_eq ϵ) ->
    {Σ, Δ |,| Deqs, E} ⊢(TT) u ∈ U.
  induction Deqs; introv Typ EQs.
  - clean_empty_Δ. auto.
  - destruct a;
      try solve [lets HF: EQs (tc_var A); false~ HF].
    fold_delta.
    rewrite <- List.app_assoc.
    lets W: typing_weakening_delta_eq Σ (Δ |,| Deqs) emptyΔ.
    clean_empty_Δ.
    rewrite <- (List.app_nil_l ((Δ |,| Deqs) |,| [tc_eq eq]*)).
    apply~ W.
    apply~ IHDeqs.
    intros eq1 ?. lets Hin: EQs eq1.
    destruct Hin; eauto.
    cbn. auto.
Qed.

Lemma typing_weakening_delta_many : forall Σ Δ E As u U TT,
    (forall A, List.In A As -> A # E) ->
    (forall A, List.In A As -> A \notin domΔ Δ) ->
    DistinctList As ->
    {Σ, Δ, E} ⊢(TT) u ∈ U ->
    {Σ, Δ |,| tc_vars As, E} ⊢(TT) u ∈ U.
  induction As as [| Ah Ats]; introv AE AD Adist Typ.
  - cbn. clean_empty_Δ. auto.
  - cbn. fold_delta.
    inversions Adist.
    rewrite <- (List.app_nil_l ((Δ |,| tc_vars Ats) |,| [tc_var Ah]*)).
    apply typing_weakening_delta; cbn; auto with listin.
    rewrite notin_domΔ_eq. split.
    + auto with listin.
    + apply notin_dom_tc_vars.
      intro HF.
      apply from_list_spec in HF.
      apply LibList_mem in HF.
      auto.
Qed.

Lemma typing_weakening : forall Σ Δ E F G e T TT,
    {Σ, Δ, E & G} ⊢(TT) e ∈ T ->
    okt Σ Δ (E & F & G) ->
    {Σ, Δ, E & F & G} ⊢(TT) e ∈ T.
Proof.
  introv HTyp. gen_eq K: (E & G). gen G F.
  induction HTyp using typing_ind; introv EQ Ok; subst; eauto.
  - apply* typing_var. apply* binds_weaken.
  - econstructor; eauto.
    let env := gather_vars in
    instantiate (2:=env).
    introv xfresh.
    lets IH: H0 x (G & x ~l V) F; auto.
    rewrite <- concat_assoc.
    apply IH.
    + auto using concat_assoc.
    + rewrite concat_assoc.
      econstructor; eauto.
      assert (xL: x \notin L); auto.
      lets Typ: H xL.
      lets [? [? ?]]: typing_regular Typ.
      eapply okt_is_wft. eauto.
  - apply_fresh* typing_tabs as X.
    lets IH: H1 X G F; auto.
    apply IH.
    + auto using JMeq_from_eq.
    + rewrite <- (List.app_nil_l (Δ |,| [tc_var X]*)).
      apply okt_weakening_delta; clean_empty_Δ; cbn; auto.
  - apply_fresh* typing_fix as x.
    lets IH: H1 x (G & x ~f T) F; auto.
    rewrite <- concat_assoc.
    apply IH; repeat rewrite concat_assoc; auto.
    constructor; auto.
    lets [? [? ?]]: typing_regular T; eauto.
  - apply_fresh* typing_let as x.
    lets IH: H0 x (G & x ~l V) F; auto.
    rewrite <- concat_assoc.
    apply IH; repeat rewrite concat_assoc; auto.
    constructor; auto.
    lets [? [? ?]]: typing_regular V; eauto.
  - eapply typing_case; eauto.
    introv Inzip.
    let envvars := gather_vars in
    (introv AlphasArity ADistinct Afresh xfresh xfreshA;
     instantiate (1:=envvars) in Afresh).
    assert (AfreshL: forall A : var, List.In A Alphas -> A \notin L);
      [ introv Ain; lets*: Afresh Ain | idtac ].
    assert (xfreshL: x \notin L); eauto.
    lets* IH1: H4 Inzip Alphas x AlphasArity ADistinct.
    lets* IH2: IH1 AfreshL xfreshL xfreshA (G & x ~l open_tt_many_var Alphas (Cargtype def)) F.
    repeat rewrite concat_assoc in IH2.
    apply~ IH2.

    constructor; auto.
    + rewrite <- (List.app_nil_l (Δ |,| tc_vars Alphas |,| equations_from_lists Ts (List.map (open_tt_many_var Alphas) (Crettypes def)))).
      apply okt_weakening_delta_many_eq.
      * apply okt_weakening_delta_many; clean_empty_Δ;
          try solve [introv Ain; cbn; lets: Afresh Ain; auto]; auto.
      * apply* equations_from_lists_are_equations.
    + assert (OKS: okGadt Σ).
      * apply~ okt_implies_okgadt.
        apply* typing_regular.
      * destruct OKS as [? OKS].
        lets [? OKD]: OKS H0.
        lets Din: fst_from_zip Inzip.
        lets OKC: OKD Din.
        inversion OKC as [? ? ? ? ? ? Harg ? ? ?]; subst.
        cbn.
        apply wft_weaken_simple.
        apply~ Harg.
    + repeat rewrite notin_domΔ_eq.
      split~.
      * split~.
        apply notin_dom_tc_vars. auto.
      * rewrite equations_have_no_dom; eauto using equations_from_lists_are_equations.
Qed.

Lemma typing_through_subst_ee_lam : forall Σ Δ E F x u U e T TT1 TT2,
    {Σ, Δ, E & (x ~l U) & F} ⊢(TT1) e ∈ T ->
    {Σ, Δ, E} ⊢(TT2) u ∈ U ->
    value u ->
    {Σ, Δ, E & F} ⊢(Tgen) subst_ee x lam_var u e ∈ T.
  Ltac apply_ih :=
    match goal with
    | H: forall X, X \notin ?L -> forall E0 F0 x0 vk0 U0, ?P1 -> ?P2 |- _ =>
      apply_ih_bind* H end.
  introv TypT TypU ValU.
  inductions TypT; introv; cbn;
    try solve [eapply Tgen_from_any; eauto using okt_strengthen];
    lets [okU [termU wftU]]: typing_regular TypU.
  - match goal with
    | [ H: okt ?A ?B ?C |- _ ] =>
      lets: okt_strengthen H
    end.
    case_if~.
    + eapply Tgen_from_any.
      inversions C.
      binds_get H; eauto.
      assert (E & F & empty = E & F) as HEF by apply concat_empty_r.
      rewrite <- HEF.
      apply typing_weakening; rewrite concat_empty_r; eauto.
    + eapply Tgen_from_any. binds_cases H; apply* typing_var.
      match goal with
      | [H: bind_var ?vk ?T = bind_var ?vk2 ?U |- _] =>
        inversion* H
      end.
  - eapply Tgen_from_any.
    apply_fresh* typing_abs as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih.
  - eapply Tgen_from_any.
    apply_fresh* typing_tabs as Y; rewrite* subst_ee_open_te_var.
    match goal with
    | [ H: forall X, X \notin ?L -> forall E0 F0 x0 vk0 U0, ?P1 -> ?P2 |- _ ] =>
      apply* H
    end.
    rewrite <- (List.app_nil_l (Δ |,| [tc_var Y]*)).
    apply typing_weakening_delta; clean_empty_Δ; cbn; auto.
  - eapply Tgen_from_any.
    apply_fresh* typing_fix as y; rewrite* subst_ee_open_ee_var.
    apply_ih.
  - eapply Tgen_from_any.
    apply_fresh* typing_let as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih.
  - eapply Tgen_from_any.
    econstructor; eauto.
    + unfold map_clause_trm_trm.
      rewrite* List.map_length.
    + introv inzip.
      lets* [i [Hdefs Hmapped]]: Inzip_to_nth_error inzip.
      lets* [[clA' clT'] [Hclin Hclsubst]]: nth_error_map Hmapped.
      destruct clause as [clA clT]. cbn.
      inversions Hclsubst.
      lets* Hzip: Inzip_from_nth_error Hdefs Hclin.
      lets*: H2 Hzip.
    + introv inzip.
      let env := gather_vars in
      intros Alphas xClause Alen Adist Afresh xfresh xfreshA;
        instantiate (1:=env) in xfresh.
      lets* [i [Hdefs Hmapped]]: Inzip_to_nth_error inzip.
      lets* [[clA' clT'] [Hclin Hclsubst]]: nth_error_map Hmapped.
      destruct clause as [clA clT]. cbn.
      inversions Hclsubst.
      lets* Hzip: Inzip_from_nth_error Hdefs Hclin.
      lets* IH: H4 Hzip.

      assert (Htypfin: {Σ, Δ |,| tc_vars Alphas |,| equations_from_lists Ts (List.map (open_tt_many_var Alphas) (Crettypes def)),
                        E & F & xClause ~l (open_tt_many_var Alphas (Cargtype def))}
                ⊢(Tgen) subst_ee x lam_var u (open_te_many_var Alphas clT' open_ee_varlam xClause) ∈ Tc).
      * assert (AfreshL: forall A : var, List.In A Alphas -> A \notin L);
          [ introv Ain; lets*: Afresh Ain | idtac ].
        assert (xfreshL: xClause \notin L); eauto.
        lets Htmp: IH Alphas xClause Alen Adist AfreshL.
        lets Htmp2: Htmp xfreshL xfreshA.
        lets Htmp3: Htmp2 E (F & xClause ~l (open_tt_many_var Alphas (Cargtype def))) x U.
        cbn in Htmp3.
        rewrite <- concat_assoc.
        apply* Htmp3.
        apply JMeq_from_eq.
        eauto using concat_assoc.
        apply typing_weakening_delta_many_eq;
          eauto using equations_from_lists_are_equations.
        apply typing_weakening_delta_many; auto;
          try introv Ain; lets: Afresh Ain; auto.
      * assert (Horder:
                  subst_ee x lam_var u (open_te_many_var Alphas clT' open_ee_varlam xClause)
                  =
                  open_te_many_var Alphas (subst_ee x lam_var u clT') open_ee_varlam xClause).
        -- rewrite* <- subst_ee_open_ee_var.
           f_equal.
           apply* subst_commutes_with_unrelated_opens_te_ee.
        -- rewrite* <- Horder.
               Qed.

Lemma typing_through_subst_ee_fix : forall Σ Δ E F x u U e T TT1 TT2,
    {Σ, Δ, E & (x ~f U) & F} ⊢(TT1) e ∈ T ->
    {Σ, Δ, E} ⊢(TT2) u ∈ U ->
    {Σ, Δ, E & F} ⊢(Tgen) subst_ee x fix_var u e ∈ T.
  introv TypT TypU.
  inductions TypT; introv; cbn;
    try solve [eapply Tgen_from_any; eauto using okt_strengthen];
    lets [okU [termU wftU]]: typing_regular TypU.
  - match goal with
    | [ H: okt ?A ?B ?C |- _ ] =>
      lets: okt_strengthen H
    end.
    case_if~.
    + inversions C.
      eapply Tgen_from_any. binds_get H; eauto.
      assert (E & F & empty = E & F) as HEF by apply concat_empty_r.
      rewrite <- HEF.
      apply typing_weakening; rewrite concat_empty_r; eauto.
    + eapply Tgen_from_any. binds_cases H; apply* typing_var.
      match goal with
      | [H: bind_var ?vk ?T = bind_var ?vk2 ?U |- _] =>
        inversion* H
      end.
  - eapply Tgen_from_any.
    apply_fresh* typing_abs as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih.
  - eapply Tgen_from_any.
    apply_fresh* typing_tabs as Y; rewrite* subst_ee_open_te_var.
    + apply* subst_ee_fix_value.
    + match goal with
      | [ H: forall X, X \notin ?L -> forall E0 F0 x0 vk0 U0, ?P1 -> ?P2 |- _ ] =>
        apply* H
      end.
      rewrite <- (List.app_nil_l (Δ |,| [tc_var Y]* )).
      apply typing_weakening_delta; clean_empty_Δ; cbn; auto.
  - eapply Tgen_from_any.
    apply_fresh* typing_fix as y; rewrite* subst_ee_open_ee_var.
    + apply* subst_ee_fix_value.
    + apply_ih.
  - eapply Tgen_from_any.
    apply_fresh* typing_let as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih.
  - eapply Tgen_from_any.
    econstructor; eauto.
    + unfold map_clause_trm_trm.
      rewrite* List.map_length.
    + introv inzip.
      lets* [i [Hdefs Hmapped]]: Inzip_to_nth_error inzip.
      lets* [[clA' clT'] [Hclin Hclsubst]]: nth_error_map Hmapped.
      destruct clause as [clA clT]. cbn.
      inversions Hclsubst.
      lets* Hzip: Inzip_from_nth_error Hdefs Hclin.
      lets*: H2 Hzip.
    + introv inzip.
      let env := gather_vars in
      intros Alphas xClause Alen Adist Afresh xfresh xfreshA;
        instantiate (1:=env) in xfresh.
      lets* [i [Hdefs Hmapped]]: Inzip_to_nth_error inzip.
      lets* [[clA' clT'] [Hclin Hclsubst]]: nth_error_map Hmapped.
      destruct clause as [clA clT]. cbn.
      inversions Hclsubst.
      lets* Hzip: Inzip_from_nth_error Hdefs Hclin.
      lets* IH: H4 Hzip.

      assert (Htypfin: {Σ, Δ |,| tc_vars Alphas |,| equations_from_lists Ts (List.map (open_tt_many_var Alphas) (Crettypes def)),
                        E & F & xClause ~l (open_tt_many_var Alphas (Cargtype def))}
                ⊢(Tgen) subst_ee x fix_var u (open_te_many_var Alphas clT' open_ee_varlam xClause) ∈ Tc).
      * assert (AfreshL: forall A : var, List.In A Alphas -> A \notin L);
          [ introv Ain; lets*: Afresh Ain | idtac ].
        assert (xfreshL: xClause \notin L); eauto.
        lets Htmp: IH Alphas xClause Alen Adist AfreshL.
        lets Htmp2: Htmp xfreshL xfreshA.
        lets Htmp3: Htmp2 E (F & xClause ~l (open_tt_many_var Alphas (Cargtype def))) x U.
        cbn in Htmp3.
        rewrite <- concat_assoc.
        apply* Htmp3.
        apply JMeq_from_eq.
        eauto using concat_assoc.
        apply typing_weakening_delta_many_eq;
          eauto using equations_from_lists_are_equations.
        apply typing_weakening_delta_many; auto;
          try introv Ain; lets: Afresh Ain; auto.
      * assert (Horder:
                  subst_ee x fix_var u (open_te_many_var Alphas clT' open_ee_varlam xClause)
                  =
                  open_te_many_var Alphas (subst_ee x fix_var u clT') open_ee_varlam xClause).
        -- rewrite* <- subst_ee_open_ee_var.
           f_equal.
           apply* subst_commutes_with_unrelated_opens_te_ee.
        -- rewrite* <- Horder.
Qed.

Lemma typing_through_subst_te_gen : forall Σ Δ1 Δ2 E Z e P T TT,
    {Σ, Δ1 |,| [tc_var Z]* |,| Δ2, E} ⊢(TT) e ∈ T ->
    wft Σ Δ1 P ->
    Z \notin fv_typ P ->
    Z \notin domΔ (Δ1 |,| Δ2) ->
    Z # E ->
    {Σ, Δ1 |,| List.map (subst_td Z P) Δ2, map (subst_tb Z P) E} ⊢(Tgen) subst_te Z P e ∈ subst_tt Z P T.
  introv Typ.
  gen_eq G: (Δ1 |,| [tc_var Z]* |,| Δ2). gen Δ2.
  induction Typ; introv EQ WFT FVZP FVZD FVZE; subst; eapply Tgen_from_any;
    cbn; eauto.
  - constructor. apply~ okt_through_subst_tdtb.
  - cbn. econstructor.
    + fold (subst_tb Z P (bind_var vk T)).
      apply~ binds_map.
    + apply~ okt_through_subst_tdtb.
  - assert (OKS: okGadt Σ).
    1: {
      apply~ okt_implies_okgadt.
      apply* typing_regular.
    }
    destruct OKS as [? OKS].
    lets [? OKD]: OKS H.
    lets Din: List.nth_error_In H0.
    lets OKC: OKD Din.
    inversion OKC as [? ? ? ? ? ? Harg Hwft FVarg FVret]; subst.
    econstructor; auto.
    + apply H.
    + rewrite~ List.map_length.
      eauto.
    + rewrite~ subst_commutes_open_tt_many.
      * apply* type_from_wft.
      * rewrite~ FVarg.
    + intros T' Tin.
      apply List.in_map_iff in Tin.
      destruct Tin as [T [? Tin]]; subst.
      apply* wft_subst_tb_3.
    + rewrite~ subst_commutes_open_tt_many.
      * apply* type_from_wft.
      * cbn. fold (fv_typs CretTypes).
        apply~ notin_fold.
        intros TR Tin.
        rewrite~ FVret.
  - apply_fresh typing_abs as x.
    fold (subst_tb Z P (bind_var lam_var V)).
    rewrite <- map_push.
    rewrite subst_te_open_ee_var.
    apply~ H0.
  - lets: type_from_wft WFT.
    apply_fresh typing_tabs as X.
    + forwards~ : H X.
      rewrite~ subst_te_open_te_var.
    + forwards * IH : H1 X (Δ2 |,| [tc_var X]*).
      1: {
        fold_delta.
        repeat rewrite domDelta_app in *.
        repeat rewrite notin_union in *.
        destruct FVZD.
        repeat split~.
        cbn.
        rewrite notin_union; split~.
        apply* notin_inverse.
      }
      fold_delta.
      repeat rewrite List.app_assoc in *.
      rewrite~ subst_te_open_te_var.
      rewrite~ subst_tt_open_tt_var.
      apply* IH.
  - econstructor; auto.
    + apply* IHTyp.
    + apply* wft_subst_tb_3.
    + fold subst_tt.
      rewrite* subst_tt_open_tt.
  - apply_fresh typing_fix as x.
    + forwards~ : H x.
      rewrite subst_te_open_ee_var.
      apply~ subst_te_value.
      apply* type_from_wft.
    + fold (subst_tb Z P (bind_var fix_var T)).
      rewrite <- map_push.
      rewrite subst_te_open_ee_var.
      apply~ H1.
  - apply_fresh typing_let as x.
    + apply* IHTyp.
    + rewrite subst_te_open_ee_var.
      fold (subst_tb Z P (bind_var lam_var V)).
      rewrite <- map_push.
      apply~ H0.
  - econstructor; eauto.
    + cbn. eauto.
    + unfold map_clause_trm_trm.
      rewrite~ List.map_length.
    + introv Inzip.
      lets [clA [clT [In2 ?]]]: inzip_map_clause_trm Inzip; subst.
      lets: H2 In2.
      cbn in *. auto.
    + let FV := gather_vars in
      introv Inzip Len Dist FA Fx FxA;
        instantiate (1 := FV) in FA.
      lets [clA [clT [In2 ?]]]: inzip_map_clause_trm Inzip; subst.
      assert (OKS: okGadt Σ).
      1: {
        apply~ okt_implies_okgadt.
        apply* typing_regular.
      }
      destruct OKS as [? OKS].
      lets [? OKD]: OKS H0; clear OKS.
      lets Din: fst_from_zip In2.
      lets OKC: OKD Din.
      inversion OKC as [? ? ? ? ? ? Harg Hwft FVarg FVret]; subst.
      cbn in *.
      lets~ IH : H4 In2 x Len Dist (Δ2 |,| tc_vars Alphas
                                |,| equations_from_lists Ts
                                (List.map (open_tt_many_var Alphas) retTs)).
      * introv Ain. lets*: FA Ain.
      * cbn in *.
        forwards~ IH2: IH; clear IH.
        -- repeat rewrite~ List.app_assoc.
        -- repeat rewrite domDelta_app in *.
           repeat rewrite notin_union.
           repeat rewrite notin_union in FVZD.
           destruct FVZD.
           repeat split~.
           ++ apply notin_dom_tc_vars.
              apply~ notin_from_list.
              intro HF.
              lets HF2 : FA HF.
              repeat rewrite notin_union in HF2.
              assert (Z \notin \{ Z }).
              ** destruct~ HF2 as [? [[? ?] ?]].
              ** apply* notin_same.
           ++ rewrite~ equations_have_no_dom.
              apply* equations_from_lists_are_equations.
        -- assert (FVZA: forall X : var, List.In X Alphas -> X <> Z).
           1: {
             intros A Ain.
             intro HF.
             subst.
             lets FA2: FA Ain.
             repeat rewrite notin_union in FA2.
             destruct~ FA2 as [? [[?]]].
             apply* notin_same.
           }
           rewrite~ <- subst_commutes_with_unrelated_opens_te.
           ** rewrite subst_te_open_ee_var.
              rewrite List.map_app in IH2.
              rewrite List.map_app in IH2.
              rewrite subst_td_alphas in IH2.
              rewrite subst_td_eqs in IH2.
              --- rewrite map_concat in IH2.
                  rewrite map_single in IH2.
                  cbn in IH2.
                  assert (Hrew: subst_tt Z P (open_tt_many_var Alphas argT) = open_tt_many_var Alphas argT).
                  +++ rewrite~ subst_commutes_with_unrelated_opens.
                      *** f_equal. rewrite~ subst_tt_fresh.
                          rewrite~ FVarg.
                      *** apply* type_from_wft.
                  +++ rewrite Hrew in IH2; clear Hrew.
                      repeat rewrite List.app_assoc in *.
                      apply IH2.
              --- introv Uin.
                  apply List.in_map_iff in Uin.
                  destruct Uin as [V [EQ Vin]]; subst.
                  intro HF.
                  lets Sm: fv_smaller_many Alphas V.
                  apply Sm in HF.
                  rewrite in_union in HF.
                  destruct HF as [HF|HF].
                  +++ rewrite~ FVret in HF.
                      apply* in_empty_inv.
                  +++ apply from_list_spec in HF.
                      apply LibList_mem in HF.
                      lets: FVZA HF. false.
           ** apply* type_from_wft.
  - econstructor; eauto.
    + apply* entails_through_subst.
    + apply* wft_subst_tb_3.
Qed.

Lemma typing_through_subst_te_3 :
  forall Σ Δ E Z e P T TT,
    {Σ, Δ |,| [tc_var Z]*, E} ⊢(TT) e ∈ T ->
    wft Σ Δ P ->
    Z \notin fv_typ P ->
    Z # E ->
    Z \notin fv_env E ->
    Z \notin domΔ Δ ->
    {Σ, Δ, E} ⊢(Tgen) subst_te Z P e ∈ subst_tt Z P T.
  introv Typ WFT ZP ZE1 ZE2 ZD.
  rewrite <- (List.app_nil_l (Δ |,| [tc_var Z]*)) in Typ.
  lets HT: typing_through_subst_te_gen Typ WFT ZP ZD ZE1.
  cbn in HT.
  rewrite~ subst_tb_id_on_fresh in HT.
Qed.

Lemma typing_through_subst_te_many : forall As Σ Δ Δ2 E F e T Ps TT,
    {Σ, (Δ |,| tc_vars As |,| Δ2), E & F} ⊢(TT) e ∈ T ->
    length As = length Ps ->
    (forall P, List.In P Ps -> wft Σ Δ P) ->
    (forall A, List.In A As -> A # E) ->
    (forall A, List.In A As -> A # F) ->
    (forall A, List.In A As -> A \notin domΔ Δ) ->
    (forall A, List.In A As -> A \notin domΔ Δ2) ->
    (forall A P, List.In A As -> List.In P Ps -> A \notin fv_typ P) ->
    (forall A, List.In A As -> A \notin fv_env E) ->
    DistinctList As ->
    {Σ, Δ |,| List.map (subst_td_many As Ps) Δ2, E & map (subst_tb_many As Ps) F} ⊢(Tgen) (subst_te_many As Ps e) ∈  subst_tt_many As Ps T.
  induction As as [| Ah Ats]; introv Htyp Hlen Pwft AE AF AD AD2 AP AEE Adist;
    destruct Ps as [| Ph Pts]; try solve [cbn in *; congruence].
  - cbn. cbn in Htyp.
    rewrite List.map_id.
    rewrite map_def.
    rewrite <- LibList_map.
    rewrite <- map_id; eauto using Tgen_from_any.
    intros. destruct x as [? [?]].
    cbv. auto.
  - cbn.
    inversions Adist.
    lets IH0: IHAts Σ Δ (List.map (subst_td Ah Ph) Δ2) (map (subst_tb Ah Ph) E) (map (subst_tb Ah Ph) F).
    lets IH: IH0 (subst_te Ah Ph e) (subst_tt Ah Ph T) Pts; clear IH0.
    rewrite <- (@subst_tb_id_on_fresh E Ah Ph).
    rewrite subst_tb_many_split.
    rewrite List.map_map in IH.
    eapply IH; auto with listin.
    + clear IH IHAts.
      cbn in Htyp. fold_delta.
      lets HT: typing_through_subst_te_gen Ph Htyp.
      rewrite <- map_concat.
      apply HT; auto with listin.
      * assert (WFT: wft Σ Δ Ph); auto with listin.
        apply* wft_weaken_simple.
      * repeat rewrite domDelta_app.
        repeat rewrite notin_union.
        repeat split; auto with listin.
        apply notin_dom_tc_vars.
        intro HF.
        apply from_list_spec in HF.
        apply LibList_mem in HF.
        false~.
    + introv Ain.
      rewrite <- domDelta_subst_td; auto with listin.
    + introv Ain.
      apply~ fv_env_subst; auto with listin.
    + auto with listin.
Qed.

Ltac generalize_typings :=
  match goal with
  | [ H: {?Σ, ?D, ?E} ⊢(?TT) ?e ∈ ?T |- _ ] =>
    match TT with
    | Tgen => fail 1
    | Treg => fail 1
    | _ => apply Tgen_from_any in H;
           try clear TT
    end
  end.

Lemma typing_replace_typ_gen : forall Σ Δ E F x vk T1 TT e U T2,
    {Σ, Δ, E & x ~ bind_var vk T1 & F} ⊢( TT) e ∈ U ->
    wft Σ Δ T2 ->
    entails_semantic Σ Δ (T1 ≡ T2) ->
    {Σ, Δ, E & x ~ bind_var vk T2 & F} ⊢(Tgen) e ∈ U.
  introv Typ.
  gen_eq K: (E & x ~ bind_var vk T1 & F). gen F x T1.
  induction Typ using typing_ind; introv EQ WFT Sem; subst; eauto;
    try solve [apply Tgen_from_any with Treg; eauto].
  - apply Tgen_from_any with Treg;
      econstructor. apply* okt_replace_typ.
  - destruct (classicT (x = x0)); subst.
    + lets: okt_is_ok H0.
      apply binds_middle_eq_inv in H; auto.
      inversions H.
      apply typing_eq with T2 Treg.
      * constructor.
        -- apply binds_concat_left.
           ++ apply binds_push_eq.
           ++ lets* [? ?]: ok_middle_inv H1.
        -- apply* okt_replace_typ.
      * apply~ teq_symmetry.
      * apply* okt_is_wft_2.
    + apply Tgen_from_any with Treg.
      constructor.
      * lets [? | [[? [? ?]] | [? [? ?]]]]: binds_middle_inv H; subst.
        -- apply~ binds_concat_right.
        -- false.
        -- apply~ binds_concat_left.
      * apply* okt_replace_typ.
  - apply Tgen_from_any with Treg.
    econstructor.
    introv xiL.
    lets IH: H0 xiL (F & x0 ~l V) x T0.
    repeat rewrite concat_assoc in IH.
    apply* IH.
  - apply Tgen_from_any with Treg.
    econstructor; eauto.
    introv xiL.
    lets IH: H1 xiL F x T0.
    repeat rewrite concat_assoc in IH.
    apply* IH.
    + apply~ wft_weaken_simple.
    + rewrite <- (List.app_nil_l (Δ |,| [tc_var X]*)).
      apply~ equation_weaken_var.
      cbn. auto.
  - apply Tgen_from_any with Treg.
    econstructor; eauto.
    introv xiL.
    lets IH: H1 xiL (F & x0 ~f T) x T1.
    repeat rewrite concat_assoc in IH.
    apply* IH.
  - apply Tgen_from_any with Treg.
    econstructor; eauto.
    introv xiL.
    lets IH: H0 xiL (F & x0 ~l V) x T1.
    repeat rewrite concat_assoc in IH.
    apply* IH.
  - apply Tgen_from_any with Treg.
    econstructor; eauto.
    introv In Alen Adist Afr xfr xAfr.
    lets Htmp: H4 In Alen Adist Afr xfr.
    lets IH: Htmp xAfr (F & x0 ~l open_tt_many_var Alphas (Cargtype def)) x T1. clear Htmp.
    repeat rewrite concat_assoc in IH.
    apply* IH.
    + repeat apply* wft_weaken_simple.
    + apply~ equations_weaken_match.
      rewrite List.map_length.
      lets [OKT [? WFT2]]: typing_regular Typ.
      inversions WFT2.
      lets OKS: okt_implies_okgadt OKT.
      inversion OKS as [? OKC].
      lets [? OKD]: OKC H0.
      lets indef: fst_from_zip In.
      lets OKE: OKD indef.
      inversions OKE.
      cbn.
      match goal with
      | [ H1: binds ?g ?A Σ, H2: binds ?g ?B Σ |- _ ] =>
        let H := fresh "H" in
        lets H: binds_ext H1 H2;
          inversions H
      end.
      auto.
Qed.

Lemma typing_replace_typ : forall Σ Δ E x vk T1 TT e U T2,
    {Σ, Δ, E & x ~ bind_var vk T1} ⊢( TT) e ∈ U ->
    entails_semantic Σ Δ (T1 ≡ T2) ->
    wft Σ Δ T2 ->
    {Σ, Δ, E & x ~ bind_var vk T2} ⊢( Tgen) e ∈ U.
  intros.
  rewrite <- (concat_empty_r (E & x ~ bind_var vk T2)).
  apply* typing_replace_typ_gen.
  fold_env_empty.
Qed.

Lemma remove_true_equation : forall Σ Δ1 Δ2 E e TT T U1 U2,
    {Σ, Δ1 |,| [tc_eq (U1 ≡ U2)]* |,| Δ2, E} ⊢(TT) e ∈ T ->
    entails_semantic Σ Δ1 (U1 ≡ U2) ->
    {Σ, Δ1 |,| Δ2, E} ⊢(TT) e ∈ T.
  introv Typ.
  gen_eq D3: (Δ1 |,| [tc_eq (U1 ≡ U2)]* |,| Δ2). gen Δ1 Δ2.
  lets: okt_strengthen_delta_eq.
  lets: wft_strengthen_equation.
  induction Typ using typing_ind; introv EQ Sem; subst; eauto.
  - econstructor; eauto.
    introv XFr.
    lets IH: H3 XFr Δ1 (Δ2 |,| [tc_var X]*).
    apply* IH.
  - econstructor; eauto.
    introv clin Hlen Hdist Afresh xfresh xfreshA.
    lets Htmp: H6 clin Hlen Hdist Afresh xfresh.
    lets IH: Htmp xfreshA Δ1
                  (Δ2 |,| tc_vars Alphas |,| equations_from_lists Ts (List.map (open_tt_many_var Alphas) (Crettypes def)));
      clear Htmp.
    repeat rewrite List.app_assoc in *.
    apply* IH.
  - lets: equation_strengthen H1 Sem.
    econstructor; eauto.
Qed.

Lemma remove_true_equations : forall Σ Δ E e TT V Ts Us,
    {Σ, Δ |,| equations_from_lists Ts Us, E} ⊢(TT) e ∈ V ->
    List.Forall2 (fun T U => entails_semantic Σ Δ (T ≡ U)) Ts Us ->
    {Σ, Δ, E} ⊢(TT) e ∈ V.
  induction 2 as [| T U Ts Us].
  - cbn in *. auto.
  - cbn in H.
    fold (equations_from_lists Ts Us) in H.
    apply* IHForall2.
    rewrite <- (List.app_nil_l ((Δ |,| equations_from_lists Ts Us) |, tc_eq (T ≡ U))) in H.
    forwards~ H2: remove_true_equation H.
    forwards* H3: equations_weaken_match (@nil var) Ts Us.
    apply* Forall2_eq_len.
Qed.

Lemma helper_equations_commute : forall Ts As Us Vs,
    List.length As = List.length Us ->
    List.length Ts = List.length Vs ->
    (forall A, List.In A As -> A \notin fv_typs Ts) ->
    equations_from_lists
      Ts
      (List.map (fun T : typ => subst_tt_many As Us (open_tt_many_var As T)) Vs)
    =
    List.map
      (subst_td_many As Us)
      (equations_from_lists Ts (List.map (open_tt_many_var As) Vs)).
  intros.
  rewrite (equations_from_lists_map _ (subst_tt_many As Us) (subst_tt_many As Us)).
  - f_equal.
    + gen Us.
      induction As as [| A As]; introv Len.
      * cbn. rewrite~ List.map_id.
      * destruct Us as [| U Us]; cbn.
        -- rewrite~ List.map_id.
        -- rewrite <- List.map_map.
           rewrite (List.map_ext_in (subst_tt A U) (fun x => x)).
           ++ rewrite List.map_id.
              apply~ IHAs; auto with listin.
           ++ intros T Tin.
              apply subst_tt_fresh.
              apply fv_typs_notin with Ts; auto with listin.
    + rewrite List.map_map. auto.
  - rewrite~ List.map_length.
  - introv In.
    gen H.
    clear.
    rename U into T2. rename T into T1.
    gen Us T1 T2.
    induction As as [| A As]; introv Len; destruct Us as [| U Us]; auto.
    cbn.
    rewrite~ IHAs.
Qed.

Theorem preservation_thm : preservation.
  Ltac find_hopen :=
    let Hopen := fresh "Hopen" in
    match goal with
    | H: forall x, x \notin ?L -> typing _ _ _ _ _ _ |- _ =>
      rename H into Hopen
    end.
  unfold preservation.
  introv Htyp.
  assert (term e) as Hterm; eauto using typing_implies_term.
  generalize e'.
  clear e'.
  induction Htyp; inversions Hterm;
    introv Hred; inversions Hred;
      try solve [eauto using Tgen_from_any];
      repeat generalize_typings.
  - (* app *)
    lets [U [HT EQ]]: inversion_typing_eq Htyp2.
    inversions HT.
    pick_fresh x.
    find_hopen. forwards~ K: (Hopen x).
    rewrite* (@subst_ee_intro lam_var x).
    expand_env_empty E.
    apply* typing_through_subst_ee_lam.
    fold_env_empty.
    apply teq_symmetry in EQ.
    lets [EQarg EQret]: inversion_eq_arrow EQ.
    apply typing_eq with T0 Tgen; auto.
    + apply* typing_replace_typ.
      lets*: typing_regular Htyp1.
    + lets* [? [? WFT]]: typing_regular Htyp2.
      inversion~ WFT.
  - (* tabs *)
    lets [U [HT EQ]]: inversion_typing_eq Htyp.
    inversions HT.

    apply teq_symmetry in EQ.
    lets: inversion_eq_typ_all EQ; subst.

    apply typing_eq with (open_tt T0 T1) Tgen.
    + pick_fresh X.
      rewrite* (@subst_te_intro X).
      rewrite* (@subst_tt_intro X).
      apply* typing_through_subst_te_3.
    + apply~ teq_open.
    + lets* [? [? WFT]]: typing_regular Htyp.
      apply~ wft_open.
  - (* fst *)
    lets [U [HT EQ]]: inversion_typing_eq Htyp.
    inversions HT.
    repeat generalize_typings.
    apply teq_symmetry in EQ.
    lets [EQarg EQret]: inversion_eq_tuple EQ.
    apply* typing_eq.
    lets* [? [? WFT]]: typing_regular Htyp.
    inversion~ WFT.
  - (* snd *)
    lets [U [HT EQ]]: inversion_typing_eq Htyp.
    inversions HT.
    repeat generalize_typings.
    apply teq_symmetry in EQ.
    lets [EQarg EQret]: inversion_eq_tuple EQ.
    apply* typing_eq.
    lets* [? [? WFT]]: typing_regular Htyp.
    inversion~ WFT.
  - (* fix *)
    pick_fresh f.
    rewrite* (@subst_ee_intro fix_var f).
    expand_env_empty E.
    apply* typing_through_subst_ee_fix.
    fold_env_empty.
  - (* let *)
    pick_fresh x.
    rewrite* (@subst_ee_intro lam_var x).
    expand_env_empty E.
    apply* typing_through_subst_ee_lam.
    fold_env_empty.
  - (* matchgadt *)
    (* we reduce to one of the branches which correspond to their definitions in type *)
    lets* [Def [nthDef Inzip]]: nth_error_implies_zip_swap Defs.
    lets HclTyp: H3 Inzip.
    remember (Cargtype Def) as argT.
    (* prepare fresh vars *)
    let fresh := gather_vars in
    lets* [Alphas [Hlen [Adist Afresh]]]: exist_alphas fresh (length Ts0).
    pick_fresh x.

    match goal with
    | [ H: term (trm_constructor ?A ?B ?C) |- _ ] =>
      inversions H
    end.

    (* extract info from well-formedness of GADT env Σ - our constructors are well formed *)
    lets [Hokt ?]: typing_regular Htyp.
    lets okgadt: okt_implies_okgadt Hokt.
    unfold okGadt in okgadt.
    destruct okgadt as [okΣ okCtors].
    lets [defsNe okDefs]: okCtors H0.
    lets indef: fst_from_zip Inzip.
    lets okCtor: okDefs indef.
    inversion okCtor.
    subst.
    (* clear H14 H15 Tarity0 Σ0. *)
    rename Carity into DefArity.

    (* replace open with subst+open_var *)
    rewrite~ (@subst_ee_intro lam_var x);
      [ idtac
      | apply fv_open_te_many;
        [ introv Tin;
          apply* fv_typs_notin
        | auto ]
      ].

    rewrite (@subst_te_intro_many Alphas _ Ts0); auto;
      [ idtac
      | introv Ain; subst; cbn; cbn in Afresh; lets*: Afresh Ain
      | introv Ain Tin; lets: Afresh Ain; apply* fv_typs_notin
      ].

    (* use fact that subst preserves typing *)
    lets [T' [Typ2 EQ]]: inversion_typing_eq Htyp.
    inversions Typ2.
    match goal with
    | [ H1: binds ?g ?A Σ, H2: binds ?g ?B Σ |- _ ] =>
      let H := fresh "H" in
      lets H: binds_ext H1 H2;
        inversions H
    end.

    rename H19 into TypCtorArg.
    match goal with
    | [ H1: List.nth_error Ctors cid = ?A, H2: List.nth_error Ctors cid = ?B |- _ ] =>
      let H := fresh "H" in
      assert (H: A = B); [ rewrite <- H2; auto | idtac ];
        inversions H
    end.
    rewrite (@subst_tt_intro_many Alphas _ Ts0) in TypCtorArg; auto.
    2: {
      intros A Ain; subst; cbn; cbn in Afresh.
      rewrite H14. auto.
    }
    2: {
      intros A U Ain Uin.
      lets WFT: H28 Uin.
      lets: wft_gives_fv WFT.
      intro HF.
      assert (HA: A \in domΔ Δ); auto.
      lets HA2: Afresh Ain.
      apply HA2. repeat rewrite in_union. repeat right~.
    }

    expand_env_empty E.
    match goal with
    | H: value (trm_constructor _ _ e1) |- _ =>
      inversions H
    end.
    eapply typing_through_subst_ee_lam with (subst_tt_many Alphas Ts0 (open_tt_many_var Alphas CargType)) Tgen _; auto; [idtac | eauto].

    (* instantiate the inductive hypothesis *)
    assert (AfreshL: forall A : var, List.In A Alphas -> A \notin L);
      [ introv Ain; lets*: Afresh Ain | idtac].
    assert (xfreshL: x \notin L); auto.
    assert (xfreshA: x \notin from_list Alphas); auto.

    lets* IH: H3 Inzip Alphas x Adist xfreshA.
    cbn in IH.

    rewrite subst_te_many_commutes_open; auto;
      [ idtac
      | introv Ain; lets: Afresh Ain;
        lets: from_list_spec2 Ain;
        intro; subst; auto
      ].

    fold (subst_tb_many Alphas Ts0 (bind_var lam_var (open_tt_many_var Alphas CargType))).
    rewrite <- map_single.
    fold_env_empty.

    rewrite subst_tt_many_free with Alphas Ts0 Tc;
      [ idtac | introv Ain; lets*: Afresh Ain ].

    assert (length CretTypes = length Ts).
    1: {
      lets [OKT [? WFT2]]: typing_regular Htyp.
      inversions WFT2.
      lets OKS: okt_implies_okgadt OKT.
      inversion OKS as [? OKC].
      lets [? OKD]: OKC H0.
      cbn in *.
      lets OKE: OKD indef.
      inversions OKE.
      match goal with
      | [ H1: binds ?g ?A Σ, H2: binds ?g ?B Σ |- _ ] =>
        let H := fresh "H" in
        lets H: binds_ext H1 H2;
          inversions H
      end.
      auto.
    }

    apply remove_true_equations with Ts (List.map (fun T => subst_tt_many Alphas Ts0 (open_tt_many_var Alphas T)) CretTypes).
    + assert (Hrew:
          equations_from_lists Ts (List.map (fun T : typ => subst_tt_many Alphas Ts0 (open_tt_many_var Alphas T)) CretTypes)
          =
          List.map (subst_td_many Alphas Ts0) (equations_from_lists Ts (List.map (open_tt_many_var Alphas) CretTypes))
        ).
      * apply~ helper_equations_commute.
        introv Ain. lets~ : Afresh Ain.
      * rewrite Hrew; clear Hrew.
        apply typing_through_subst_te_many with Tgen; trivial.
        -- intros A Ain.
           lets: Afresh Ain. auto.
        -- autorewrite with rew_env_dom.
           intros A Ain.
           apply notin_inverse.
           intro HF.
           apply xfreshA.
           rewrite in_singleton in HF. subst.
           apply from_list_spec2. auto.
        -- introv Ain.
           lets~ : Afresh Ain.
        -- introv Ain.
           rewrite~ equations_have_no_dom.
           apply* equations_from_lists_are_equations.
        -- introv Ain Tin.
           apply fv_typs_notin with Ts0; auto.
           lets: Afresh Ain.
           auto with listin.
        -- introv Ain; lets*: Afresh Ain.
    + assert (Hrew:
                open_tt_many Ts0 (typ_gadt CretTypes Name)
                =
                typ_gadt (List.map (open_tt_many Ts0) CretTypes) Name).
      * clear.
        rename Ts0 into Ts.
        rename CretTypes into Us.
        gen Us.
        induction Ts; introv.
        -- cbn. rewrite~ List.map_id.
        -- cbn. rewrite IHTs.
           f_equal.
           rewrite List.map_map.
           apply List.map_ext.
           intro T. auto.
      * rewrite Hrew in EQ; clear Hrew.
        assert (Hrew: (List.map (fun T : typ => subst_tt_many Alphas Ts0 (open_tt_many_var Alphas T)) CretTypes) = List.map (open_tt_many Ts0) CretTypes).
        1: {
          apply List.map_ext_in.
          intros T Tin.
          rewrite~ <- subst_tt_intro_many.
          - intros A Ain.
            rewrite~ H15.
          - intros A U Ain Uin.
            lets: Afresh Ain.
            apply fv_typs_notin with Ts0; auto.
        }
        rewrite Hrew; clear Hrew.
        lets EQ2: inversion_eq_typ_gadt EQ.
        rewrite <- (List.map_ext_in (fun T : typ => open_tt_many Ts0 T)).
        2: {
          intros T Tin.
          rewrite~ (@subst_tt_intro_many Alphas T Ts0).
          -- rewrite~ H15.
          -- introv Ain Uin. lets HF2: Afresh Ain.
             apply* fv_typs_notin.
        }
        -- rewrite~ List.map_length.
        -- apply EQ2.
Qed.
