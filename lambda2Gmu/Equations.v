Require Import Prelude.
Require Import Infrastructure.

Open Scope list_scope.

(* Proofs regarding proposition 2.1 from the paper *)
Section SimpleEquationProperties.

  Variable Σ : GADTEnv.

  Lemma teq_reflexivity : forall Δ T,
      entails_semantic Σ Δ (T ≡ T).
    cbn.
    intros.
    auto.
  Qed.

  Lemma teq_symmetry : forall Δ T U,
      entails_semantic Σ Δ (T ≡ U) ->
      entails_semantic Σ Δ (U ≡ T).
    cbn. intros.
    symmetry.
    auto.
  Qed.

  Lemma teq_transitivity : forall Δ T U V,
      entails_semantic Σ Δ (T ≡ U) ->
      entails_semantic Σ Δ (U ≡ V) ->
      entails_semantic Σ Δ (T ≡ V).
    cbn. intros.
    transitivity (subst_tt' U Θ); auto.
  Qed.

  Lemma subst_has_no_fv : forall Σ Δ Θ,
      subst_matches_typctx Σ Δ Θ ->
      (forall X U, List.In (X, U) Θ -> fv_typ U = \{}).
  Proof.
    induction 1; introv Hin.
    - false.
    - cbn in Hin.
      destruct Hin as [Hin | Hin].
      + inversions Hin.
        lets Hfv: wft_gives_fv H.
        cbn in Hfv.
        apply~ fset_extens.
      + apply* IHsubst_matches_typctx.
    - apply* IHsubst_matches_typctx.
  Qed.

  Lemma teq_axiom : forall Δ T U,
      List.In (tc_eq (T ≡ U)) Δ ->
      entails_semantic Σ Δ (T ≡ U).
  Proof.
    unfold entails_semantic.
    induction Δ; introv Hin M.
    - contradiction.
    - cbn in Hin.
      destruct Hin as [Hin | Hin].
      + subst. inversion M.
        easy.
      + inversion M; auto.
        cbn.
        repeat rewrite subst_tt_inside; auto.
        * f_equal.
          apply IHΔ; auto.
        * introv Uin.
          lets Fr: subst_has_no_fv Uin.
          -- eauto.
          -- rewrite Fr. apply notin_empty.
        * introv Uin.
          lets Fr: subst_has_no_fv Uin.
          -- eauto.
          -- rewrite Fr. apply notin_empty.
  Qed.

End SimpleEquationProperties.

Ltac fold_from_list :=
  repeat progress match goal with
  | [ H: context[LibList.fold_right (fun (x : var) (acc : fset var) => \{ x} \u acc) \{} ?L]  |- _ ] =>
    fold (from_list L) in H
  | |- context[LibList.fold_right (fun (x : var) (acc : fset var) => \{ x} \u acc) \{} ?L] =>
    fold (from_list L)
                  end.

Lemma notin_from_list : forall As (A : var),
    ~ (List.In A As) ->
    A \notin from_list As.
  intros.
  intro HF.
  lets [A' [Hin Heq]]: in_from_list HF.
  subst.
  auto.
Qed.

Lemma spawn_unit_subst : forall Σ As,
    DistinctList As ->
    exists Θ, length Θ = length As /\ subst_matches_typctx Σ (tc_vars As) Θ /\ substitution_sources Θ = from_list As.
Proof.
  induction As as [| Ah Ats]; introv ADist.
  - cbn.
    exists (@nil (var * typ)).
    splits~.
    constructor.
  - inversions ADist.
    destruct IHAts as [LT [Len [Match Src]]]; auto.
    exists ((Ah, typ_unit) :: LT).
    splits.
    + cbn. auto.
    + constructor;
        fold (List.map tc_var Ats);
        fold (tc_vars Ats);
        auto.
      * rewrite Src.
        apply~ notin_from_list.
      * apply notin_dom_tc_vars.
        apply~ notin_from_list.
    + cbn.
      fold_from_list.
      fold (substitution_sources LT).
      rewrite Src.
      trivial.
Qed.

Lemma only_vars_is_tc_vars : forall Δ,
    (forall tc, List.In tc Δ -> exists A, tc = tc_var A) ->
    exists As, Δ = tc_vars As.
Proof.
  induction Δ as [| [A | eq] Δt].
  - cbn. intros. exists (@nil var). cbn. trivial.
  - cbn. intro Hin.
    lets* [Ats EQ]: IHΔt.
    exists (A :: Ats). cbn.
    fold (tc_vars Ats).
    f_equal.
    auto.
  - cbn. intro Hin.
    false~ Hin. congruence.
Qed.

Lemma contradictory_env_test_0 : forall Σ Δ,
    entails_semantic Σ Δ (typ_unit ≡ (typ_unit ** typ_unit)) ->
    contradictory_bounds Σ Δ.
Proof.
  introv Heq.
  unfold contradictory_bounds.
  intros.
  unfold entails_semantic in *.
  introv Hmatch.
  exfalso.
  lets HF: Heq Hmatch.
  rewrite subst_ttΘ_fresh in HF.
  - rewrite subst_ttΘ_fresh in HF.
    + false.
    + cbn. rewrite union_empty_r.
      rewrite~ inter_empty_r.
  - cbn.
    rewrite~ inter_empty_r.
Qed.

Lemma subst_ttΘ_into_abs : forall Θ A B,
    subst_tt' (A ==> B) Θ
    =
    (subst_tt' A Θ) ==> (subst_tt' B Θ).
  induction Θ as [| [X T] Θ]; cbn in *; trivial.
Qed.
Lemma subst_ttΘ_into_tuple : forall Θ A B,
    subst_tt' (A ** B) Θ
    =
    (subst_tt' A Θ) ** (subst_tt' B Θ).
  induction Θ as [| [X T] Θ]; cbn in *; trivial.
Qed.

Lemma contradictory_env_test : forall Σ Δ A B C D,
    entails_semantic Σ Δ ((A ==> B) ≡ (C ** D)) ->
    contradictory_bounds Σ Δ.
Proof.
  introv Heq.
  unfold contradictory_bounds.
  intros.
  unfold entails_semantic in *.
  introv Hmatch.
  exfalso.
  lets HF: Heq Hmatch.
  rewrite subst_ttΘ_into_abs in HF.
  rewrite subst_ttΘ_into_tuple in HF.
  congruence.
Qed.

Lemma empty_is_not_contradictory : forall Σ,
    ~ (contradictory_bounds Σ emptyΔ).
Proof.
  intros.
  intro HF.
  unfold contradictory_bounds in HF.
  asserts M: (subst_matches_typctx Σ emptyΔ (@nil (var*typ)));
    try econstructor.
  lets F: HF typ_unit (typ_unit ** typ_unit) (@nil (var * typ)) M.
  cbn in F.
  false.
Qed.

Lemma typing_exfalso : forall Σ Δ E e T1 T2 TT,
    {Σ, Δ, E} ⊢(TT) e ∈ T1 ->
    contradictory_bounds Σ Δ ->
    wft Σ Δ T2 ->
    {Σ, Δ, E} ⊢(Tgen) e ∈ T2.
  introv Typ Bounds.
  eapply typing_eq; eauto.
Qed.

Lemma inversion_typing_eq : forall Σ Δ E e T TT,
    {Σ, Δ, E} ⊢(TT) e ∈ T ->
    exists T',
      {Σ, Δ, E} ⊢(Treg) e ∈ T' /\ entails_semantic Σ Δ (T ≡ T').
Proof.
  introv Htyp.
  lets Htyp2: Htyp.
  induction Htyp;
    try match goal with
        | [ H: {Σ, Δ, E} ⊢(Treg) ?e ∈ ?T |- _ ] =>
          exists T; split~; auto using teq_reflexivity
        end.
  lets [T' [IHTyp IHeq]]: IHHtyp Htyp.
  exists T'.
  split~.
  eauto using teq_symmetry, teq_transitivity.
Qed.

Lemma subst_has_no_fv2 : forall Σ Δ Θ Y,
    subst_matches_typctx Σ Δ Θ ->
    (forall A U, List.In (A, U) Θ -> Y \notin fv_typ U).
Proof.
  introv M Hin.
  lets EQ: subst_has_no_fv M Hin.
  rewrite EQ.
  auto.
Qed.

Lemma inversion_eq_arrow : forall Σ Δ TA1 TB1 TA2 TB2,
    entails_semantic Σ Δ ((TA1 ==> TB1) ≡ (TA2 ==> TB2)) ->
    entails_semantic Σ Δ (TA1 ≡ TA2) /\
    entails_semantic Σ Δ (TB1 ≡ TB2).
Proof.
  introv Sem; cbn in *.
  split~;
       introv M;
    lets EQ: Sem M;
    repeat rewrite subst_tt_prime_reduce_arrow in EQ;
    inversion~ EQ.
Qed.

Lemma inversion_eq_tuple : forall Σ Δ TA1 TB1 TA2 TB2,
    entails_semantic Σ Δ ((TA1 ** TB1) ≡ (TA2 ** TB2)) ->
    entails_semantic Σ Δ (TA1 ≡ TA2) /\
    entails_semantic Σ Δ (TB1 ≡ TB2).
Proof.
  introv Sem; cbn in *.
  split~;
       introv M;
    lets EQ: Sem M;
    repeat rewrite subst_tt_prime_reduce_tuple in EQ;
    inversion~ EQ.
Qed.

Lemma inversion_eq_typ_all : forall Σ Δ T U,
    entails_semantic Σ Δ (typ_all T ≡ typ_all U) ->
    entails_semantic Σ Δ (T ≡ U).
Proof.
  introv Sem; cbn in *.
  introv M;
    lets EQ: Sem M;
    repeat rewrite subst_tt_prime_reduce_typ_all in EQ;
    inversion~ EQ.
Qed.

Lemma inversion_eq_typ_gadt : forall Σ Δ Ts Us N,
    List.length Ts = List.length Us ->
    entails_semantic Σ Δ (typ_gadt Ts N ≡ typ_gadt Us N) ->
    List.Forall2 (fun T U => entails_semantic Σ Δ (T ≡ U)) Ts Us.
Proof.
  introv Len Sem.
  apply F2_iff_In_zip.
  split~.
  intros T U In.
  cbn in *.
  introv M.
  lets EQ: Sem M.
  repeat rewrite subst_tt_prime_reduce_typ_gadt in EQ.
  inversion EQ as [EQ2].
  lets~ : lists_map_eq EQ2 In.
Qed.

Lemma equations_from_lists_map : forall F F1 F2 Ts Us,
    List.length Ts = List.length Us ->
    (forall T U, List.In (T,U) (zip Ts Us) -> F (tc_eq (T ≡ U)) = tc_eq (F1 T ≡ F2 U)) ->
    List.map F (equations_from_lists Ts Us)
    =
    equations_from_lists (List.map F1 Ts) (List.map F2 Us).
Proof.
  induction Ts as [| T Ts]; destruct Us as [| U Us];
    introv Len;  try solve [inversion~ Len].
  introv EQ.
  cbn.
  fold (equations_from_lists Ts Us).
  fold (equations_from_lists (List.map F1 Ts) (List.map F2 Us)).
  f_equal.
  - apply EQ. cbn. auto.
  - apply* IHTs.
    introv In.
    apply EQ. cbn. auto.
Qed.

Lemma empty_eq_is_equivalent : forall Σ T1 T2,
  entails_semantic Σ emptyΔ (T1 ≡ T2) ->
  T1 = T2.
Proof.
  introv Sem.
  cbn in *.
  lets M: Sem (@nil (var * typ)).
  forwards * : M.
  constructor.
Qed.