Set Implicit Arguments.
Require Import Prelude.
Require Import Infrastructure.
Require Import Equations.
Require Import TLC.LibLN.
Require Import TLC.LibEnv.
Require Import Regularity.

Lemma okt_strengthen_simple : forall Σ D E F,
    okt Σ D (E & F) -> okt Σ D E.
Proof.
  introv O.
  induction F using env_ind.
  - fold_env_empty_H.
  - rewrite concat_assoc in O.
    apply IHF.
    inversion O.
    + false* empty_push_inv.
    + lets [? [? ?]]: eq_push_inv H; subst. auto.
Qed.

#[export] Hint Resolve okt_strengthen_simple.

Lemma wft_weaken_simple : forall Σ D1 D2 E,
    wft Σ D1 E ->
    wft Σ (D1 |,| D2) E.
Proof.
  intros.
  rewrite <- (List.app_nil_l (D1 |,| D2)).
  apply wft_weaken.
  clean_empty_Δ. auto.
Qed.

Lemma okt_weakening_delta : forall Σ D1 D2 E X,
    okt Σ (D1 |,| D2) E ->
    X # E ->
    X \notin domΔ D1 ->
    X \notin domΔ D2 ->
    okt Σ (D1 |,| [tc_var X]* |,| D2) E.
Proof.
  introv Hokt FE FD1 FD2; gen_eq D': (D1 |,| D2). gen D2.
  induction Hokt; econstructor; subst; auto using wft_weaken.
  apply notin_domΔ_eq.
  rewrite notin_domΔ_eq in H1. destruct H1.
  split; auto.
  apply notin_domΔ_eq; split; auto.
  cbn.
  rewrite notin_union; split; auto.
  apply notin_inverse.
  rewrite dom_concat in FE. rewrite dom_single in FE. auto.
Qed.

Lemma okt_weakening_delta_eq : forall Σ D1 D2 E eq,
    okt Σ (D1 |,| D2) E ->
    okt Σ (D1 |,| [tc_eq eq]* |,| D2) E.
Proof.
  introv Hokt; gen_eq D': (D1 |,| D2). gen D2.
  induction Hokt; econstructor; subst; auto using wft_weaken.
  repeat rewrite notin_domΔ_eq in *. destruct H1.
  destruct eq; cbn.
  split~.
Qed.

Lemma okt_weakening_delta_many_eq : forall Σ D1 D2 Deqs E,
    okt Σ (D1 |,| D2) E ->
    (forall eq, List.In eq Deqs -> exists ϵ, eq = tc_eq ϵ) ->
    okt Σ (D1 |,| Deqs |,| D2) E.
Proof.
  induction Deqs; introv Hok Heq.
  - clean_empty_Δ. auto.
  - destruct a.
    + lets: Heq (tc_var A); cbn in *; false* Heq; congruence.
    + fold_delta.
      rewrite <- List.app_assoc.
      apply okt_weakening_delta_eq.
      apply IHDeqs; auto.
      intros eq1 ?. lets Hin: Heq eq1.
      apply Hin. cbn. auto.
Qed.

Lemma okt_weakening_delta_many : forall Σ D1 D2 As E,
    (forall A, List.In A As -> A # E) ->
    (forall A, List.In A As -> A \notin domΔ D1) ->
    (forall A, List.In A As -> A \notin domΔ D2) ->
    DistinctList As ->
    okt Σ (D1 |,| D2) E ->
    okt Σ (D1 |,| tc_vars As |,| D2) E.
Proof.
  induction As as [| Ah Ats]; introv AE AD1 AD2 Adist Hok.
  - cbn. clean_empty_Δ. auto.
  - cbn. fold_delta.
    inversions Adist.
    apply okt_weakening_delta; auto with listin.
    apply notin_domΔ_eq. split; auto with listin.
    apply notin_dom_tc_vars.
    intro HF.
    apply from_list_spec in HF.
    apply LibList_mem in HF.
    auto.
Qed.

(* TODO try merging with others *)
Lemma wft_subst_tb_2 : forall Σ D1 D2 Z P T,
  wft Σ (D1 |,| [tc_var Z]* |,| D2) T ->
  wft Σ (D1 |,| D2) P ->
  wft Σ (D1 |,| D2) (subst_tt Z P T).
Proof.
  introv WT WP; gen_eq G: (D1 |,| [tc_var Z]* |,| D2). gen D2.
  induction WT; intros; subst; simpl subst_tt; auto.
  - case_var*.
    constructor.
    unfold is_var_defined in *.
    repeat destruct_app_list; auto using List.in_or_app.
    cbn in H. destruct H.
    * congruence.
    * contradiction.
  - apply_fresh* wft_all as Y.
    lets: wft_type.
    rewrite* subst_tt_open_tt_var.
    lets* IH: H0 Y (D2 |,| [tc_var Y]*).
    rewrite List.app_assoc in *.
    apply~ IH.
    rewrite <- List.app_assoc.
    apply* wft_weaken_simple.
  - apply* wft_gadt.
    + introv Tin.
      apply List.in_map_iff in Tin.
      destruct Tin as [U [? Tin]]; subst.
      apply* H0.
    + apply List.map_length.
Qed.

Lemma wft_subst_tb_3 : forall Σ D1 D2 Z P T,
  wft Σ (D1 |,| [tc_var Z]* |,| D2) T ->
  wft Σ D1 P ->
  wft Σ (D1 |,| List.map (subst_td Z P) D2) (subst_tt Z P T).
Proof.
  introv WT WP; gen_eq G: (D1 |,| [tc_var Z]* |,| D2). gen D2.
  induction WT; intros; subst; simpl subst_tt; auto.
  - case_var*.
    + apply~ wft_weaken_simple.
    + econstructor.
      unfold is_var_defined in *.
      apply List.in_app_iff.
      apply List.in_app_iff in H.
      destruct H.
      * left.
        clear WP. clear C.
        induction D2.
        -- inversion H.
        -- inversions H; cbn; auto.
      * apply List.in_app_iff in H.
        destruct H.
        -- cbn in H. destruct H as [EQ|EQ]; inversions EQ.
           false.
        -- right~.
  - apply_fresh* wft_all as Y.
    lets: wft_type.
    rewrite* subst_tt_open_tt_var.
    lets* IH: H0 Y (D2 |,| [tc_var Y]*).
  - apply* wft_gadt.
    + introv Tin.
      apply List.in_map_iff in Tin.
      destruct Tin as [U [? Tin]]; subst.
      apply* H0.
    + apply List.map_length.
Qed.

Lemma okt_push_fresh : forall Σ Δ E x vk T,
    okt Σ Δ (E & x ~ bind_var vk T) ->
    x # E /\ x \notin domΔ Δ.
Proof.
  induction E using env_ind; introv OK.
  - split~.
    inversions OK.
    + false* empty_push_inv.
    + lets [? [EQ ?]]: eq_push_inv H; inversions EQ.
      auto.
  - inversions OK.
    + false* empty_push_inv.
    + lets [? [EQ ?]]: eq_push_inv H; inversions EQ.
      split~.
Qed.

(* TODO maybe merge with the origl one *)
Lemma okt_is_wft_2 : forall Σ Δ E F x vk T,
    okt Σ Δ (E & x ~ bind_var vk T & F) -> wft Σ Δ T.
Proof.
  induction F using env_ind; introv OK.
  - rewrite concat_empty_r in OK.
    apply* okt_is_wft.
  - rewrite concat_assoc in OK.
    inversions OK.
    + false* empty_push_inv.
    + lets (?&?&?): eq_push_inv H. subst.
      apply* IHF.
Qed.

Lemma subst_td_eqs : forall Z P Ts Us,
    (forall U, List.In U Us -> Z \notin fv_typ U) ->
    List.map (subst_td Z P)
             (equations_from_lists Ts Us) =
    equations_from_lists (List.map (subst_tt Z P) Ts) Us.
Proof.
  induction Ts as [| T Ts]; destruct Us as [| U Us];
    introv ZU; cbn; auto.
  repeat f_equal.
  - rewrite~ subst_tt_fresh.
    auto with listin.
  - apply IHTs.
    auto with listin.
Qed.

Lemma okt_through_subst_tdtb : forall Σ D1 D2 E Z P,
    okt Σ (D1 |,| [tc_var Z]* |,| D2) E ->
    wft Σ D1 P ->
    okt Σ (D1 |,| List.map (subst_td Z P) D2) (map (subst_tb Z P) E).
Proof.
  induction E using env_ind; introv OKT WFT.
  - rewrite map_empty.
    constructor.
    apply* okt_implies_okgadt.
  - rewrite map_push.
    destruct v as [T]; cbn.
    lets [? ?]: okt_push_fresh OKT.
    constructor; auto.
    + apply* IHE.
    + apply* wft_subst_tb_3.
      apply* okt_is_wft.
    + repeat rewrite notin_domΔ_eq in *.
      destruct H0 as [[? ?] ?].
      split~.
      apply~ notin_domDelta_subst_td.
Qed.

Lemma okt_replace_typ : forall Σ Δ E F x vk T1 T2,
  okt Σ Δ (E & x ~ bind_var vk T1 & F) ->
  wft Σ Δ T2 ->
  okt Σ Δ (E & x ~ bind_var vk T2 & F).
Proof.
  induction F using env_ind; introv OK WFT.
  - rewrite concat_empty_r.
    rewrite concat_empty_r in OK.
    inversions OK.
    + false* empty_push_inv.
    + apply eq_push_inv in H.
      destruct H as [? [HS ?]]; inversions HS.
      constructor; auto.
  - rewrite concat_assoc in *.
    inversions OK.
    + false* empty_push_inv.
    + apply eq_push_inv in H.
      destruct H as [? [HS ?]]. inversions HS.
      constructor; auto.
      apply* IHF.
Qed.

Lemma okt_strengthen_delta_eq : forall Σ D1 D2 E eq,
    okt Σ (D1 |,| [tc_eq eq]* |,| D2) E -> okt Σ (D1 |,| D2) E.
Proof.
  introv OK.
  induction E using env_ind.
  - constructor.
    lets*: okt_implies_okgadt.
  - destruct v as [T].
    inversions OK.
    + lets*: empty_push_inv H.
    + lets [? [? ?]]: eq_push_inv H.
      match goal with
      | H: bind_var ?vk ?A = bind_var ?vk2 ?B |- _ => inversions H
      end.
      constructor; auto.
      * apply* wft_strengthen_equation.
      * rewrite notin_domΔ_eq in *; auto.
Qed.
