Set Implicit Arguments.
Require Import GMuAnnot.Prelude.
Require Import TLC.LibLogic.
Require Import TLC.LibLN.

Lemma fv_fold_general : forall A x (ls : list A) (P : A -> fset var) base,
    x \notin List.fold_left (fun (fv : fset var) (e : A) => fv \u P e) ls base ->
    x \notin base.
  induction ls.
  - introv Hfold. cbn in Hfold. auto.
  - introv Hfold. cbn in Hfold.
    assert (x \notin base \u P a).
    + apply* IHls.
    + auto.
Qed.

Lemma fv_fold_base : forall x ls base,
    x \notin List.fold_left (fun (fv : fset var) (T : typ) => fv \u fv_typ T) ls base ->
    x \notin base.
  lets*: fv_fold_general.
Qed.

Lemma fv_fold_base_clause : forall Z ls base,
    Z \notin List.fold_left (fun (fv : fset var) (cl : Clause) => fv \u fv_trm (clauseTerm cl)) ls base ->
    Z \notin base.
  intros.
  lets*: fv_fold_general (fun cl => fv_trm (clauseTerm cl)).
Qed.

Lemma fv_fold_in_general : forall A Z (e : A) (P : A -> fset var) ls base,
    Z \notin List.fold_left (fun (fv : fset var) (e' : A) => fv \u P e') ls base ->
    List.In e ls ->
    Z \notin P e.
  induction ls; introv ZIL Lin.
  - false*.
  - apply List.in_inv in Lin.
    destruct Lin.
    + cbn in ZIL.
      apply fv_fold_general in ZIL. subst. auto.
    + apply* IHls.
Qed.

Lemma fv_fold_in_clause : forall Z cl ls base,
    Z \notin List.fold_left (fun (fv : fset var) (cl : Clause) => fv \u fv_trm (clauseTerm cl)) ls base ->
    List.In cl ls ->
    Z \notin fv_trm (clauseTerm cl).
  intros.
  lets*: fv_fold_in_general (fun cl => fv_trm (clauseTerm cl)) ls.
Qed.

Lemma fv_fold_in : forall Z x ls base,
    Z \notin List.fold_left (fun (fv : fset var) (T : typ) => fv \u fv_typ T) ls base ->
    List.In x ls ->
    Z \notin fv_typ x.
  lets*: fv_fold_in_general.
Qed.

Lemma notin_fold : forall A B (ls : list A) z x (P : A -> fset B),
    (forall e, List.In e ls -> x \notin P e) ->
    x \notin z ->
    x \notin List.fold_left (fun fv e => fv \u P e) ls z.
  induction ls; introv FPe Fz; cbn; eauto.
  apply* IHls.
  - eauto with listin.
  - rewrite notin_union; split*.
    eauto with listin.
Qed.

#[export] Hint Resolve fv_fold_base fv_fold_in fv_fold_general fv_fold_in_general.

Lemma fv_open : forall T U k,
    fv_typ (open_tt_rec k U T) = (fv_typ T \u fv_typ U)
    \/ fv_typ (open_tt_rec k U T) = fv_typ T.
  induction T using typ_ind'; introv;
    try solve [
          unfold open_tt_rec; crush_compare; cbn; eauto using union_empty_l
        | cbn; eauto
        | cbn; fold (open_tt T1 U); fold (open_tt T2 U);
          rewrite union_distribute;
          apply* subset_union_2
        ].
  - cbn.
    lets* IH1: IHT1 U k.
    lets* IH2: IHT2 U k.
    destruct IH1 as [IH1 | IH1];
      destruct IH2 as [IH2 | IH2];
      rewrite IH1; rewrite IH2; eauto.
    + left.
      lets*: union_distribute.
    + left.
      rewrite <- union_assoc.
      rewrite <- union_assoc.
      rewrite (union_comm (fv_typ T2) (fv_typ U)).
      trivial.
    + rewrite union_assoc. eauto.
  - cbn.
    lets* IH1: IHT1 U k.
    lets* IH2: IHT2 U k.
    destruct IH1 as [IH1 | IH1];
      destruct IH2 as [IH2 | IH2];
      rewrite IH1; rewrite IH2; eauto.
    + left. eauto using union_distribute.
    + left.
      rewrite <- union_assoc.
      rewrite <- union_assoc.
      rewrite (union_comm (fv_typ T2) (fv_typ U)).
      trivial.
    + rewrite union_assoc. eauto.
  - cbn.
    induction ls.
    + cbn. eauto.
    + assert (Has: List.Forall
           (fun T : typ =>
            forall (U : typ) (k : nat),
            fv_typ (open_tt_rec k U T) = fv_typ T \u fv_typ U \/
            fv_typ (open_tt_rec k U T) = fv_typ T) ls).
      * rewrite List.Forall_forall in *.
        eauto with listin.
      * lets* IH: IHls Has.
        destruct IH as [IH | IH].
        -- left.
           cbn.
           repeat rewrite union_fold_detach in *.
           rewrite IH.
           rewrite <- union_assoc.
           rewrite List.Forall_forall in *.
           lets* Ha: H a U k; eauto with listin.
           destruct Ha as [Ha | Ha].
           ++ rewrite union_distribute.
              rewrite union_assoc.
              f_equal. eauto.
           ++ rewrite <- union_assoc.
              rewrite (union_comm (fv_typ a) (fv_typ U)).
              f_equal. f_equal. eauto.
        -- rewrite List.Forall_forall in *.
           lets* Ha: H a U k; eauto with listin.
           destruct Ha as [Ha | Ha].
           ++ left.
              cbn.
              repeat rewrite union_fold_detach.
              rewrite IH.
              rewrite <- union_assoc.
              f_equal. eauto.
           ++ right.
              cbn.
              repeat rewrite union_fold_detach.
              f_equal; eauto.
Qed.

Lemma fv_smaller : forall T U k,
    fv_typ (open_tt_rec k U T) \c (fv_typ T \u fv_typ U).
  introv.
  lets* characterized: fv_open T U k.
  destruct characterized as [Hc | Hc]; rewrite Hc; eauto.
Qed.

Lemma fv_typs_notin : forall Ts T X,
    List.In T Ts ->
    X \notin fv_typs Ts ->
    X \notin fv_typ T.
  introv Hin Hall.
  induction Ts as [| Th Tt].
  - inversion Hin.
  - lets* Hem: (classicT (Th = T)).
    destruct Hem.
    + subst.
      cbn in Hall.
      eauto.
    + inversion Hin.
      * contradiction.
      * apply* IHTt.
        cbn in Hall. eauto.
Qed.

Lemma notin_fv_tt_open : forall Y X T,
    X \notin fv_typ (T open_tt_var Y) ->
    X \notin fv_typ T.
Proof.
  unfold open_tt.
  introv FO.
  lets* characterized: fv_open T (typ_fvar Y) 0.
  destruct characterized as [Hc | Hc]; rewrite Hc in FO; eauto.
Qed.

Lemma fv_smaller_many : forall As T,
    fv_typ (open_tt_many_var As T) \c (fv_typ T \u from_list As).
  induction As as [| Ah Ats]; introv.
  - cbn. eauto.
  - cbn.
    fold (from_list Ats).
    fold (open_tt_many_var Ats (T open_tt_var Ah)).
    lets IH: IHAts (T open_tt_var Ah).
    intros x xin.
    lets Hin: IH xin.
    rewrite in_union in Hin.
    rewrite union_assoc.
    destruct Hin as [Hin | Hin].
    + lets Hs: fv_smaller T (typ_fvar Ah) 0.
      fold (open_tt T (typ_fvar Ah)) in Hs.
      lets Hf: Hs Hin. cbn in Hf.
      rewrite* in_union.
    + rewrite* in_union.
Qed.

Lemma fv_open_tt : forall x T1 T2 k,
    x \notin fv_typ T1 ->
    x \notin fv_typ T2 ->
    x \notin fv_typ (open_tt_rec k T1 T2).
  introv f1 f2.
  unfold open_tt.
  lets [Ho | Ho]: fv_open T2 T1 k; rewrite Ho; eauto.
Qed.

Lemma fv_open_te : forall e k x T,
    x \notin fv_trm e ->
    x \notin fv_typ T ->
    x \notin fv_trm (open_te_rec k T e).
  induction e using trm_ind'; introv efresh Tfresh;
    try solve [
          cbn in *; eauto
        | cbn in *;
          rewrite notin_union;
          split*; apply* fv_open_tt
        ].
  - cbn. cbn in efresh.
    apply notin_fold.
    + intros T' Tin.
      unfold open_typlist_rec in Tin.
      lets Tin2: Tin.
      apply List.in_map_iff in Tin2.
      destruct Tin2 as [T'' [T'eq T''in]].
      subst.
      apply* fv_open_tt.
    + apply* IHe.
  - cbn in *.
    repeat rewrite notin_union.
    splits~; apply* fv_open_tt.
  - cbn in *.
    rewrite notin_union; split; try apply~ fv_open_tt.
    apply notin_fold.
    + intros cl clin.
      apply List.in_map_iff in clin.
      destruct clin as [[cl'A cl'T] [cl'eq cl'in]].
      subst. cbn.

      rewrite List.Forall_forall in *.
      fold (clauseTerm (clause cl'A cl'T)).
      apply* H.

      cbn.
      fold (clauseTerm (clause cl'A cl'T)).
      rewrite notin_union in efresh.
      destruct efresh.
      apply* fv_fold_in_clause.
    + apply* IHe.
      rewrite notin_union in efresh.
      destruct efresh.
      apply* fv_fold_base_clause.
Qed.

Lemma fv_open_te_many : forall Ts e x,
    (forall T, List.In T Ts -> x \notin fv_typ T) ->
    x \notin fv_trm e ->
    x \notin fv_trm (open_te_many Ts e).
  induction Ts as [| Th Tts]; introv Tfresh efresh.
  - cbn. trivial.
  - cbn. apply IHTts.
    + introv Tin. eauto with listin.
    + unfold open_te.
      apply fv_open_te; eauto with listin.
Qed.

Lemma fv_env_extend : forall E x vk T,
    fv_env (E & x ~ bind_var vk T) = fv_typ T \u fv_env E.
  intros.
  rewrite concat_def.
  rewrite single_def.
  cbn.
  fold (fv_env E).
  trivial.
Qed.

Lemma notin_env_inv : forall E X x vk T,
    X \notin fv_env (E & x ~ bind_var vk T) ->
    X \notin fv_env E /\ X \notin fv_typ T.
  introv Fr.
  rewrite fv_env_extend in Fr.
  rewrite* notin_union in Fr.
Qed.

Lemma notin_domΔ_eq : forall D1 D2 X,
    X \notin domΔ (D1 |,| D2) <->
    X \notin domΔ D1 /\ X \notin domΔ D2.
  induction D2; intros; constructor;
    try solve [cbn in *; intuition]; intro H;
      destruct a; try destruct eq; cbn in *;
        repeat rewrite notin_union in *;
        destruct (IHD2 X) as [IH1 IH2];
        intuition.
Qed.

Lemma in_domΔ_eq : forall D1 D2 X,
    X \in domΔ (D1 |,| D2) <->
    X \in domΔ D1 \/ X \in domΔ D2.
  induction D2; intros; constructor;
    intro H;
    try solve [
          cbn in *; intuition
        | destruct a; try destruct eq; cbn in *;
          repeat rewrite in_union in *;
          destruct (IHD2 X) as [IH1 IH2];
          intuition
        ].
  destruct H.
  - cbn. auto.
  - cbn in H. false* in_empty_inv.
Qed.

Lemma fold_empty : forall Ts,
    (forall T : typ, List.In T Ts -> fv_typ T = \{}) ->
    List.fold_left (fun (fv : fset var) (T : typ) => fv \u fv_typ T) Ts \{} = \{}.
  induction Ts as [ | Th]; introv Fv; cbn; eauto.
  lets* Hempty: Fv Th.
  rewrite Hempty; eauto with listin.
  rewrite union_empty_r.
  eauto with listin.
Qed.

Lemma in_fold_exists : forall TV TT P ls Z X,
    X \in List.fold_left (fun (fv : fset TV) (T : TT) => fv \u P T) ls Z ->
          (exists T, List.In T ls /\ X \in P T) \/ X \in Z.
  induction ls; introv Hin.
  - right.
    cbn in *. eauto.
  - cbn in Hin.
    lets* IH: IHls (Z \u P a) X Hin.
    destruct IH as [IH | IH].
    + destruct IH as [T [Tin PT]].
      left. exists T. eauto with listin.
    + rewrite in_union in IH.
      destruct IH as [IH | IH]; eauto with listin.
Qed.

Lemma fv_subst_tt : forall X Z P T,
    X \notin fv_typ T ->
    X \notin fv_typ P ->
    X \notin fv_typ (subst_tt Z P T).
  induction T using typ_ind'; introv FT FP; cbn in *; auto.
  - case_if*.
  - apply notin_fold.
    + intros T Tin.
      apply List.in_map_iff in Tin.
      destruct Tin as [U [? ?]]. subst.
      rewrite List.Forall_forall in H.
      apply* H.
    + auto.
Qed.

Lemma fv_env_subst : forall X Z P E,
    X \notin fv_env E ->
    X \notin fv_typ P ->
    X \notin fv_env (map (subst_tb Z P) E).
  intros.
  induction E using env_ind.
  - rewrite map_empty. auto.
  - destruct v as [T]; lets [? ?]: notin_env_inv H.
    rewrite map_concat.
    rewrite map_single.
    cbn.
    rewrite fv_env_extend.
    rewrite notin_union.
    split.
    + apply* fv_subst_tt.
    + apply* IHE.
Qed.

Lemma notin_dom_tc_vars : forall As x,
    x \notin from_list As ->
    x \notin domΔ (tc_vars As).
  induction As; introv Hin; cbn in *; auto.
  rewrite notin_union. split; auto.
  fold (tc_vars As).
  apply IHAs.
  fold (from_list As) in Hin.
  auto.
Qed.

Lemma notin_env_binds:
  forall (Z : var) (E : env bind) (x : var) vk (T : typ),
    binds x (bind_var vk T) E ->
    Z \notin fv_env E -> Z \notin fv_typ T.
Proof.
  induction E using env_ind; introv Hbind FE.
  - false* binds_empty_inv.
  - lets [[? ?] | [? ?]]: binds_push_inv Hbind; subst;
      try destruct v; lets* [? ?]: notin_env_inv FE.
Qed.

Lemma domDelta_in:
  forall (Δ : typctx) (X : var), List.In (tc_var X) Δ -> \{ X} \c domΔ Δ.
Proof.
  induction Δ; introv Hin.
  - inversion Hin.
  - cbn in Hin.
    destruct Hin as [Hin | Hin].
    + subst. cbn. eauto.
    + cbn. destruct a.
      * assert (\{ X } \c domΔ Δ).
        -- apply~ IHΔ.
        -- introv HX.
           rewrite in_union.
           right~.
      * destruct eq.
        introv In.
        repeat rewrite in_union.
        repeat right.
        apply* IHΔ.
Qed.

Lemma subset_fold : forall T U P Xs E C,
    (forall x : T, List.In x Xs -> P x \c C) ->
    E \c C ->
    List.fold_left (fun (fv : fset U) (x : T) => fv \u P x) Xs E \c C.
  induction Xs; introv HXs HE;
    cbn; auto.
  apply IHXs.
  - auto with listin.
  - rewrite <- union_same.
    lets Hsu: subset_union_2 E (P a) C C.
    apply~ Hsu.
    auto with listin.
Qed.

Lemma wft_gives_fv : forall Σ Δ T,
    wft Σ Δ T ->
    fv_typ T \c domΔ Δ.
  induction 1; cbn; eauto;
    try solve [
          rewrite <- union_same;
          lets Hsu: subset_union_2 (fv_typ T1) (fv_typ T2) (domΔ Δ) (domΔ Δ);
          apply ~Hsu
        ].
  - unfold is_var_defined in H.
    apply~ domDelta_in.
  - introv Hx.
    pick_fresh X.
    assert (Fr2: X \notin L); auto.
    assert (x <> X); auto.
    lets IH: H0 Fr2.
    lets Hopen: fv_open T2 (typ_fvar X) 0.
    fold (T2 open_tt_var X) in Hopen.
    destruct Hopen as [Ho | Ho].
    + rewrite Ho in IH.
      assert (Hu: x \in fv_typ T2 \u fv_typ (typ_fvar X)).
      * rewrite~ in_union.
      * lets Hd: IH Hu.
        apply in_domΔ_eq in Hd.
        destruct~ Hd as [? | Hd].
        cbn in Hd.
        rewrite union_empty_r in Hd.
        rewrite in_singleton in Hd.
        false.
    + rewrite Ho in IH.
      lets Hd: IH Hx.
      apply in_domΔ_eq in Hd.
      destruct Hd as [| Hd]; auto.
      cbn in Hd.
      rewrite union_empty_r in Hd.
      rewrite in_singleton in Hd.
      false.
  - apply~ subset_fold.
Qed.

Lemma equations_have_no_dom : forall Deqs,
    (forall eq, List.In eq Deqs -> exists ϵ, eq = tc_eq ϵ) ->
    domΔ Deqs = \{}.
  induction Deqs; cbn; auto; destruct a; intros.
  - lets HF: H (tc_var A).
    false~ HF.
  - apply IHDeqs.
    intros. auto.
Qed.

Lemma subst_match_notin_srcs2 : forall O X U,
    List.In (X, U) O ->
    X \in substitution_sources O.
  induction O; introv Hin.
  - inversion Hin.
  - cbn in Hin.
    destruct Hin.
    + subst. cbn. rewrite in_union. left. apply in_singleton_self.
    + cbn.
      rewrite in_union. right. fold_subst_src.
      apply* IHO.
Qed.

Lemma subst_src_app : forall O1 O2,
    substitution_sources (O1 |,| O2) = substitution_sources O1 \u substitution_sources O2.
  induction O2.
  - cbn. fold_subst_src.
    rewrite~ union_empty_r.
  - cbn. fold_subst_src.
    rewrite IHO2.
    repeat rewrite union_assoc.
    rewrite~ (union_comm \{ fst a}).
Qed.

Lemma substitution_sources_from_in : forall O A T,
    List.In (A, T) O ->
    A \in substitution_sources O.
  induction O; introv Oin; cbn in *.
  - false.
  - fold_subst_src.
    rewrite in_union.
    destruct Oin.
    + subst. cbn.
      left. apply in_singleton_self.
    + right. apply* IHO.
Qed.

Lemma fv_delta_app : forall D1 D2,
    fv_delta (D1 |,| D2) = fv_delta D1 \u fv_delta D2.
  induction D2 as [| [X | [T1 T2]]];
    cbn; auto using union_empty_r.
  rewrite IHD2.
  repeat rewrite union_assoc.
  f_equal.
  rewrite union_comm.
  repeat rewrite union_assoc.
  auto.
Qed.

Lemma fv_delta_alphas : forall As,
    fv_delta (tc_vars As) = \{}.
  induction As; cbn; auto.
Qed.

Lemma fv_delta_equations : forall A Ts Us,
    (forall T, List.In T Ts -> A \notin fv_typ T) ->
    (forall U, List.In U Us -> A \notin fv_typ U) ->
    A \notin fv_delta (equations_from_lists Ts Us).
  induction Ts as [| T Ts]; cbn; introv FrT FrU; auto.
  destruct Us as [| U Us]; cbn; auto.
  repeat rewrite notin_union.
  split; auto with listin.
Qed.

Lemma fold_left_subset_base : forall T U P As B,
    B \c List.fold_left (fun (fv : fset U) (x : T) => fv \u P x) As B.
  induction As; introv; cbn; auto.
  lets IH: IHAs (B \u P a).
  apply subset_transitive with (B \u P a); auto.
Qed.

Lemma fold_left_subset : forall T A P As B,
    List.In A As ->
    P A \c List.fold_left (fun (fv : fset var) (x : T) => fv \u P x) As B.
  induction As; introv In.
  - inversion In.
  - inversions In.
    + cbn.
      apply subset_transitive with (B \u P A);
        auto using fold_left_subset_base.
    + cbn.
      apply~ IHAs.
Qed.

Lemma domDelta_app : forall D1 D2,
    domΔ (D1 |,| D2) = domΔ D1 \u domΔ D2.
  induction D2 as [| [|]]; cbn; auto.
  - rewrite~ union_empty_r.
  - rewrite union_comm.
    rewrite (union_comm (\{A})).
    rewrite IHD2.
    rewrite~ union_assoc.
Qed.

Lemma distinct_split1 : forall O1 O2,
    DistinctList (List.map fst O1 |,| List.map fst O2) ->
    substitution_sources O1 \n substitution_sources O2 = \{}.
  induction O2 as [| [A U]]; cbn; introv D; fold_subst_src.
  - apply inter_empty_r.
  - inversions D.
    lets SS: IHO2 H2.
    rewrite inter_comm.
    rewrite union_distributes.
    rewrite inter_comm in SS.
    rewrite SS.
    rewrite union_empty_r.
    apply~ fset_extens.
    intros x HF.
    false.
    rewrite in_inter in HF. destruct HF as [HF1 HF2].
    rewrite in_singleton in HF1. subst.
    apply H1.
    apply List.in_or_app. right.
    gen HF2. clear. intro H.
    induction O1 as [| [X V]]; cbn in *.
    + apply* in_empty_inv.
    + fold_subst_src.
      rewrite in_union in H. destruct H as [H | H].
      * left. rewrite~ in_singleton in H.
      * right~.
Qed.

Lemma sources_list_fst : forall A O,
  List.In A (List.map fst O) ->
  A \in substitution_sources O.
  induction O as [| [X V]]; cbn; introv In; fold_subst_src.
  - false.
  - destruct In; subst; rewrite in_union.
    + left. apply in_singleton_self.
    + right~.
Qed.

Lemma subst_td_alphas : forall Z P As,
    List.map (subst_td Z P) (tc_vars As) =
    tc_vars As.
  induction As; cbn; auto.
  rewrite List.map_map.
  f_equal.
Qed.

Lemma domDelta_subst_td : forall Δ Z P,
    domΔ Δ = domΔ (List.map (subst_td Z P) Δ).
  induction Δ as [| [| []]]; eauto; introv; cbn.
  f_equal. auto.
Qed.

Lemma notin_domDelta_subst_td : forall x Δ Z P,
  x \notin domΔ Δ ->
  x \notin domΔ (List.map (subst_td Z P) Δ).
  induction Δ as [| [|[]]]; introv FR; cbn in *; auto.
Qed.
