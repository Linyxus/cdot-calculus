Set Implicit Arguments.
Require Import GMuAnnot.Prelude.
Require Import GMuAnnot.Infrastructure.
Require Import GMuAnnot.Equations.
Require Import TLC.LibLN.
Require Import TLC.LibEnv.


(** * Regularity *)
(**
Defines basic properties of well formed types and typing judgement.
*)

(** * Properties of well-formedness of a type in an environment *)

(** If a type is well-formed in an environment then it is locally closed. *)

Lemma type_from_wft : forall Σ E T,
  wft Σ E T -> type T.
Proof.
  induction 1; eauto.
Qed.

#[export] Hint Resolve type_from_wft.

(* Lemma values_decidable : forall t, *)
(*     term t -> *)
(*     (value t \/ ~ (value t)). *)
(*   induction t; intro H; *)
(*   inversion H; subst; try solve [ *)
(*                      right; intro Hv; inversion Hv *)
(*                    | left; econstructor *)
(*                           ]. *)
(*   -  *)
(*   - match goal with *)
(*     | H: term t |- _ => rename H into Ht end. *)
(*     apply IHt in Ht. *)
(*     destruct Ht as [Hv | Hv]. *)
(*     + left; constructor*. *)
(*     + right. intro Hv'. inversion* Hv'. *)
(*   - match goal with *)
(*     | H: term t1 |- _ => rename H into Ht1 end. *)
(*     match goal with *)
(*     | H: term t2 |- _ => rename H into Ht2 end. *)
(*     apply IHt1 in Ht1. *)
(*     apply IHt2 in Ht2. *)
(*     destruct Ht1; *)
(*       destruct Ht2; *)
(*       try solve [ left; econstructor; eauto *)
(*                 | right; intro Hv; inversion Hv; congruence ]. *)
(*   - left; econstructor. *)
(*     econstructor; eauto. *)
(*   - left; econstructor. *)
(*     econstructor; eauto. *)
(* Qed. *)

Ltac IHap IH := eapply IH; eauto;
                try (unfold open_ee; rewrite <- open_ee_var_preserves_size);
                try (unfold open_te; rewrite <- open_te_var_preserves_size);
                cbn; lia.

(* Lemma wft_weaken : forall Σ Δ E F G T, *)
(*     wft Σ Δ (E & G) T -> *)
(*     ok (E & F & G) -> *)
(*     wft Σ Δ (E & F & G) T. *)
(*   introv Hwft Hok. gen_eq K: (E & G). gen E F G. *)
(*   induction Hwft; intros; subst; auto. *)
(*   - (* case: var *) *)
(*     apply (@wft_var Σ (E0 & F & G) X).  apply* binds_weaken. *)
(*   - (* case: all *) *)
(*     apply_fresh* wft_all as X. apply_ih_bind* H0. *)
(*   - econstructor; eauto. *)
(* Qed. *)

#[export] Hint Resolve subst_tt_type subst_te_term subst_ee_term.
#[export] Hint Resolve subst_te_value subst_ee_value.

Lemma okt_is_ok : forall Σ Δ E, okt Σ Δ E -> ok E.
  introv. intro Hokt.
  induction Hokt; eauto.
Qed.
#[export] Hint Extern 1 (ok _) => apply okt_is_ok.


Lemma wft_from_env_has_typ : forall Σ Δ x vk U E,
    okt Σ Δ E -> binds x (bind_var vk U) E -> wft Σ Δ U.
Proof.
  induction E using env_ind; intros Ok B.
  false* binds_empty_inv.
  inversions Ok.
  - false (empty_push_inv H).
  - destruct (eq_push_inv H) as [? [? ?]]; subst. clear H.
    lets [[? HT] | [? HB]]: binds_push_inv B.
    + inversion* HT.
    + apply* IHE.
Qed.

Lemma wft_strengthen_typ : forall Σ D1 D2 U T,
    U \notin fv_typ T ->
    wft Σ (D1 |,| [tc_var U]* |,| D2) T -> wft Σ (D1 |,| D2) T.
Proof.
  introv Ufresh Hwft. gen_eq G: (D1 |,| [tc_var U]* |,| D2). gen D2.
  induction Hwft; intros D2 EQ; cbn in Ufresh; subst; auto.
  - apply* wft_var.
    repeat destruct_in_app;
      unfold is_var_defined; eauto using List.in_or_app.
    cbn in H. intuition. inversions H0. exfalso; eauto using in_singleton_self.
  - (* todo: binds_cases tactic *)
    match goal with
    | H: forall X, X \notin L -> ?P3 -> forall F0, ?P1 -> ?P2 |- _ =>
      rename H into H_ctxEq_implies_wft end.
    apply_fresh* wft_all as Y.
    lets* IH: H_ctxEq_implies_wft Y (D2 |, tc_var Y).
    + lets [Hfv | Hfv]: fv_open T2 (typ_fvar Y) 0;
        cbn in Hfv; unfold open_tt; rewrite Hfv; eauto.
  - econstructor; eauto.
Qed.

Lemma wft_strengthen_equation : forall Σ D1 D2 ϵ T,
    wft Σ (D1 |,| [tc_eq ϵ]* |,| D2) T ->
    wft Σ (D1 |,| D2) T.
  introv Hwft. gen_eq G: (D1 |,| [tc_eq ϵ]* |,| D2). gen D2.
  induction Hwft; intros D2 EQ; subst; auto.
  - apply* wft_var.
    unfold is_var_defined in *.
    lets [Hin | Hin]: List.in_app_or H.
    + apply List.in_or_app; left~.
    + lets [? | ?]: List.in_app_or Hin.
      * inversion H0; false*.
      * apply List.in_or_app; right~.
  - apply_fresh wft_all as X.
    lets IH: H0 X (D2 |, tc_var X); auto.
  - econstructor; eauto.
Qed.

Lemma wft_strengthen_equations : forall Σ D1 Deqs D2 T,
    wft Σ (D1 |,| Deqs |,| D2) T ->
    (forall eq, List.In eq Deqs -> exists ϵ, eq = tc_eq ϵ) ->
    wft Σ (D1 |,| D2) T.
  induction Deqs; introv Hwft Heqs.
  - clean_empty_Δ. auto.
  - destruct a.
    + lets [? ?]: Heqs (tc_var A); auto with listin.
      false~.
    + fold_delta.
      apply IHDeqs.
      * apply* wft_strengthen_equation.
        repeat rewrite List.app_assoc in *; eauto.
      * intros eq1 Hin.
        lets Hl: Heqs eq1.
        apply Hl.
        cbn. right~.
Qed.

Lemma wft_strengthen_typ_many : forall Σ As Δ T,
    wft Σ (Δ |,| tc_vars As) T ->
    (forall A, List.In A As -> A \notin fv_typ T) ->
    wft Σ Δ T.
  induction As as [| Ah Ats]; introv Hwft Asfresh.
  - cbn in *. clean_empty_Δ.
    trivial.
  - cbn in *. fold_delta. fold_delta.
    apply* IHAts.
    lets W: wft_strengthen_typ Σ (Δ |,| tc_vars Ats) emptyΔ.
    clean_empty_Δ.
    apply~ W.
Qed.
(* Lemma wft_strengthen : forall Σ Δ E F x U T, *)
(*  wft Σ Δ (E & (x ~: U) & F) T -> wft Σ (E & F) T. *)
(* Proof. *)
(*   introv Hwft. gen_eq G: (E & (x ~: U) & F). gen F. *)
(*   induction Hwft; intros F EQ; subst; auto. *)
(*   - *)
(*     match goal with *)
(*     | H: binds _ _ _ |- _ => *)
(*       rename H into Hbinds_bindtyp end. *)
(*     apply* (@wft_var). *)
(*     destruct (binds_concat_inv Hbinds_bindtyp) as [?|[? Hbinds2]]. *)
(*     + apply~ binds_concat_right. *)
(*     + destruct (binds_push_inv Hbinds2) as [[? ?]|[? ?]]. *)
(*       * subst. false. *)
(*       * apply~ binds_concat_left. *)
(*   - (* todo: binds_cases tactic *) *)
(*     match goal with *)
(*     | H: forall X, X \notin L -> forall F0, ?P1 -> ?P2 |- _ => *)
(*       rename H into H_ctxEq_implies_wft end. *)
(*     apply_fresh* wft_all as Y. apply_ih_bind* H_ctxEq_implies_wft. *)
(*   - econstructor; eauto. *)
(* Qed. *)

Lemma okt_implies_okgadt : forall Σ Δ E, okt Σ Δ E -> okGadt Σ.
  induction 1; auto.
Qed.

Ltac find_ctxeq :=
  match goal with
  | H: _ & _ ~ _ = _ & _ ~ _ |- _ =>
    rename H into Hctx_eq
  end.

Lemma okt_push_var_inv : forall Σ Δ E x vk T,
  okt Σ Δ (E & x ~ bind_var vk T) -> okt Σ Δ E /\ wft Σ Δ T /\ x # E.
Proof.
  introv O; inverts O.
  - false* empty_push_inv.
  - find_ctxeq. lets (?&M&?): (eq_push_inv Hctx_eq). subst. inverts~ M.
Qed.

Lemma okt_is_wft : forall Σ Δ E x vk T,
    okt Σ Δ (E & x ~ bind_var vk T) -> wft Σ Δ T.
  introv Hokt.
  inversion Hokt.
  - false* empty_push_inv.
  (* - lets (?&?&?): eq_push_inv H. false*. *)
  - lets (?&?&?): eq_push_inv H. subst.
    match goal with Heq: bind_var ?k1 ?T1 = bind_var ?k2 ?T2 |- _ => inversions* Heq end.
Qed.

Lemma okt_strengthen : forall Σ Δ E x vk U F,
    okt Σ Δ (E & (x ~ bind_var vk U) & F) -> okt Σ Δ (E & F).
  introv O. induction F using env_ind.
  - rewrite concat_empty_r in *. lets*: (okt_push_var_inv O).
  - rewrite concat_assoc in *.
    (* lets Hinv: okt_push_inv O; inversions Hinv. *)
    (* + lets (?&?): (okt_push_typ_inv O). *)
    (*   applys~ okt_sub. *)
    (* + match goal with *)
    (*   | H: exists T, v = bind_var T |- _ => *)
    (*     rename H into Hexists_bindvar end. *)
      (* inversions Hexists_bindvar. *)
    (* lets (?&?&?): (okt_push_var_inv O). *)
    destruct v.
    inversions O.
    + false* empty_push_inv.
    + apply eq_push_inv in H.
      destruct H as [? [? ?]]. subst.
      match goal with
      | [ H: bind_var ?vk1 ?T = bind_var ?vk2 ?t |- _ ] => inversions H
      end.
      applys~ okt_typ.
Qed.

Lemma okt_strengthen_delta_var : forall Σ D1 D2 E X,
    X # E ->
    X \notin fv_env E ->
    okt Σ (D1 |,| [tc_var X]* |,| D2) E -> okt Σ (D1 |,| D2) E.
  introv FXE FXTE O. induction E using env_ind.
  - constructor.
    lets*: okt_implies_okgadt.
  - destruct v as [T].
    inversions O.
    + lets*: empty_push_inv H.
    + lets [? [? ?]]: eq_push_inv H.
      match goal with
      | H: bind_var ?vk1 ?A = bind_var ?vk2 ?B |- _ => inversions H
      end.
      lets [? ?]: notin_env_inv FXTE.
      constructor; auto.
      * apply wft_strengthen_typ with X; auto.
      * apply notin_domΔ_eq.
        apply notin_domΔ_eq in H5.
        destruct H5.
        apply notin_domΔ_eq in H5.
        intuition.
Qed.

Lemma okt_is_type : forall Σ Δ E x vk T,
    okt Σ Δ (E & x ~ bind_var vk T) -> type T.
  introv Hokt. apply okt_is_wft in Hokt. apply* type_from_wft.
Qed.

Lemma wft_type : forall Σ Δ T,
    wft Σ Δ T -> type T.
Proof.
  induction 1; eauto.
Qed.

Lemma wft_weaken : forall Σ D1 D2 D3 T,
    wft Σ (D1 |,| D3) T ->
    wft Σ (D1 |,| D2 |,| D3) T.
  introv WT. gen_eq K: (D1 |,| D3). gen D3.
  induction WT; auto; introv EQ.
  - constructor. unfold is_var_defined in *.
    subst.
    lets [? | ?]: List.in_app_or H;
      auto using List.in_or_app.
  - apply_fresh* wft_all as Y.
    assert (Yfr: Y \notin L); eauto.
    lets: H0 Yfr (D3 |, tc_var Y).
    assert (Hassoc: ((D1 |,| D2) |,| (D3 |, tc_var Y)) = (((D1 |,| D2) |,| D3) |,| [tc_var Y]*));
      auto using List.app_assoc.
    rewrite <- Hassoc.
    apply H1. subst. auto using List.app_assoc.
  - apply* wft_gadt.
Qed.

Ltac destruct_app_list :=
  match goal with
  | [ H: List.In ?X (?L ++ ?K) |- _ ] =>
    apply List.in_app_or in H; destruct H
  end.

Lemma wft_subst_tb : forall Σ D1 D2 Z P T,
  wft Σ (D1 |,| [tc_var Z]* |,| D2) T ->
  wft Σ D1 P ->
  wft Σ (D1 |,| D2) (subst_tt Z P T).
Proof.
  introv WT WP; gen_eq G: (D1 |,| [tc_var Z]* |,| D2). gen D2.
  induction WT; intros; subst; simpl subst_tt; auto.
  - case_var*.
    + lets Hw: wft_weaken D1 D2 emptyΔ.
      repeat rewrite List.app_nil_r in *.
      apply* Hw.
    + constructor. unfold is_var_defined in *.
      repeat destruct_app_list; auto using List.in_or_app.
      cbn in H. destruct H.
      * congruence.
      * contradiction.
  - apply_fresh* wft_all as Y.
    lets: wft_type.
    rewrite* subst_tt_open_tt_var.
    lets* IH: H0 Y (D2 |, tc_var Y).
  - apply* wft_gadt.
    + introv Tin.
      apply List.in_map_iff in Tin.
      destruct Tin as [U [? Tin]]; subst.
      apply* H0.
    + apply List.map_length.
Qed.

Lemma wft_open : forall Σ Δ U T1,
  wft Σ Δ (typ_all T1) ->
  wft Σ Δ U ->
  wft Σ Δ (open_tt T1 U).
Proof.
  introv WA WU. inversions WA. pick_fresh X.
  rewrite* (@subst_tt_intro X).
  lets K: (@wft_subst_tb Σ Δ emptyΔ X).
  clean_empty_Δ.
  apply* K.
Qed.

(** ** GADT environment properties *)

#[export] Hint Resolve okt_is_ok.

Lemma gadt_constructor_ok : forall Σ Name Tarity Ctors Ctor Carity CargType CretTypes,
    binds Name (mkGADT Tarity Ctors) Σ ->
    List.nth_error Ctors Ctor = Some (mkGADTconstructor Carity CargType CretTypes) ->
    okGadt Σ ->
    okConstructorDef Σ Tarity (mkGADTconstructor Carity CargType CretTypes).
  introv Hbind Hlist HokG.
  inversion HokG as [Hok HokG'].
  apply* HokG'.
  apply* List.nth_error_In.
Qed.

Lemma wft_subst_tb_many : forall Σ (As : list var) (Us : list typ) Δ (T : typ),
    length As = length Us ->
      wft Σ (Δ |,| tc_vars As) T ->
      (forall U, List.In U Us -> wft Σ Δ U) ->
      (* (forall A, List.In A As -> A \notin dom E) -> *)
      DistinctList As ->
      wft Σ Δ (subst_tt_many As Us T).
  induction As as [|Ah Ats];
    introv Hlen HwftT WwftUs HD;
    destruct Us as [|Uh Uts]; inversion Hlen.
  - cbn in *.
    clean_empty_Δ.
    auto.
  - cbn in *. inversions HD.
    apply IHAts; eauto with listin.
    fold (tc_vars Ats) in HwftT.
    fold ((Δ |,| tc_vars Ats) |,| [tc_var Ah]*) in HwftT.
    lets W: wft_subst_tb Σ (Δ |,| tc_vars Ats) emptyΔ.
    clean_empty_Δ.
    apply~ W.
    rewrite <- (List.app_nil_l (Δ |,| tc_vars Ats)).
    apply~ wft_weaken.
Qed.

Lemma wft_open_many : forall Δ Σ Alphas Ts U,
    length Alphas = length Ts ->
    DistinctList Alphas ->
    (* (forall A : var, List.In A Alphas -> A \notin dom E) -> *)
    (forall A : var, List.In A Alphas -> A \notin fv_typ U) ->
    (forall (A : var) (T : typ), List.In A Alphas -> List.In T Ts -> A \notin fv_typ T) ->
    (forall T : typ, List.In T Ts -> wft Σ Δ T) ->
    wft Σ (Δ |,| tc_vars Alphas) (open_tt_many_var Alphas U) ->
    wft Σ Δ (open_tt_many Ts U).
  introv Hlen Hdistinct FU FT WT WU.
  rewrite* (@subst_tt_intro_many Alphas).
  - lets Htb: (@wft_subst_tb_many Σ Alphas Ts).
    specializes_vars Htb.
    apply* Htb.
Qed.

Hint Rewrite in_union : fsets.

Lemma notin_fv_wf : forall Σ Δ X T,
    wft Σ Δ T -> (~ is_var_defined Δ X) -> X \notin fv_typ T.
Proof.
  induction 1 as [ | ? ? ? Hbinds | | | |];
    introv Fr; simpl; eauto.
  - rewrite notin_singleton. intro. subst. contradiction.
  - notin_simpl; auto. pick_fresh Y. apply* (@notin_fv_tt_open Y).
    apply* H0.
    cbn.
    intro HF.
    destruct HF as [HF | HF].
    + inversions HF.
      assert (X \notin \{ X}); eauto using in_singleton_self.
    + contradiction.
  - intro Hin.
    lets* Hex: in_fold_exists Hin.
    destruct Hex as [Hex | Hex].
    + destruct Hex as [T [Tin fvT]].
      lets* Hf: H0 T Tin.
    + apply* in_empty_inv.
Qed.

Lemma typing_regular : forall Σ Δ E e T TT,
    {Σ, Δ, E} ⊢(TT) e ∈ T ->
    okt Σ Δ E /\ term e /\ wft Σ Δ T.
Proof.
  intro Hbounds.
  introv Typ.
  lets Typ2: Typ.
  induction Typ as [ |
                   |
                   | ? ? ? ? ? ? ? ? ? IH
                   |
                   | ? ? ? ? ? ? ? ? ? IH
                   | | | |
                   | ? ? ? ? ? ? ? IHval ? IH
                   | ? ? ? ? ? ? ? ? ? ? ? ? IH
                   |
                   |
                   ];
    try solve [splits*].
  - splits*. apply* wft_from_env_has_typ.
  - subst. destruct IHTyp as [Hokt [Hterm Hwft]]; auto.
    splits*.
    lets* HG: okt_implies_okgadt Hokt.
    lets* GADTC: gadt_constructor_ok HG.
    inversions GADTC.
    rewrite rewrite_open_tt_many_gadt.
    econstructor; eauto.
    + introv TiL.
      lets* TiL2: TiL. apply List.in_map_iff in TiL2.
      inversion TiL2 as [CretT [Heq CiC]]. subst.
      let usedvars := gather_vars in
      lets* EAlphas: exist_alphas (usedvars) (length Ts).
      inversion EAlphas as [Alphas [A1 [A2 A3]]].
      lets* HH: H9 Alphas CiC.
      apply (@wft_open_many Δ Σ Alphas Ts); auto.
      * introv Ain; lets~ FA: A3 Ain.
      * introv Ain Tin; lets~ FA: A3 Ain.
        eauto using fv_typs_notin.
      * eauto.
    + rewrite List.map_length. trivial.
  - pick_fresh y.
    copyTo IH IH1.
    assert (yL: y \notin L); eauto.
    lets~ [? [? ?]]: IH yL.
    splits*.
    + apply_folding E okt_strengthen.
    + econstructor.
      * apply* okt_is_type.
      * intros.  apply* IH1.
    + econstructor; eauto.
      apply* okt_is_wft.
  - splits*.
    destruct~ IHTyp2 as [? [? Hwft]]. inversion* Hwft.
  - copyTo IH IH1.
    pick_fresh_gen (L \u fv_env E \u dom E) y.
    add_notin y L. lets~ HF: IH Fr0. destructs~ HF.
    splits*.
    * rewrite <- (List.app_nil_l Δ).
      apply okt_strengthen_delta_var with y; eauto.
    * apply* term_tabs. intros. apply* IH1.
    * apply_fresh* wft_all as Y.
      add_notin Y L. lets~ HF: IH1 Y Fr1. destruct* HF.
  - subst. splits*. destruct~ IHTyp as [? [? Hwft]].
    copyTo Hwft Hwft2.
    inversions Hwft.
    match goal with
    | IH: forall X : var, X \notin L -> ?conclusion |- _ =>
      pick_fresh Y; add_notin Y L; lets HW: IH Y Fr0
    end.
    apply* wft_open.
  - splits*.
    destruct~ IHTyp as [? [? Hwft]]. inversion* Hwft.
  - splits*.
    destruct~ IHTyp as [? [? Hwft]]. inversion* Hwft.
  - pick_fresh y.
    copyTo IH IH1.
    specializes IH1 y. destructs~ IH1.
    splits*.
    + apply_folding E okt_strengthen.
    + econstructor. apply* okt_is_type.
      intros. apply* IH.
      intros. apply* IHval.
  - destructs~ IHTyp.
    pick_fresh y.
    assert (yFr: y \notin L); eauto.
    lets IH1: H yFr.
    destructs~ IH1.
    splits*.
    econstructor; auto.
    introv HxiL. lets HF: H x HxiL. destructs~ HF.
  - destruct~ IHTyp as [Hokt [Hterme HwftT]].
    splits*.
    + econstructor; eauto.
      2: {
        lets* OKG: okt_implies_okgadt Hokt.
        inversions OKG.
        lets*: H6 H0.
        destruct Defs as [|Def0].
        1: {
          destruct H. false*.
        }

        destruct ms as [|cl0].
        1: {
          false*.
        }

        lets [Alphas [? [?]]]: exist_alphas L (Carity Def0).
        pick_fresh x.
        lets~ : H4 Def0 cl0 Alphas x.
        - cbn. auto.
        - destruct H10; eauto.
          + apply* H3. cbn. auto.
          + destruct H11.
          apply* type_from_wft.
      }
      intros cl clin Alphas x Hlen Hdist Afresh xfresh xAlphas.
      destruct cl as [clA clT].
      cbn.
      apply F2_from_zip in H4; eauto.
      lets* [Def [DefIn [DefIn2 HDef]]]: forall2_from_snd clin.
      cbn in HDef.
      cbn in Hlen.
      lets Hlen2: H2 DefIn2.
      cbn in Hlen2.
      assert (Hlen3: length Alphas = Carity Def); try lia.
      lets~ HF: HDef Alphas x Hlen3 Hdist Afresh.
      lets~ [? [? ?]]: HF xfresh xAlphas.
      lets~ HT: H3 Def (clause clA clT) Alphas x.
    + assert (ms <> []*).
      * lets gadtOk: okt_implies_okgadt Hokt.
        inversion gadtOk as [? okDefs].
        lets [defNEmpty okDef]: okDefs H0.
        intro.
        destruct Defs; subst; eauto. cbn in H1. lia.
      * destruct ms as [ | cl1 rest]; [ contradiction | idtac ].
        apply F2_from_zip in H3; eauto.
        lets* [Def [DefIn [DefIn2 HDef]]]: forall2_from_snd cl1 H3;
          eauto with listin.

        (* May want a tactic 'pick_fresh Alphas' *)
        lets* [Alphas [A1 [A2 A3]]]: exist_alphas (Carity Def).
        instantiate (1:=L \u fv_typ Tc) in A3.
        pick_fresh x.

        assert (Afresh: (forall A : var, List.In A Alphas -> A \notin L));
          [ introv Ain; lets*: A3 Ain | idtac ].
        assert (xfresh: x \notin L); eauto.

        assert (xfreshA: x \notin from_list Alphas); eauto.

        lets* HTyp: HDef A1 A2 Afresh xfresh xfreshA.
        lets~ [? [? Hwft2]]: H4 HTyp.
        apply wft_strengthen_typ_many with Alphas; auto.
        -- rewrite <- (List.app_nil_l (Δ |,| tc_vars Alphas)).
           eapply wft_strengthen_equations.
           ++ clean_empty_Δ.
              apply Hwft2.
           ++ introv Hin.
              unfold equations_from_lists in Hin.
              rewrite zipWithIsMappedZip in Hin.
              apply List.in_map_iff in Hin.
              destruct Hin as [[U V] [Heq Hin]]. subst.
              eauto.
        -- introv Ain. lets*: A3 Ain.
Qed.

(** The reduction relation is restricted to well-formed objects. *)

(* does not seem to be helpful for proving safety, just a useful result on its own, but let's ignore it while there are more pressing theorems to prove *)
(* Lemma red_regular : forall t t', *)
(*   red t t' -> term t /\ term t'. *)
(* Proof. *)
(*   induction 1; split; autos* value_regular. *)
(*   - inversions H. pick_fresh y. rewrite* (@subst_ee_intro y). *)
(*   - inversions H. pick_fresh Y. rewrite* (@subst_te_intro Y). *)
(*   - inversions H. pick_fresh y. rewrite* (@subst_ee_intro y). *)
(*   - inversions H. auto. *)
(*   - inversions H. auto. *)
(*   - inversions IHred. econstructor. *)
(* Qed. *)


Lemma typing_implies_term : forall Σ Δ E e T TT,
    {Σ, Δ, E} ⊢(TT) e ∈ T ->
    term e.
  introv Typ.
  lets* TR: typing_regular Typ.
Qed.

Lemma Tgen_from_any : forall Σ Δ E TT e T,
    {Σ, Δ, E} ⊢(TT) e ∈ T ->
    {Σ, Δ, E} ⊢(Tgen) e ∈ T.
  introv Typ.
  applys~ typing_eq T TT.
  - apply teq_reflexivity.
  - lets* : typing_regular Typ.
Qed.

