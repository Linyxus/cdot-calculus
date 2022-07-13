Set Implicit Arguments.
Require Import GMuAnnot.Prelude.
Require Import GMuAnnot.InfrastructureFV.
Require Import GMuAnnot.InfrastructureOpen.
Require Import GMuAnnot.InfrastructureSubst.
Require Import TLC.LibLogic.
Require Import TLC.LibLN.

Lemma subst_ttΘ_fresh : forall Θ T,
  substitution_sources Θ \n fv_typ T = \{} ->
  subst_tt' T Θ = T.
  induction Θ as [| [A U] Θ].
  - cbn. auto.
  - introv Fr.
    cbn in Fr.
    fold (from_list (List.map fst Θ)) in Fr.
    fold (substitution_sources Θ) in Fr.
    rewrite union_distributes in Fr.
    lets [FrA FrT]: union_empty Fr.
    cbn.
    rewrite subst_tt_fresh.
    + apply~ IHΘ.
    + eapply empty_inter_implies_notin.
      * apply FrA.
      * apply in_singleton_self.
Qed.

Lemma subst_tt_inside : forall Θ A P T,
    A \notin substitution_sources Θ ->
    (forall X U, List.In (X, U) Θ -> A \notin fv_typ U) ->
    subst_tt' (subst_tt A P T) Θ
    =
    subst_tt A (subst_tt' P Θ) (subst_tt' T Θ).
  induction Θ as [| [X U] Θ]; introv ThetaFr UFr; cbn; trivial.
  rewrite <- IHΘ.
  - f_equal.
    rewrite~ subst_commute.
    + cbn in ThetaFr.
      rewrite notin_union in ThetaFr.
      destruct~ ThetaFr.
    + eauto with listin.
  - cbn in ThetaFr.
    fold (from_list (List.map fst Θ)) in ThetaFr.
    fold (substitution_sources Θ) in ThetaFr.
    auto.
  - eauto with listin.
Qed.

Lemma subst_tt_prime_reduce_typ_all : forall O T,
    subst_tt' (typ_all T) O = typ_all (subst_tt' T O).
  induction O as [| [A U]]; cbn; auto.
Qed.

Lemma subst_tt_prime_reduce_tuple : forall O T1 T2,
    subst_tt' (T1 ** T2) O = subst_tt' T1 O ** subst_tt' T2 O.
  induction O as [| [A U]]; cbn; auto.
Qed.

Lemma subst_tt_prime_reduce_arrow : forall O T1 T2,
    subst_tt' (T1 ==> T2) O = subst_tt' T1 O ==> subst_tt' T2 O.
  induction O as [| [A U]]; cbn; auto.
Qed.

Lemma subst_tt_prime_reduce_typ_gadt : forall O Ts N,
    subst_tt' (typ_gadt Ts N) O = typ_gadt (List.map (fun T => subst_tt' T O) Ts) N.
  induction O as [| [A U]]; introv; cbn; auto.
  - rewrite~ List.map_id.
  - rewrite IHO.
    f_equal.
    rewrite List.map_map. auto.
Qed.

Lemma subst_tt_prime_reduce_typ_unit : forall O,
    subst_tt' (typ_unit) O = typ_unit.
  induction O as [| [A U]]; cbn; auto.
Qed.

Lemma subst_ttprim_open_tt : forall O T U,
  (forall A P, List.In (A, P) O -> type P) ->
  subst_tt' (open_tt T U) O
  =
  open_tt (subst_tt' T O) (subst_tt' U O).
  induction O as [| [X P]]; introv TP; cbn; auto.
  rewrite subst_tt_open_tt; eauto with listin.
Qed.
