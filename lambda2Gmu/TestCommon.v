Require Export Prelude.
Require Import Psatz.
Require Import TLC.LibLN.
Require Import TLC.LibEnv.
Require Import Infrastructure.
Require Export Notations.
Require Export Regularity.
Require Export Regularity2.

Ltac fs := exact \{}.

Ltac ininv :=
  match goal with
  | H: List.In _ _ |- _ =>
    inversions H
  end.

Ltac destruct_const_len_list :=
  repeat (match goal with
          | H: length ?L = ?n |- _ =>
            destruct L; inversions H
          end).

Ltac binds_inv :=
  match goal with
  | H: binds ?x ?a empty |- _ =>
    apply binds_empty_inv in H; contradiction
  | H: binds ?x ?a ?E |- _ =>
    binds_cases H;
    try match goal with
        | H: binds ?x ?a empty |- _ =>
          apply binds_empty_inv in H; contradiction
        end;
    subst
  | |- ?x \notin \{ ?y } =>
    apply* notin_inverse
  end.

Ltac solve_dom all_distinct :=
  simpl_dom; notin_solve; try (apply notin_singleton; lets*: all_distinct).

Ltac distinct2 :=
  match goal with
  | H1: DistinctList ?L |- _ =>
    inversions H1;
    match goal with
    | H2: ~ List.In ?v ?L1 |- _ =>
      cbn in H2; eauto
    end
  end.

Ltac solve_bind_core :=
  lazymatch goal with
  | |- binds ?Var ?What (?Left & ?Right) =>
    match goal with
    | |- binds Var What (Left & Var ~ ?Sth) =>
      apply* binds_concat_right; apply* binds_single_eq
    | _ => apply* binds_concat_left
    end
  end.

Ltac solve_bind :=
  (repeat solve_bind_core); try (solve_dom).

Export Definitions.
Export Psatz.
Export TLC.LibLN.
Export TLC.LibEnv.
Export Infrastructure. (* TODO only the gathering parts, should be split out *)

Inductive evals : trm -> trm -> Prop :=
| eval_step : forall a b c, a --> b -> evals b c -> evals a c
| eval_finish : forall a, evals a a.

Lemma is_var_defined_split : forall A B c, (is_var_defined A c \/ is_var_defined B c) -> is_var_defined (A |,| B) c.
  unfold is_var_defined.
  intros.
  apply List.in_or_app.
  destruct H; auto.
Qed.

Ltac autotyper1 :=
  repeat progress (
           cbn;
           match goal with
           | [ H: False |- _ ] => false*
           | [ |- ok ?A ] => econstructor
           | [ |- okt ?A ?B ?C ] => econstructor
           | [ |- binds ?A ?B ?C ] => solve_bind
           | [ |- ?A \notin ?B ] => simpl_dom; notin_solve; try (apply notin_singleton)
           | [ |- typing ?TT ?A ?B ?C ?D ?E ] => econstructor
           | [ |- forall x, x \notin ?L -> ?P ] =>
             let free := gather_vars in
             let x' := fresh "x" in
             let xiL := fresh "xiL" in
             intros x' xiL; intros;
             try instantiate (1 := free) in xiL
           | [ |- okGadt empty ] => econstructor
           | [ |- wft ?A ?B ?C ] => econstructor
           | [ |- value ?A ] => econstructor
           | [ |- term ?A ] => econstructor
           | [ |- type ?A ] => econstructor
           | [ H: binds ?A ?B ?C |- _ ] => binds_inv
           | [ |- ?A /\ ?B ] => split
           | [ H: {| Tarity := ?A; Tconstructors := ?B |} = ?C |- _ ] =>
             inversions H
           | [ H: ?A \/ ?B |- _ ] => destruct H
           | [ |- is_var_defined (?A |,| ?B) ?c ] => apply is_var_defined_split
           | _ => intros; auto
           end;
           cbn; subst).

(* TODO merge with autotyper1 *)
Ltac autotyper0 :=
  repeat progress (
           cbn;
           match goal with
           | [ H: False |- _ ] => false*
           | [ |- ok ?A ] => econstructor
           | [ |- okt ?A ?B ?C ] => econstructor
           | [ |- binds ?A ?B ?C ] => solve_bind
           | [ |- ?A \notin ?B ] => simpl_dom; notin_solve; try (apply notin_singleton)
           | [ |- forall x, x \notin ?L -> ?P ] =>
             let free := gather_vars in
             let x' := fresh "x" in
             let xiL := fresh "xiL" in
             intros x' xiL; intros;
             try instantiate (1 := free) in xiL
           | [ |- okGadt empty ] => econstructor
           | [ |- wft ?A ?B ?C ] => econstructor
           | [ |- value ?A ] => econstructor
           | [ |- term ?A ] => econstructor
           | [ |- type ?A ] => econstructor
           | [ H: binds ?A ?B ?C |- _ ] => binds_inv
           | [ |- ?A /\ ?B ] => split
           | [ H: {| Tarity := ?A; Tconstructors := ?B |} = ?C |- _ ] =>
             inversions H
           | [ H: ?A \/ ?B |- _ ] => destruct H
           | [ |- is_var_defined (?A |,| ?B) ?c ] => apply is_var_defined_split
           | _ => intros; auto
           end;
           cbn; subst).

Lemma neq_from_notin : forall (A : Type) (x y : A), x \notin \{ y } -> x <> y.
  intros.
  intro HF.
  subst.
  apply* notin_same.
Qed.

Ltac autotyper2 :=
  repeat progress (
           cbn;
           let free := gather_vars in
           let x' := fresh "x" in
           let xiL := fresh "xiL" in
           match goal with
           | [ H: False |- _ ] => false*
           | [ |- ok ?A ] => econstructor
           | [ |- okt ?A ?B ?C ] => econstructor
           | [ |- binds ?A ?B ?C ] => solve_bind
           | [ |- typing ?TT ?A ?B ?C (trm_unit) ?E ] => eapply typing_unit
           | [ |- typing ?TT ?A ?B ?C (trm_fvar ?k ?X) ?E ] => eapply typing_var with (vk:=k)
           | [ |- typing ?TT ?A ?B ?C (trm_constructor ?Ts ?N ?e) ?E ] => eapply typing_cons
           | [ |- typing ?TT ?A ?B ?C (trm_abs ?T ?e) ?E ] => eapply typing_abs with (L:=free)
           | [ |- typing ?TT ?A ?B ?C (trm_tabs ?e) ?E ] => eapply typing_tabs with (L:=free)
           | [ |- typing ?TT ?A ?B ?C (trm_app ?e1 ?e2) ?E ] => eapply typing_app
           | [ |- typing ?TT ?A ?B ?C (trm_tapp ?e1 ?T) ?E ] => eapply typing_tapp
           | [ |- typing ?TT ?A ?B ?C (trm_tuple ?e1 ?e2) ?E ] => eapply typing_tuple
           | [ |- typing ?TT ?A ?B ?C (trm_fst ?e1) ?E ] => eapply typing_fst
           | [ |- typing ?TT ?A ?B ?C (trm_snd ?e1) ?E ] => eapply typing_snd
           | [ |- typing ?TT ?A ?B ?C (trm_fix ?T ?e) ?E ] => eapply typing_fix with (L:=free)
           | [ |- typing ?TT ?A ?B ?C (trm_let ?e1 ?e2) ?E ] => eapply typing_let with (L:=free)
           | [ |- typing ?TT ?A ?B ?C (trm_matchgadt ?e1 ?N ?ms) ?E ] => eapply typing_case with (L:=free)
           | [ |- ?A \notin ?B ] => simpl_dom; notin_solve; try (apply notin_singleton)
           | [ |- forall x, x \notin ?L -> ?P ] =>
             let free := gather_vars in
             let x' := fresh "x" in
             let xiL := fresh "xiL" in
             intros x' xiL; intros;
             try instantiate (1 := free) in xiL
           | [ |- okGadt empty ] => econstructor
           | [ |- wft ?A ?B ?C ] => econstructor
           | [ |- value ?A ] => econstructor
           | [ |- term ?A ] => econstructor
           | [ |- type ?A ] => econstructor
           | [ H: binds ?A ?B ?C |- _ ] => binds_inv
           | [ |- ?A /\ ?B ] => split
           | [ H: {| Tarity := ?A; Tconstructors := ?B |} = ?C |- _ ] =>
             inversions H
           | [ H: ?A \/ ?B |- _ ] => destruct H
           | [ H: ?C = (?A, ?B) |- _ ] => inversions H
           | [ H: (?A, ?B) = ?C |- _ ] => inversions H
           | [ |- is_var_defined (?A |,| ?B) ?c ] => apply is_var_defined_split
           | _ => intros; auto
           end;
           cbn; subst).

Ltac autotyper3 :=
  autotyper2; cbn in *;
  destruct_const_len_list; cbn; autotyper2.

Ltac autotyper4 :=
  autotyper3;
  try solve [left~ | repeat right~].

Lemma Forall2_eq : forall A B (f : A -> B) Ts Us,
    List.length Ts = List.length Us ->
    (forall T U, List.In (T, U) (zip Ts Us) -> f T = f U) ->
    List.map f Ts =
    List.map f Us.
  induction Ts as [ | T Ts]; destruct Us as [ | U Us]; intros Len F; cbn in *; inversion Len.
  - auto.
  - f_equal; auto.
Qed.

Lemma eq_typ_gadt : forall Σ Δ Ts Us N,
    List.Forall2 (fun T U => entails_semantic Σ Δ (T ≡ U)) Ts Us ->
    entails_semantic Σ Δ (typ_gadt Ts N ≡ typ_gadt Us N).
  introv FF.
  cbn in *.
  apply F2_iff_In_zip in FF.
  destruct FF.
  intros O M.
  repeat rewrite subst_tt_prime_reduce_typ_gadt.
  f_equal.
  apply~ Forall2_eq.
Qed.

Ltac ininv2 :=
  match goal with
  | H: List.In _ _ |- _ =>
    inversions H
  | [ H: ?C = (?A, ?B) |- _ ] => inversions H
  | [ H: (?A, ?B) = ?C |- _ ] => inversions H
  end.

Lemma eq_typ_tuple : forall Σ Δ A B C D,
    entails_semantic Σ Δ (A ≡ C) ->
    entails_semantic Σ Δ (B ≡ D) ->
    entails_semantic Σ Δ ((A ** B) ≡ (C ** D)).
  introv EQ1 EQ2.
  cbn in *.
  intros O M.
  repeat rewrite subst_tt_prime_reduce_tuple.
  f_equal; auto.
Qed.
