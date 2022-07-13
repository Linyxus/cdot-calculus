Require Import Definitions.
Require Import TLC.LibTactics.
Require Import List.

Lemma open_tt_test : open_tt (typ_all (typ_bvar 1)) (typ_unit) = typ_all typ_unit.
  cbv. auto.
Qed.

Lemma open_te_test : open_te (trm_abs (typ_bvar 0) (trm_bvar 0)) (typ_unit) = trm_abs typ_unit (trm_bvar 0).
  cbv. auto.
Qed.

Lemma open_ee_test : open_ee (trm_abs (typ_bvar 0) (trm_bvar 1)) (trm_unit) = trm_abs (typ_bvar 0) (trm_unit).
  cbv. auto.
Qed.

Lemma open_typlist_test : open_typlist_rec 0 (typ_unit) [typ_bvar 0; typ_tuple (typ_bvar 0) (typ_bvar 1)]* = [typ_unit; typ_tuple (typ_unit) (typ_bvar 0)]*.
  cbv; repeat case_if. auto.
Qed.

Require Import TLC.LibEnv.
Section ManyTest.
Hypothesis T : var.
(* Lemma open_tt_many_test : open_tt_many [typ_unit; typ_fvar T] (typ_tuple (typ_bvar 0) (typ_bvar 1)) = typ_tuple typ_unit (typ_fvar T). *)
(*   cbv. auto. *)
(* Qed. *)
Lemma open_tt_many_test : open_tt_many [typ_fvar T; typ_unit]* (typ_tuple (typ_bvar 0) (typ_bvar 1)) = typ_tuple typ_unit (typ_fvar T).
  cbv. auto.
Qed.

Lemma open_te_many_test : open_te_many [typ_fvar T; typ_unit]* (trm_abs (typ_tuple (typ_bvar 0) (typ_bvar 1)) (trm_bvar 0)) = (trm_abs (typ_tuple typ_unit (typ_fvar T)) (trm_bvar 0)).
  cbv. auto.
Qed.

End ManyTest.
