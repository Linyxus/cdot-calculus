(** * List Example *)

(** Encoding the recursive list library from Amin et al. (2016) *)

Require Import ExampleTactics.
Require Import String.

Section SymmetryExample.

(*
Type: SymType := { a: x.b.type } ∧ { b: x.a.type }

Term: ν(x: SymType) { a = x.b } ∧ { b = x.a }
*)

Variables a b : trm_label.
Hypothesis Hab: a <> b.

Notation SymType :=
  (typ_rcd { a ⦂ {{ this•b }} } ∧
  typ_rcd { b ⦂ {{ this•a }} }).

Definition t :=
  trm_val (ν (SymType)
             defs_nil Λ
             { a :=p this•b } Λ
             { b :=p this•a }).

Theorem sym_typing :
  empty ⊢ t : μ SymType.
Proof.
  fresh_constructor. repeat apply ty_defs_cons; crush.
  - constructor. apply ty_def_path with (T:={{(pvar z)•a}}).
    assert (Heq: p_sel (avar_f z) (b :: nil) = (pvar z)•b).
      { trivial. }
    rewrite Heq. clear Heq.
    apply ty_new_elim.
    eapply ty_sub. crush.
    assert (Heq: typ_rcd {b ⦂ {{p_sel (avar_f z) (a :: nil)}}} = typ_rcd { b ⦂ {{(pvar z)•a}} }).
      { trivial. }
    rewrite Heq. clear Heq.
    crush.
  - apply ty_def_path with (T:={{(pvar z)•b}}).
    assert (Heq: p_sel (avar_f z) (a :: nil) = (pvar z)•a).
      { trivial. }
    rewrite Heq. clear Heq.
    apply ty_new_elim.
    eapply ty_sub. crush.
    assert (Heq: typ_rcd {a ⦂ {{p_sel (avar_f z) (b :: nil)}}} = typ_rcd { a ⦂ {{(pvar z)•b}} }).
      { trivial. }
    rewrite Heq. clear Heq.
    crush.
Qed.

End SymmetryExample.
