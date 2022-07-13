Require Import GMuAnnot.Definitions.
Require Import TLC.LibLN.

Declare Scope L2GMu.
Bind Scope L2GMu with typ.
Bind Scope L2GMu with trm.


(*
TODO: test ->
otherwise reduction -->
*)
Notation "## n" := (typ_bvar n) (at level 29) : L2GMu.
Coercion typ_fvar : var >-> typ.
Notation "T1 ** T2" := (typ_tuple T1 T2) (at level 49) : L2GMu.
Notation "T1 ==> T2" := (typ_arrow T1 T2) (at level 49, right associativity) : L2GMu .
Notation "∀ T" := (typ_all T) (at level 42) : L2GMu.
Notation "'γ()' N" := (typ_gadt nil N) (at level 42) : L2GMu.
Notation "'γ(' x , .. , z ) N" :=  (typ_gadt (cons z .. (cons x nil) ..) N) (at level 42) : L2GMu.

Notation "# n" := (trm_bvar n) (at level 29) : L2GMu.
(* Coercion trm_fvar : var >-> trm. *)
Notation "<.>" := trm_unit : L2GMu.
Notation "< a , b >" := (trm_tuple a b) (at level 42, a at level 30, b at level 30) : L2GMu.
Notation "fst( a )" := (trm_fst a) : L2GMu.
Notation "snd( a )" := (trm_snd a) : L2GMu.

Notation "'new' N [| |] ( e )" := (trm_constructor nil N e) : L2GMu.
Notation "'new' N [| T1 , .. , TN |] ( e )" := (trm_constructor (cons TN .. (cons T1 nil) .. ) N e) : L2GMu.


Notation "'λ' T => e" := (trm_abs T e) (at level 42) : L2GMu.
Infix "<|" := trm_app (at level 42) : L2GMu.

Notation "'Λ' => e" := (trm_tabs e) (at level 42) : L2GMu.
Infix "<||" := trm_tapp (at level 42) : L2GMu.

Notation "'fixs' T => v" := (trm_fix T v) (at level 42) : L2GMu.
(* ;; or no ending *)
Notation "'lets' e1 'in' e2 'tel'" := (trm_let e1 e2) : L2GMu.

(* https://coq.inria.fr/refman/user-extensions/syntax-extensions.html#custom-entries *)
Declare Custom Entry case_pattern.
Notation "'case' e 'as' N 'of' { p1 | .. | pN }" := (trm_matchgadt e N (cons p1 (.. (cons pN nil) ..))) (p1 custom case_pattern, pN custom case_pattern) : L2GMu.

Notation "n '=>' e" := (clause n e) (in custom case_pattern at level 10, n constr, e constr) : L2GMu.

Notation "'enum' n {{ c1 | .. | cN }}" := (mkGADT n (cons c1 (.. (cons cN nil) ..))) : L2GMu.
