Require Import TestCommon.
Require Import Equations.

(*

This file implements a list type with type-level-encoded length, called Vector.

We introduce two phantom types: Zero : * and Succ : * -> *, to encode natural numbers on typelevel.

It has the following constructors:
data Vector A N
  empty : () -> Vector a Zero
  cons : (a * Vector a n) -> Vector a (Succ n)

or in dotty:
trait Zero
trait Succ[N]

enum Vector[A,N] {
  case Empty[A](unused: Unit) extends Vector[A, Zero]
  case Cons[A, N](data: (A, Vector[A, N])) extends Vector[A, Succ[N]]
}

Then we wrap the constructors as functions (just as an exercise):
  empty': forall a, Vector a Zero
  cons' : forall a n, a -> Vector a n -> Vector a (Succ n)
or in dotty:
  def empty[A]: Vector[A, Zero]
  def cons[A,N](head: A)(tail: Vector[A, N]): Vector[A, Succ[N]]

we can create a vector containing two units:
  uvec = (cons () (cons () empty)) // I skip the type args here, they are elaborated in the proof
  uvec : Vector Unit (Succ (Succ Zero))

we can create a map function that guarantees that it preserves length:
  map : forall a b n, (a -> b) -> Vector a n -> Vector b n

then we implement the 'safe' head function that works only on non-empty vectors:
  head : forall a n, Vector a (Succ n) -> a
  def head[A,N](v: Vector[A, Succ[N]]): A
this will be an occassion to show how we handle contradictory branches:
- we may use the contradictory type equalities to prove that unit: A for every a and just return it

another showcase of GADT abilities will be a typesafe zip function that only allows to zip vectors of equal length
  zip : forall a b n, Vector a n -> Vector b n -> Vector (a * b) n
  def zip[A,B,N](va: Vector[A,N])(vb: Vector[B,N]): Vector[(A,B), N]

  append (nat - plus)
*)

(* type level natural numbers *)
Axiom Zero : var.
Axiom Succ : var.
Axiom Vector : var.

Open Scope L2GMu.
Axiom all_distinct :
  (Zero <> Succ) /\ (Succ <> Vector) /\ (Zero <> Vector).

(* De Bruijn indices for arguments are in 'reverse' order, that is the last arg on the list is treated as 'closest' and referred to as ##0 *)
Definition VectorDef := (* Vector a len *)
  enum 2 {{
         (* empty : forall a, () -> Vector a Zero *)
         mkGADTconstructor 1 typ_unit [##0; γ() Zero]* |
         (* cons : forall a n, (a * Vector a n) -> Vector a (Succ n) *)
         mkGADTconstructor 2 (##1 ** γ(##1, ##0) Vector) [##1; γ(##0) Succ]*
         }}
.

Definition sigma :=
  empty
    (* Zero and Succ are phantom types, but we add them constructors as at least one constructor is required for consistency *)
  & Zero ~ enum 0 {{
           mkGADTconstructor 0 typ_unit []*
         }}
  & Succ ~ enum 1 {{
           mkGADTconstructor 1 typ_unit [##0]*
         }}
  & Vector ~ VectorDef.

Lemma oksigma : okGadt sigma.
Proof.
  unfold sigma.
  unfold VectorDef.
  lets [? [? ?]]: all_distinct.
  lets: is_var_defined_split.
  econstructor; autotyper1;
    try congruence;
    try econstructor; autotyper1;
      destruct_const_len_list;
      autotyper1;
      repeat rewrite union_empty_r; auto.
Qed.

Definition Nil := (Vector, 0).
Definition Cons := (Vector, 1).

Definition nil A := new Nil [| A |] (trm_unit).
Definition cons A N h t := new Cons [|A, N|]  (trm_tuple h t).

Lemma nil_type : {sigma, emptyΔ, empty} ⊢(Treg) (Λ => nil (##0)) ∈ typ_all (γ(##0, γ() Zero) Vector).
Proof.
  cbv.
  lets: oksigma.
  autotyper1.
Qed.

Ltac distinct22 :=
  lazymatch goal with
  | |- ?a <> ?b =>
    match goal with
    | H: a \in ?S -> False |- _ =>
      intro; apply H; subst; apply in_singleton_self
    | H: b \in ?S -> False |- _ =>
      intro; apply H; subst; apply in_singleton_self
    end
  end.

Ltac free_abs :=
  unshelve econstructor; cbv; try (let v := gather_vars in exact v).

Lemma notin_eqv : forall A (x : A) L,
    (x \in L -> False) <-> x \notin L.
Proof.
  introv.
  intuition.
Qed.

Lemma cons_type :
  {sigma, emptyΔ, empty} ⊢(Treg)
                         (Λ => Λ =>
                          (λ ##1 => λ γ(##1, ##0) Vector =>
                           cons (##1) (##0) (#1) (#0)
                         ))
                         ∈
                         ∀ ∀ (##1 ==> (γ(##1, ##0) Vector) ==> (γ(##1, γ(##0) Succ) Vector)).
Proof.
  cbv.
  lets: oksigma.
  autotyper1.
Qed.

Definition GZ := γ() Zero.
Definition GS (T : typ) := γ(T) Succ.

Definition uvec2 := cons typ_unit (GS GZ) trm_unit (cons typ_unit GZ trm_unit (nil typ_unit)).

Definition two := GS (GS GZ).
Lemma uvec2_type : {sigma, emptyΔ, empty} ⊢(Treg) uvec2 ∈ γ(typ_unit, two) Vector.
Proof.
  cbv.
  lets: oksigma.
  lets [? [? ?]]: all_distinct.
  autotyper1.
Qed.

(*
head : ∀a. ∀n. ((a, (n) Succ) Vector) -> a
head = Λa. Λn. λv: ((a, (n) Succ) Vector).
        case v of {
          Nil[a2](unused) => <>
        | Cons[a2, n2](da) => fst(da)
        }
The term below has been generated from the pseudocode above using the converter tool.
*)
Definition head_trm :=
  trm_tabs (trm_tabs (trm_abs (typ_gadt [##1; typ_gadt [##0]* Succ]* Vector) (trm_matchgadt (#0) Vector [clause 2 (trm_fst (#0)); clause 1 (trm_unit)]*)))
.
Definition head_typ :=
  ∀ ∀ (γ(##1, γ(##0) Succ) Vector ==> ##1).

Lemma head_types : {sigma, emptyΔ, empty} ⊢(Treg) head_trm ∈ head_typ.
Proof.
cbv.
lets: oksigma.
  lets [? [? ?]]: all_distinct.
autotyper4;
  try solve[
    cbn in *;
    destruct_const_len_list;
    cbn; autotyper4
  ].
  - forwards*: H6 v. cbn in *.
    eapply typing_eq.
    + autotyper4.
    + unfold entails_semantic.
      intros O OM.
      exfalso.
      repeat (
        match goal with
        | H: subst_matches_typctx ?A ?B ?C |- _ =>
          inversions H
        end
      ).
      repeat (
        match goal with
        | H: wft ?A ?B ?C |- _ =>
          clear H
        end
      ).
      cbn in *.
      congruence.
    + autotyper4.
  - forwards*: H6 v.
    forwards*: H6 v0.
    cbn in *.
    eapply typing_eq.
    + autotyper4.
    + apply teq_symmetry.
      apply teq_axiom; listin.
    + autotyper4.
  Unshelve.
  fs. fs. fs.
Qed.

(*
zip : ∀a. ∀b. ∀n. ((a,n) Vector -> (b,n) Vector -> (a * b,n) Vector
zip = fix $self: (∀a. ∀b. ∀n. ((a,n) Vector -> (b,n) Vector -> (a * b,n) Vector)).
        Λa. Λb. Λn. λva: ((a,n) Vector). λvb: ((b,n) Vector). case va of {
            Nil[a2](unused) => Nil[a * b](<>)
          | Cons[a2, n2](da) =>
            case vb of {
              Nil[b2](unused) => <>
            | Cons[b2, n3](db) =>
                let h = <fst(da), fst(db)> in
                  let t = (((($self[a])[b])[n2]) (snd(da))) (snd(db)) in
                    Cons[(a*b),n2](<h, t>)
                  end
                end
            }
          }
The term below has been generated from the pseudocode above using the converter tool.
*)
Definition zip_trm :=
  trm_fix (typ_all (typ_all (typ_all ((typ_gadt [##2; ##0]* Vector) ==> ((typ_gadt [##1; ##0]* Vector) ==> (typ_gadt [(##2) ** (##1); ##0]* Vector)))))) (trm_tabs (trm_tabs (trm_tabs (trm_abs (typ_gadt [##2; ##0]* Vector) (trm_abs (typ_gadt [##1; ##0]* Vector) (trm_matchgadt (#1) Vector [clause 2 (trm_matchgadt (#1) Vector [clause 2 (trm_let (trm_tuple (trm_fst (#1)) (trm_fst (#0))) (trm_let (trm_app (trm_app (trm_tapp (trm_tapp (trm_tapp (#5) (##6)) (##5)) (##2)) (trm_snd (#2))) (trm_snd (#1))) (trm_constructor [(##6) ** (##5); ##2]* (Vector, 1) (trm_tuple (#1) (#0))))); clause 1 (trm_unit)]*); clause 1 (trm_constructor [(##3) ** (##2)]* (Vector, 0) (trm_unit))]*))))))
.

Definition zip_typ :=
  ∀ ∀ ∀ (γ(##2, ##0) Vector ==> γ(##1, ##0) Vector ==> γ(##2 ** ##1, ##0) Vector).

Lemma zip_types : {sigma, emptyΔ, empty} ⊢(Treg) zip_trm ∈ zip_typ.
Proof.
cbv.
lets: oksigma.
  lets [? [? ?]]: all_distinct.
autotyper4;
  try solve[
    cbn in *;
    destruct_const_len_list;
    cbn; autotyper4
  ].
  - forwards*: H6 v.
    eapply typing_eq with (γ( x1 ** x2, (γ() Zero)) Vector) _;
      try solve[autotyper4].
      apply eq_typ_gadt.
      apply F2_iff_In_zip.
      split~.
      intros.
      repeat ininv2.
      + apply teq_symmetry.
        apply teq_axiom. listin.
      + apply teq_reflexivity.
  - forwards*: H6 v.
    forwards*: H6 v0.
    cbn in *.
    apply Tgen_from_any with Treg.
    autotyper4.
    + cbn in *.
      forwards*: H12 v1.
      eapply typing_eq.
      * autotyper4.
      * unfold entails_semantic.
        intros O OM.
        exfalso.
        repeat (
          match goal with
          | H: subst_matches_typctx ?A ?B ?C |- _ =>
            inversions H
          end
        ).
        repeat (
          match goal with
          | H: wft ?A ?B ?C |- _ =>
            clear H
          end
        ).
        match goal with
        | H1: subst_tt' (typ_fvar x3) ?S1 = subst_tt' ?A ?S2,
          H2: subst_tt' (typ_fvar x3) ?S3 = subst_tt' ?B ?S4 |- _ =>
          assert (subst_tt' (typ_fvar x3) S1 = subst_tt' (typ_fvar x3) S3)
        end.
        -- cbn.
           fold (subst_tt v T0 x3).
           repeat f_equal.
           assert (x3 <> v1) by (apply neq_from_notin; notin_solve).
           case_if*.
        -- match goal with
          | H1: subst_tt' (typ_fvar x3) ?S1 = subst_tt' ?A ?S2,
            H2: subst_tt' (typ_fvar x3) ?S3 = subst_tt' ?B ?S4,
            H3: subst_tt' (typ_fvar x3) ?S5 = subst_tt' ?C ?S6 |- _ =>
            assert (HEQ: subst_tt' A S1 = subst_tt' B S3) by congruence
          end.
          cbn in HEQ.
          congruence.
      * autotyper4.
    + eapply typing_eq.
      * forwards*: H12 v1.
        forwards*: H12 v2.
        cbn in *.
        match goal with
        | |- {?E, ?D, ?G} ⊢( ?TT) ?t ∈ ?T =>
          assert (okt E D G) by autotyper4
        end.
        econstructor.
        -- econstructor.
           ++ econstructor. econstructor.
              ** solve_bind.
              ** auto.
           ++ econstructor. econstructor.
              ** solve_bind.
              ** auto.
        -- let FR := gather_vars in
            introv xFr;
            instantiate (1:=FR) in xFr.
           match goal with
           | |- {?E, ?D, ?G} ⊢( ?TT) ?t ∈ ?T =>
             assert (okt E D G)
           end.
           1: {
             autotyper4.
           }
           econstructor.
           ++ econstructor.
              2: {
                econstructor.
                2: {
                  econstructor.
                  - econstructor.
                    + econstructor.
                      * econstructor; solve_bind; auto.
                      * autotyper4.
                      * cbn. auto.
                    + autotyper4.
                    + cbn. auto.
                  - autotyper4.
                  - cbn. auto.
                }

                match goal with
                | |- context[x ~l (?A ** ?B)] =>
                  apply typing_eq with B Treg
                end.
                - econstructor.
                  econstructor; solve_bind; auto.
                - apply eq_typ_gadt.
                  apply F2_iff_In_zip.
                  split~.
                  intros.
                  repeat ininv2.
                  * apply teq_reflexivity.
                  * apply teq_symmetry.
                    apply teq_axiom. listin.
                - autotyper4.
              }

              match goal with
              | |- context[x6 ~l (?A ** ?B)] =>
                apply typing_eq with B Treg
              end.
              ** econstructor.
                 econstructor; solve_bind; auto.
              ** apply eq_typ_gadt.
                 apply F2_iff_In_zip.
                 split~.
                 intros.
                 repeat ininv2.
                 --- forwards* HI: inversion_eq_typ_gadt [typ_fvar v1]* [typ_fvar v]*.
                     2: {
                      rewrite F2_iff_In_zip in HI.
                      destruct HI as [? HI].
                      lets* HI2: HI v1 v.
                      apply HI2.
                      cbn; auto.
                     }
                     apply teq_transitivity with (typ_fvar x3).
                     +++ apply teq_symmetry.
                         apply teq_axiom; listin.
                     +++ apply teq_axiom; listin.
                 --- apply teq_symmetry. apply teq_axiom. listin.
              ** autotyper4.
            ++ cbn.
               let FR := gather_vars in
                 introv xFr2;instantiate (1:=FR) in xFr2.
               match goal with
               | |- {?E, ?D, ?G} ⊢( ?TT) ?t ∈ ?T =>
                 assert (okt E D G) by autotyper4
               end.
               econstructor.
               2: {
                 solve_bind.
               }
               2: {
                 cbn. auto.
               }
               2: {
                 cbn. auto.
               }
               2: {
                 cbn. auto.
               }
               1: {
                 eapply typing_eq.
                 - econstructor.
                   + econstructor; solve_bind; auto.
                   + econstructor; solve_bind; auto.
                 - apply eq_typ_tuple.
                   + apply eq_typ_tuple;
                      apply teq_symmetry;
                      apply teq_axiom; listin.
                   + apply teq_reflexivity.
                 - autotyper4.
               }
               2: {
                 cbn.
                 auto.
               }
               autotyper4.
      * apply eq_typ_gadt.
        apply F2_iff_In_zip.
        split~.
        intros.
        repeat ininv2.
        -- apply teq_symmetry.
           apply teq_axiom; listin.
        -- apply teq_reflexivity.
      * autotyper4.
Unshelve.
fs. fs. fs. fs. fs. fs. fs. fs. fs. fs. fs. fs. fs. fs. fs.
fs. fs. fs. fs. fs. fs. fs. fs. fs. fs. fs. fs. fs. fs. fs.
Qed.

(*
  map : forall a b n, (a -> b) -> Vector a n -> Vector b n
 *)
Definition map :=
  fixs ∀ ∀ ∀ ((##2 ==> ##1) ==> γ(##2, ##0) Vector ==> γ(##1, ##0) Vector) =>
  Λ (* a *) => Λ (* b *) => Λ (* n *) =>
  λ (* f *) (##2 ==> ##1) =>
  λ (* v *) γ(##2, ##0) Vector =>
  case #0 as Vector of {
                      (* a' *) 1 => new Nil [| ##2 |] ( <.> ) |
                      (* a', n'; elem *) 2 => new Cons [| ##3, ##0 |] (
                                      trm_tuple
                                        (#2 <| fst(#0))
                                        (#3 <|| ##4 <|| ##3 <|| ##0 <| #2 <| snd(#0))
                                    )
                    }.


Lemma map_types : {sigma, emptyΔ, empty} ⊢(Treg) map ∈ ∀ ∀ ∀ ((##2 ==> ##1) ==> γ(##2, ##0) Vector ==> γ(##1, ##0) Vector).
Proof.
  cbv.
  lets: oksigma.
  lets [? [? ?]]: all_distinct.
  autotyper3;
    rename x0 into map;
    rename x4 into f;
    rename x1 into A;
    rename x2 into B;
    rename x3 into N;
    rename x5 into vec.
  - rename v into C.
    forwards~ : H6 C.
    eapply typing_eq with (T1:=γ(typ_fvar B, γ() Zero) Vector).
    + autotyper4.
    + apply eq_typ_gadt.
      apply F2_iff_In_zip.
      split~.
      intros.
      repeat ininv2.
      * apply teq_symmetry.
        apply teq_axiom. listin.
      * apply teq_reflexivity.
    + autotyper4.
  - rename v0 into A'.
    rename v into N'.
    forwards~ : H6 A'.
    forwards~ : H6 N'.
    apply typing_eq with (γ(typ_fvar B, γ(typ_fvar N') Succ) Vector) Treg.
    + eapply typing_cons; autotyper0.
      * eapply typing_tuple; autotyper0.
        -- econstructor.
           ++ instantiate (1:=A).
              apply typing_eq with A' Treg.
              ** autotyper4.
              ** apply teq_symmetry. apply teq_axiom. listin.
              ** autotyper4.
           ++ autotyper4.
        -- econstructor; autotyper0.
           instantiate (1:= γ(typ_fvar A, typ_fvar N') Vector).
           ++ apply typing_eq with (γ(typ_fvar A', typ_fvar N') Vector) Treg.
              ** autotyper4.
              ** apply eq_typ_gadt.
                 apply F2_iff_In_zip.
                 split~.
                 intros.
                 repeat ininv2.
                 --- apply teq_reflexivity.
                 --- apply teq_symmetry.
                     apply teq_axiom. listin.
              ** autotyper4.
           ++ autotyper4.
      * autotyper4.
    + apply eq_typ_gadt.
      apply F2_iff_In_zip.
      split~.
      intros.
      repeat ininv2.
      * apply teq_symmetry.
        apply teq_axiom. listin.
      * apply teq_reflexivity.
    + autotyper4.
      Unshelve.
      fs.
      fs.
      fs.
      fs.
      fs.
      fs.
      fs.
      fs.
      fs.
      fs.
      fs.
      fs.
      fs.
      fs.
      fs.
Qed.
