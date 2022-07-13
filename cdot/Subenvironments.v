(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** * Subenvironments [G1 ⪯ G2] *)

Set Implicit Arguments.

Require Import Definitions.
Require Import Coq.Program.Equality.

(** [G1] is a subenvironment of [G2], denoted [G1 ⪯ G2],
    if [dom(G1) = dom(G2)] and for each [x],
    [G1 ⊢ G1(x) <: G2(x)]. *)
Reserved Notation "G1 ⪯ G2" (at level 35).

Inductive subenv: ctx -> ctx -> Prop :=
| subenv_empty : empty ⪯ empty
| subenv_push: forall G G' x T T',
    G ⪯ G' ->
    ok (G & x ~ T) ->
    ok (G' & x ~ T') ->
    G ⊢ T <: T' ->
    G & x ~ T ⪯ G' & x ~ T'
where "G1 ⪯ G2" := (subenv G1 G2).

Hint Constructors subenv.

(** If [ok G], then [G ⪯ G].
    Note: [ok(G)] means that [G]'s domain consists of distinct variables. *)
Lemma subenv_refl : forall G, ok G -> G ⪯ G.
Proof.
  intros G H. induction H; auto.
Qed.
Hint Resolve subenv_refl.

(** If [G' ⪯ G] then [G', x: T ⪯ G, x: T] *)
Lemma subenv_extend : forall G1 G2 x T,
    G1 ⪯ G2 ->
    ok (G1 & x ~ T) -> ok (G2 & x ~ T) ->
    (G1 & x ~ T) ⪯ (G2 & x ~ T).
Proof.
  intros. induction H; intros; auto.
Qed.
Hint Resolve subenv_extend.


(** If [G ⊢ S <: U] and [x ∉ dom G] then [G', x: T subG G, x: T] *)
Lemma subenv_last: forall G x S U,
  G ⊢ S <: U ->
  ok (G & x ~ S) ->
  (G & x ~ S) ⪯ (G & x ~ U).
Proof.
  intros.
  inversion H0;
  match goal with
  | [ H : empty = _ |- _ ] => destruct (empty_push_inv H2)
  | [ H : _ & _ ~ _ = _ & _ ~ _ |- _ ] =>
    apply eq_push_inv in H; destruct_all; subst
  end;
  constructor; auto.
Qed.
Hint Resolve subenv_last.

(** If [G1 ⪯ G2] then the domains of both [G1] and [G2] consist of distinct elements. *)
Lemma subenv_implies_ok : forall G1 G2,
    G1 ⪯ G2 -> ok G1 /\ ok G2.
Proof.
  intros. inversion H; split; auto.
Qed.
