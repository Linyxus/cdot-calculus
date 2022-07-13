Require Export GMu.Zip.
Require Import GMu.Definitions.
Require Export Definitions.
Require Export TLC.LibTactics.
Require Export TLC.LibFset.
Require Export TLC.LibEnv.
Require Import TLC.LibLN.
Require Export Psatz.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.EqNat.
Require Import List.

#[export] Hint Constructors type term wft typing red value.

#[export] Hint Resolve typing_var typing_app typing_tapp.

Lemma value_is_term : forall e, value e -> term e.
  induction e; intro Hv; inversion Hv; eauto.
Qed.


(** Gathering free names already used in the proofs *)
Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : trm => fv_trm x) in
  let E := gather_vars_with (fun x : typ => fv_typ x) in
  let F := gather_vars_with (fun x : ctx => dom x \u fv_env x) in
  let G := gather_vars_with (fun x : list var => from_list x) in
  let H := gather_vars_with (fun x : list typ => fv_typs x) in
  let I := gather_vars_with (fun x : typctx => domΔ x \u fv_delta x) in
  constr:(A \u B \u C \u E \u F \u G \u H \u I).

(** "pick_fresh x" tactic create a fresh variable with name x *)

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

(** "apply_fresh T as x" is used to apply inductive rule which
   use an universal quantification over a cofinite set *)

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto_star.

Ltac get_env :=
  match goal with
  | |- wft ?E _ => E
  | |- typing ?E _ _ => E
  end.

Ltac handleforall :=
  let Hforall := fresh "Hforall" in
  match goal with
  | H: List.Forall ?P ?ls |- _ => rename H into Hforall; rewrite List.Forall_forall in Hforall
  end.

Ltac rewritemapmap :=
  let H' := fresh "Hmapmap" in
  match goal with
  | H: List.map ?f ?ls = (List.map ?g (List.map ?h ?ls)) |- _ => rename H into H'; rewrite List.map_map in H'
  end.

Ltac decide_compare i j :=
  let CMP := fresh "CMP" in
  let EQ := fresh "EQ" in
  remember (i ?= j) as CMP eqn: EQ;
  symmetry in EQ;
  destruct CMP;
  match goal with
  | H: (i ?= j) = Eq |- _ => apply nat_compare_eq in H
  | H: (i ?= j) = Lt |- _ => apply nat_compare_lt in H
  | H: (i ?= j) = Gt |- _ => apply nat_compare_gt in H
  end.

Ltac crush_compare :=
  match goal with
  | H: context [(?i ?= ?j)] |- _ => decide_compare i j; (try lia); eauto
  | |- context [(?i ?= ?j)] => decide_compare i j; (try lia); eauto
  end.

Ltac decide_eq i j :=
  let CMP := fresh "CMP" in
  let EQ := fresh "EQ" in
  remember (i =? j) as CMP eqn: EQ;
  symmetry in EQ;
  destruct CMP;
  match goal with
  | H: (i =? j) = true |- _ => apply beq_nat_true in H
  | H: (i =? j) = false |- _ => apply beq_nat_false in H
  end.

Ltac crush_eq :=
  match goal with
  | H: context [(?i =? ?j)] |- _ => decide_eq i j; eauto
  | |- context [(?i =? ?j)] => decide_eq i j; eauto
  end.

(* maybe move strong induction to separate file? *)
Lemma strong_induction (P : nat -> Prop): (forall m, (forall k, k < m -> P k) -> P m) -> forall n, P n.
  apply Wf_nat.induction_ltof1.
Qed.

Lemma strong_induction_on_term_size_helper : forall (P : trm -> Prop),
    (forall n, (forall e, trm_size e < n -> P e) -> forall e, trm_size e = n -> P e) ->
    forall n e, trm_size e = n -> P e.
  introv IH.
  lets K: strong_induction (fun n => forall e, trm_size e = n -> P e).
  apply K.
  introv IHk.
  lets IHm: IH m.
  apply IHm.
  intros.
  eapply IHk; eauto.
Qed.

Lemma strong_induction_on_term_size : forall (P : trm -> Prop),
    (forall n, (forall e, trm_size e < n -> P e) -> forall e, trm_size e = n -> P e) ->
    forall e, P e.
  intros.
  pose (n := trm_size e).
  eapply strong_induction_on_term_size_helper; eauto.
Qed.

(* TODO DRY *)
Lemma strong_induction_on_type_size_helper : forall (P : typ -> Prop),
    (forall n, (forall e, typ_size e < n -> P e) -> forall e, typ_size e = n -> P e) ->
    forall n e, typ_size e = n -> P e.
  introv IH.
  lets K: strong_induction (fun n => forall e, typ_size e = n -> P e).
  apply K.
  introv IHk.
  lets IHm: IH m.
  apply IHm.
  intros.
  eapply IHk; eauto.
Qed.

Lemma strong_induction_on_typ_size : forall (P : typ -> Prop),
    (forall n, (forall T, typ_size T < n -> P T) -> forall T, typ_size T = n -> P T) ->
    forall T, P T.
  intros.
  pose (n := typ_size T).
  eapply strong_induction_on_type_size_helper; eauto.
Qed.

(* (** These tactics help applying a lemma which conclusion mentions *)
(*   an environment (E & F) in the particular case when F is empty *) *)
(* Tactic Notation "apply_empty_bis" tactic(get_env) constr(lemma) := *)
(*   let E := get_env in rewrite <- (concat_empty E); *)
(*   eapply lemma; try rewrite concat_empty. *)

(* Tactic Notation "apply_empty" constr(F) := *)
(*   apply_empty_bis (get_env) F. *)

(* Tactic Notation "apply_empty" "*" constr(F) := *)
(*   apply_empty F; auto*. *)

Ltac unsimpl_map_bind :=
  match goal with |- context [ ?B (subst_tt ?Z ?P ?U) ] =>
    unsimpl ((subst_tb Z P) (B U)) end.

Tactic Notation "unsimpl_map_bind" "*" :=
  unsimpl_map_bind; auto_star.

(* TODO make better names for map_id and ext_in_map *)
Lemma map_id : forall (A : Type) (f : A -> A) (ls : list A),
    (forall x, List.In x ls -> x = f x) ->
    ls = List.map f ls.
  introv feq.
  induction ls.
  - auto.
  - cbn.
    rewrite <- feq.
    + rewrite <- IHls.
      * auto.
      * intros.
        apply feq.
        apply* List.in_cons.
    + constructor*.
Qed.

(* adapted from a newer version of Coq stdlib:
https://github.com/coq/coq/blob/master/theories/Lists/List.v
*)
Lemma ext_in_map :
  forall (A B : Type)(f g:A->B) l, List.map f l = List.map g l -> forall a, List.In a l -> f a = g a.
Proof. induction l; intros [=] ? []; subst; auto. Qed.

Ltac crush_open :=
  (try unfold open_tt); (try unfold open_tt_rec); crush_compare.


#[export] Hint Immediate subset_refl subset_empty_l subset_union_weak_l subset_union_weak_r subset_union_2 union_comm union_assoc union_same.

Lemma union_distribute : forall T (A B C : fset T),
    (A \u B) \u C = (A \u C) \u (B \u C).
  intros.
  assert (CuC: C \u C = C); try apply union_same.
  rewrite <- CuC at 1.
  rewrite <- union_assoc.
  rewrite union_comm.
  rewrite union_assoc.
  rewrite <- union_assoc.
  rewrite union_comm.
  assert (CuA: C \u A = A \u C); try apply union_comm.
  rewrite* CuA.
Qed.

Lemma union_fold_detach : forall B (ls : list B) (P : B -> fset var) (z : fset var) (z' : fset var),
    List.fold_left (fun (a : fset var) (b : B) => a \u P b) ls (z \u z')
    =
    List.fold_left (fun (a : fset var) (b : B) => a \u P b) ls z \u z'.
  induction ls; introv.
  - cbn. eauto.
  - cbn.
    assert (Horder: ((z \u z') \u P a) = ((z \u P a) \u z')).
    + rewrite union_comm.
      rewrite union_assoc.
      rewrite (union_comm (P a) z).
      eauto.
    + rewrite Horder.
      apply* IHls.
Qed.

Ltac expand_env_empty E :=
  let HE := fresh "HE" in
  assert (HE: E = E & empty); [
    rewrite* concat_empty_r
  | rewrite HE ].

Ltac fold_env_empty :=
  match goal with
  | |- context [?E & empty] =>
    let HE := fresh "HE" in
    assert (HE: E = E & empty); [
      rewrite* concat_empty_r
    | rewrite* <- HE ]
  end.

Ltac fold_env_empty_H :=
  match goal with
  | H: context [?E & empty] |- _ =>
    let HE := fresh "HE" in
    assert (HE: E = E & empty); [
      rewrite* concat_empty_r
    | rewrite* <- HE in H]
  | H: context [empty & ?E] |- _ =>
    let HE := fresh "HE" in
    assert (HE: E = empty & E); [
      rewrite* concat_empty_l
    | rewrite* <- HE in H]
  end.

Ltac copy H :=
  let H' := fresh H in
  let Heq := fresh "EQ" in
  remember H as H' eqn:Heq; clear Heq.

Ltac copyTo H Hto :=
  let H' := fresh Hto in
  let Heq := fresh "EQ" in
  remember H as H' eqn:Heq; clear Heq.

Ltac apply_folding E lemma :=
  expand_env_empty E; apply* lemma; fold_env_empty.

Ltac add_notin x L :=
  let Fr := fresh "Fr" in
  assert (Fr: x \notin L); auto.

Require Import TLC.LibFset TLC.LibList.
(* different Fset impl? taken from repo: *)
Lemma from_list_spec : forall A (x : A) L,
  x \in from_list L -> LibList.mem x L.
Proof using.
  unfold from_list. induction L; rew_listx.
  - rewrite in_empty. auto.
  - rewrite in_union, in_singleton.
    intro HH.
    destruct HH; eauto.
Qed.

Lemma from_list_spec2 : forall A (x : A) L,
    List.In x L -> x \in from_list L.
Proof using.
  unfold from_list. induction L; rew_listx.
  - rewrite in_empty. auto.
  - rewrite in_union, in_singleton.
    intro HH.
    destruct HH; eauto.
Qed.

Lemma exist_alphas : forall L len,
    exists (Alphas : list var),
      List.length Alphas = len /\ DistinctList Alphas /\ forall A, List.In A Alphas -> A \notin L.
  induction len.
  - exists (@List.nil var). splits*.
    + econstructor.
    + intuition.
  - inversion IHlen as [Alphas' [Hlen [Hdis Hnot]]].
    pick_fresh A.
    exists (List.cons A Alphas').
    splits*.
    + cbn.
      eauto.
    + constructor*.
      intro.
      assert (Hnot2: A \notin from_list Alphas'); eauto.
      apply Hnot2.
      apply* from_list_spec2.
    + introv AiA.
      inversions AiA; eauto.
Qed.

Global Transparent fold_right.

Lemma length_equality : forall A (a : list A),
    LibList.length a = Datatypes.length a.
  induction a; cbn; eauto.
  rewrite <- IHa.
  rewrite length_cons.
  lia.
Qed.

(* stdlib lemma but in TLC version *)
Lemma map_map : forall (A B C:Type)(f:A->B)(g:B->C) l,
    map g (map f l) = map (fun x => g (f x)) l.
  induction l; cbn; auto.
  repeat rewrite map_cons.
  f_equal.
  auto.
Qed.

Lemma eq_dec_var (x y : var) : x = y \/ x <> y.
  lets: var_compare_eq x y.
  Require Import TLC.LibReflect.
  destruct (var_compare x y);
  rewrite isTrue_eq_if in H;
  case_if; auto.
Qed.

Lemma JMeq_from_eq : forall T (x y : T),
    x = y -> JMeq.JMeq x y.
  introv EQ.
  rewrite EQ. trivial.
Qed.

Lemma split_notin_subset_union : forall T (x : T) A B C,
    A \c B \u C ->
    x \notin B ->
    x \notin C ->
    x \notin A.
  introv Hsub HB HC.
  intro inA.
  lets Hf: Hsub inA.
  rewrite in_union in Hf.
  destruct Hf; eauto.
Qed.

Lemma in_from_list : forall As (x : var),
    x \in from_list As ->
          exists A, List.In A As /\ x = A.
  induction As; introv xin.
  - cbn in xin. exfalso; apply* in_empty_inv.
  - cbn in *.
    fold (from_list As) in xin.
    rewrite in_union in xin.
    destruct xin as [xin | xin].
    + rewrite in_singleton in xin. subst. eauto.
    + lets [A Ain]: IHAs xin.
      exists A. split*.
Qed.

Lemma env_map_compose : forall A B C (E : env A) (f : A -> B) (g : B -> C) (h : A -> C),
    (forall x, g (f x) = h x) ->
    EnvOps.map g (EnvOps.map f E) = EnvOps.map h E.
  induction E using env_ind; introv Hcomp;
    autorewrite with rew_env_map; trivial.
  - lets IH: IHE f g h.
    rewrite IH; auto.
    rewrite Hcomp. trivial.
Qed.

Ltac clean_empty_Δ :=
  repeat match goal with
         | [ H: context [ emptyΔ |,| ?D ] |- _ ] =>
           rewrite List.app_nil_r in H
         | [ H: context [ ?D |,| emptyΔ ] |- _ ] =>
           rewrite List.app_nil_l in H
         | [ H: context [ []* |,| ?D ] |- _ ] =>
           rewrite List.app_nil_r in H
         | [ H: context [ ?D |,| []* ] |- _ ] =>
           rewrite List.app_nil_l in H
         | [ |- context [ emptyΔ |,| ?D ] ] =>
           rewrite List.app_nil_r
         | [ |- context [ ?D |,| emptyΔ ] ] =>
           rewrite List.app_nil_l
         | [ |- context [ []* |,| ?D ] ] =>
           rewrite List.app_nil_r
         | [ |- context [ ?D |,| []* ] ] =>
           rewrite List.app_nil_l
         end.

Lemma binds_ext : forall A (x : var) (v1 v2 : A) E,
    binds x v1 E ->
    binds x v2 E ->
    v1 = v2.
  induction E using env_ind; introv b1 b2.
  - exfalso. apply* binds_empty_inv.
  - lets* [[? ?] | [? ?]]: binds_push_inv b1;
      lets* [[? ?] | [? ?]]: binds_push_inv b2.
      subst; trivial.
Qed.

Lemma list_fold_map : forall (A B : Type) (ls : list A) (f : B -> A -> B) (g : A -> A) (z : B),
    List.fold_left (fun a b => f a b) (List.map g ls) z
    =
    List.fold_left (fun a b => f a (g b)) ls z.
  induction ls; introv; cbn; eauto.
Qed.

Lemma notin_inverse : forall A (x y : A),
    x \notin \{ y } ->
    y \notin \{ x }.
  intros.
  assert (x <> y).
  - intro. subst. apply H. apply in_singleton_self.
  - apply* notin_singleton.
Qed.

Lemma LibList_map : forall T U (l : list T) (f : T -> U),
    List.map f l = LibList.map f l.
  induction l; intros; cbn in *; auto.
  rewrite IHl.
  rewrite LibList.map_cons. auto.
Qed.

Lemma LibList_mem : forall A (x : A) L,
    LibList.mem x L -> List.In x L.
  induction L; introv Hin; cbn in *; inversion Hin; eauto.
Qed.

Lemma subst_tb_many_split : forall Ah Ats Ph Pts F,
    EnvOps.map (subst_tb_many (Ah :: Ats) (Ph :: Pts)) F
    =
    EnvOps.map (subst_tb_many Ats Pts) (EnvOps.map (subst_tb Ah Ph) F).
  intros.
  rewrite map_def.
  rewrite map_map.
  repeat rewrite <- LibList_map.
  cbn.
  apply List.map_ext_in.
  intros.
  destruct a as [? [?]].
  cbn.
  f_equal.
Qed.

Ltac fresh_intros :=
    let envvars := gather_vars in
    intros;
    repeat match goal with
           (* TODO find only uninstantiated *)
      | [ H: ?x \notin ?L |- _ ] =>
        instantiate (1:=envvars) in H
           end.

Lemma union_distributes : forall T (A B C : fset T),
    (A \u B) \n C = (A \n C) \u (B \n C).
  intros.
  apply fset_extens; intros x H.
  - rewrite in_union.
    rewrite in_inter in H.
    destruct H as [HAB HC].
    rewrite in_union in HAB.
    destruct HAB.
    + left.
      rewrite~ in_inter.
    + right.
      rewrite~ in_inter.
  - rewrite in_union in H.
    destruct H as [H | H]; rewrite in_inter in H; destruct H;
      rewrite in_inter;
      split~; rewrite~ in_union.
Qed.

Lemma union_empty : forall T (A B : fset T),
    A \u B = \{} ->
    A = \{} /\ B = \{}.
  intros.
  split;
    apply fset_extens; intros x Hin;
      solve [
          assert (xAB: x \in A \/ x \in B); auto;
          rewrite <- in_union in xAB;
          rewrite H in xAB; auto
        | false* in_empty_inv].
Qed.

Lemma empty_inter_implies_notin : forall T (x : T) A B,
    A \n B = \{} ->
    x \in A -> x \notin B.
  intros.
  intro HF.
  asserts~ AB: (x \in A /\ x \in B).
  rewrite <- in_inter in AB.
  rewrite H in AB.
  apply* in_empty_inv.
Qed.

Ltac fold_subst_src :=
  repeat match goal with
  | [ H: context[LibList.fold_right (fun (x : var) (acc : fset var) => \{ x} \u acc) \{} (List.map fst ?Th)] |- _ ] =>
    fold (from_list (List.map fst Th)) in H;
    fold (substitution_sources Th) in H
  | [ |- context[LibList.fold_right (fun (x : var) (acc : fset var) => \{ x} \u acc) \{} (List.map fst ?Th)] ] =>
    fold (from_list (List.map fst Th));
    fold (substitution_sources Th)
  end.

Lemma subset_transitive : forall T (A B C : fset T),
    A \c B ->
    B \c C ->
    A \c C.
  introv AB BC.
  intros x In.
  auto.
Qed.

Lemma lists_map_eq : forall A B (f : A -> B) la lb a b,
    List.map f la = List.map f lb ->
    List.In (a, b) (zip la lb) ->
    f a = f b.
  induction la as [| a' la]; destruct lb as [| b' lb]; introv Map In; try solve [inversion Map | inversion In].
  cbn in *.
  inversions Map.
  destruct In as [In | In].
  - inversions~ In.
  - apply IHla with lb; auto.
Qed.

Lemma equations_from_lists_are_equations : forall D Ts Us,
    D = equations_from_lists Ts Us ->
    (forall eq, List.In eq D -> exists ϵ, eq = tc_eq ϵ).
  induction D; cbn; introv Deq Hin; auto.
  + false.
  + destruct Ts; destruct Us; cbn; try solve [false].
    cbn in Deq.
    inversions Deq.
    destruct Hin; subst; eauto.
Qed.

Open Scope list_scope.

Ltac fold_delta :=
  repeat match goal with
  | [ H: context [List.map tc_var ?As] |- _ ] =>
    fold (tc_vars As) in H
  | [ H: context [ (tc_var ?X) :: ?As] |- _ ] =>
    match As with
    | []* => fail 1
    | _ => fold ([tc_var X]* ++ As) in H
    end
  | [ H: context [ (tc_eq ?eq) :: ?As] |- _ ] =>
    match As with
    | []* => fail 1
    | _ => fold ([tc_eq eq]* ++ As) in H
    end
  | [ |- context [List.map tc_var ?As] ] =>
    fold (tc_vars As)
  | [ |- context [ (tc_var ?X) :: ?As] ] =>
    match As with
    | []* => fail 1
    | _ => fold ([tc_var X]* ++ As)
    end
  | [ |- context [ (tc_eq ?eq) :: ?As] ] =>
    match As with
    | []* => fail 1
    | _ => fold ([tc_eq eq]* ++ As)
    end
  end.

Ltac destruct_in_app :=
  match goal with
  | [ H: List.In ?X (?A ++ ?B) |- _ ] =>
    apply List.in_app_or in H;
    destruct H
  | [ H: is_var_defined (?A ++ ?B) ?X |- _ ] =>
    unfold is_var_defined in H;
    apply List.in_app_or in H;
    destruct H
  end.
Close Scope list_scope.

Lemma Forall2_eq_len : forall A P (l1 l2 : list A),
    List.Forall2 P l1 l2 ->
    List.length l1 = List.length l2.
  induction l1; destruct l2;
    introv H; cbn in *;
      inversions H; auto.
Qed.

Lemma nth_error_map : forall A B (F : A -> B) l n d,
    List.nth_error (List.map F l) n = Some d ->
    exists e, List.nth_error l n = Some e /\ d = F e.
Proof.
  induction l; destruct n; introv EQ; cbn in *; try solve [false*].
  - inversions EQ. eauto.
  - eauto.
Qed.

Lemma inzip_map_clause_trm : forall A F (Defs : list A) Clauses def cl,
    List.In (def, cl)
            (zip Defs (map_clause_trm_trm F Clauses)) ->
    exists (clA : nat) (clT : trm),
      List.In (def, (clause clA clT)) (zip Defs Clauses) /\
      cl = clause clA (F clT).
  introv In.
  lets [n [ND NC]]: Inzip_to_nth_error In.
  unfold map_clause_trm_trm in NC.
  lets [[clA clT] [? ?]]: nth_error_map NC.
  exists clA clT.
  split~.
  apply* Inzip_from_nth_error.
Qed.

(** The value relation is restricted to well-formed objects. *)
Lemma value_regular : forall t,
  value t -> term t.
Proof.
  induction 1; autos*.
Qed.

