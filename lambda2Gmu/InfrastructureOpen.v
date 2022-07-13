Set Implicit Arguments.
Require Import Prelude.
Require Import InfrastructureFV.
Require Import TLC.LibLogic.
Require Import TLC.LibLN.
(* large portions of this are based on the TLC formalisation of FSub *)


(** ** Preserving size *)
Lemma open_ee_var_preserves_size : forall e x n vk,
    trm_size e = trm_size (open_ee_rec n (trm_fvar vk x) e).
  induction e using trm_ind'; introv; try solve [cbn; try case_if; cbn; eauto].
  cbn.
  - rewrite <- IHe.
    f_equal.
    f_equal.
    unfold map_clause_trms.
    rewrite List.map_map.
    apply List.map_ext_in.
    intros cl clin.
    rewrite List.Forall_forall in *.
    lets* Heq: H cl clin.
    destruct cl.
    unfold clauseTerm.
    apply* Heq.
Qed.

Lemma open_te_var_preserves_size : forall e x n,
    trm_size e = trm_size (open_te_rec n (typ_fvar x) e).
  induction e using trm_ind'; introv; try solve [cbn; try case_if; cbn; eauto].
  - cbn.
    rewrite <- IHe.
    f_equal.
    f_equal.
    unfold map_clause_trms.
    rewrite List.map_map.
    apply List.map_ext_in.
    intros cl clin.
    rewrite List.Forall_forall in *.
    lets* Heq: H cl clin.
    destruct cl.
    unfold clauseTerm.
    apply* Heq.
Qed.

Lemma open_tt_var_preserves_size : forall T X n,
    typ_size T = typ_size (open_tt_rec n (typ_fvar X) T).
  induction T using typ_ind' ; introv; try solve [cbn; try case_if; cbn; eauto].
  - cbn. crush_compare.
  - cbn.
    rewrite List.map_map.
    assert ((List.map typ_size ls) = (List.map (fun x : typ => typ_size (open_tt_rec n0 (typ_fvar X) x)) ls)) as Hmapeq.
    + apply List.map_ext_in.
      rewrite List.Forall_forall in H.
      intros. apply* H.
    + rewrite Hmapeq. auto.
Qed.

(** ** Properties of type substitution in type *)

(** Substitution on indices is identity on well-formed terms. *)

Inductive typ_closed_in_surroundings : nat -> typ -> Prop :=
| closed_typ_bvar : forall J k, J < k -> typ_closed_in_surroundings k (typ_bvar J)
| closed_typ_fvar : forall X k, typ_closed_in_surroundings k (typ_fvar X)
| closed_typ_unit : forall k, typ_closed_in_surroundings k (typ_unit)
| closed_typ_tuple : forall T1 T2 k,
    typ_closed_in_surroundings k T1 ->
    typ_closed_in_surroundings k T2 ->
    typ_closed_in_surroundings k (T1 ** T2)
| closed_typ_arrow : forall T1 T2 k,
    typ_closed_in_surroundings k T1 ->
    typ_closed_in_surroundings k T2 ->
    typ_closed_in_surroundings k (T1 ==> T2)
| closed_typ_all : forall T k,
    typ_closed_in_surroundings (S k) T ->
    typ_closed_in_surroundings k (typ_all T)
| closed_typ_gadt : forall Ts N k,
    List.Forall (typ_closed_in_surroundings k) Ts ->
    typ_closed_in_surroundings k (typ_gadt Ts N).

Lemma opening_adds_one : forall T X k n,
    (* for example, typ_closed_in_surroundings 0 (open_tt_rec 42 (typ_fvar X) (typ_bvar 42))
       which evaluates to typ_fvar X, so it is open in 0
       but
     *)
    typ_closed_in_surroundings n (open_tt_rec k (typ_fvar X) T) ->
    (*
      the original term (typ_bvar 42), is not open in 1, so that's why we need k+1 too
      - this is the case where the maximum binder disappeared in open
      case n+1 is the case where it was some smaller binder and so the other binders get incremented
    *)
    typ_closed_in_surroundings (max (S n) (S k)) T.
  induction T using typ_ind'; introv Hc; try solve [inversions Hc; constructor*].
  - cbn in Hc.
    crush_compare; cbn in *; econstructor; try lia.
    inversions Hc. lia.
  - constructor*.
    inversions Hc.
    rewrite List.Forall_forall in *.
    intros T Hin.
    lets* IH: H T Hin X k n0.
    apply* IH.
    apply* H2.
    apply* List.in_map.
Qed.

Lemma type_closed : forall T,
    type T -> typ_closed_in_surroundings 0 T.
  induction 1; constructor*.
  - pick_fresh X.
    lets* Hoao: opening_adds_one T2 X 0 0.
  - rewrite List.Forall_forall.
    auto.
Qed.

Lemma closed_id : forall T U n k,
    typ_closed_in_surroundings n T ->
    k >= n ->
    T = open_tt_rec k U T.
  induction T using typ_ind'; introv Hc Hk; eauto;
    try solve [
          cbn; crush_compare; inversions Hc; lia
        | cbn; inversions Hc;
          lets* IH1: IHT1 U n k;
          lets* IH2: IHT2 U n k;
          rewrite* <- IH1;
          rewrite* <- IH2
          ].
  - lets* IH: IHT U (S n) (S k).
    cbn. inversions Hc.
    rewrite* <- IH. lia.
  - cbn.
    f_equal.
    inversions Hc.
    rewrite List.Forall_forall in *.
    rewrite <- List.map_id at 1.
    apply List.map_ext_in.
    intros T Hin.
    lets* IH: H Hin.
Qed.

Lemma open_tt_rec_type : forall T U,
  type T -> forall k, T = open_tt_rec k U T.
Proof.
  introv Htype. intros.
  lets* Hc: closed_id T U 0 k.
  apply Hc.
  - apply* type_closed.
  - lia.
Qed.

(* this one describes terms being closed in relation to type-variables, not term-varaibles*)
Inductive te_closed_in_surroundings : nat -> trm -> Prop :=
| closed_trm_bvar : forall i k, te_closed_in_surroundings k (trm_bvar i)
| closed_trm_fvar : forall x vk k, te_closed_in_surroundings k (trm_fvar vk x)
| closed_trm_unit : forall k, te_closed_in_surroundings k (trm_unit)
| closed_trm_fst : forall e k, te_closed_in_surroundings k e -> te_closed_in_surroundings k (trm_fst e)
| closed_trm_snd : forall e k, te_closed_in_surroundings k e -> te_closed_in_surroundings k (trm_snd e)
| closed_trm_tuple : forall e1 e2 k, te_closed_in_surroundings k e1 ->
                                te_closed_in_surroundings k e2 ->
                                te_closed_in_surroundings k (trm_tuple e1 e2)
| closed_trm_abs : forall e T k, te_closed_in_surroundings k e ->
                            typ_closed_in_surroundings k T ->
                            te_closed_in_surroundings k (trm_abs T e)
| closed_trm_app : forall e1 e2 k, te_closed_in_surroundings k e1 ->
                              te_closed_in_surroundings k e2 ->
                              te_closed_in_surroundings k (trm_app e1 e2)
| closed_trm_tabs : forall e k, te_closed_in_surroundings (S k) e ->
                           te_closed_in_surroundings k (trm_tabs e)
| closed_trm_tapp : forall e T k, te_closed_in_surroundings k e ->
                            typ_closed_in_surroundings k T ->
                            te_closed_in_surroundings k (trm_tapp e T)
| closed_trm_fix : forall e T k, te_closed_in_surroundings k e ->
                            typ_closed_in_surroundings k T ->
                            te_closed_in_surroundings k (trm_fix T e)
| closed_trm_let : forall e1 e2 k, te_closed_in_surroundings k e1 ->
                              te_closed_in_surroundings k e2 ->
                              te_closed_in_surroundings k (trm_let e1 e2)
| closed_term_constructor : forall Ts N e k,
    List.Forall (typ_closed_in_surroundings k) Ts ->
    te_closed_in_surroundings k e ->
    te_closed_in_surroundings k (trm_constructor Ts N e)
| closed_term_match : forall G e ms k,
    te_closed_in_surroundings k e ->
    (forall cl, List.In cl ms -> te_closed_in_surroundings (k + clauseArity cl) (clauseTerm cl)) ->
    te_closed_in_surroundings k (trm_matchgadt e G ms)
.

Lemma te_opening_te_adds_one : forall e X k n,
    te_closed_in_surroundings n (open_te_rec k (typ_fvar X) e) ->
    te_closed_in_surroundings (max (S n) (S k)) e.
Proof.
  induction e using trm_ind'; introv Hc; inversions Hc;
    try solve [
          constructor*
        | constructor*; apply* opening_adds_one
        ].
  - constructor*.
    rewrite List.Forall_forall in *.
    intros T Hin.
    apply* opening_adds_one.
    apply* H2.
    unfold open_typlist_rec.
    apply* List.in_map.
  - constructor*.
    introv clin.
    rewrite List.Forall_forall in *.
    lets* IHcl: H clin.
    destruct cl as [clArity clTerm].
    cbn.
    cbn in IHcl.
    assert (Harit: Nat.max n k + clArity = Nat.max (n + clArity) (k + clArity)); try lia.
    rewrite Harit.
    apply IHcl with X.
    lets* IHcl2: H5 (clause clArity (open_te_rec (k + clArity) (typ_fvar X) clTerm)).
    cbn in IHcl2.
    apply* IHcl2.
    apply* List.in_map_iff.
    exists (clause clArity clTerm). eauto.
Qed.

Lemma te_opening_ee_preserves : forall e x vk k n,
    te_closed_in_surroundings n (open_ee_rec k (trm_fvar vk x) e) ->
    te_closed_in_surroundings n e.
  induction e using trm_ind'; introv Hc; try solve [inversions Hc; constructor*].
  - inversions Hc.
    rewrite List.Forall_forall in *.
    constructor*.
    introv clin.
    apply H with x vk (S k); eauto.
    destruct cl as [clA clT].
    lets* Hcl: H5 (clause clA (open_ee_rec (S k) (trm_fvar vk x) clT)).
    cbn in Hcl.
    cbn.
    apply Hcl.
    apply* List.in_map_iff.
    exists (clause clA clT). eauto.
Qed.

Lemma te_opening_te_many_adds : forall As N n e,
    te_closed_in_surroundings n (open_te_many_var As e) ->
    length As = N ->
    te_closed_in_surroundings (N + n) e.
  induction As as [| Ah Ats]; destruct N; introv Hcl Hlen; inversion Hlen.
  - cbn in *. eauto.
  - cbn in Hcl.
    fold (open_te_many_var Ats (e open_te_var Ah)) in Hcl.

    lets IH: IHAts (length Ats) n (e open_te_var Ah).
    assert (Harit2: Nat.max (S (length Ats + n)) (S 0) = (S (length Ats) + n)); try lia.
    rewrite <- Harit2.
    apply te_opening_te_adds_one with Ah.
    fold (e open_te_var Ah).
    apply* IH.
Qed.

Lemma term_te_closed : forall e,
    term e -> te_closed_in_surroundings 0 e.
Proof.
  induction 1; try solve [
                     constructor*
                   | match goal with
                     | H: forall x : var, x \notin ?L ->
                                     te_closed_in_surroundings 0 (open_ee ?e1 (trm_fvar ?vk x))
                                     |- _ =>
                       constructor*; try solve [
                                           pick_fresh X; apply* te_opening_ee_preserves; lets* He: H X
                                         | apply* type_closed]
                     end
                   ].
  - constructor*.
    rewrite List.Forall_forall. intros T Hin.
    apply* type_closed.
  - constructor*.
    pick_fresh X.
    lets* Hopen: te_opening_te_adds_one e1 X 0 0.
  - constructor*. apply* type_closed.
  - constructor*.
    introv clin.
    cbn.
    lets* fresh_alphas: exist_alphas L (clauseArity cl).
    inversion fresh_alphas as [Alphas [Hlen [Hdist Hnotin]]].
    pick_fresh x.
    assert (xfresh: x \notin L); eauto.
    assert (xfreshA: x \notin from_list Alphas); eauto.
    lets hmm: H1 clin Alphas x Hlen Hdist.
    lets hmm2: hmm Hnotin xfresh xfreshA.
    unfold open_ee in hmm2.
    lets hmm3: te_opening_ee_preserves hmm2.
    lets hmm4: te_opening_te_many_adds (clauseArity cl) hmm3.
    assert (Hneutral: forall n, n + 0 = n); try (intro; lia).
    rewrite Hneutral in hmm4.
    apply* hmm4.
Qed.

Lemma te_closed_id : forall e T n k,
    te_closed_in_surroundings n e ->
    k >= n ->
    e = open_te_rec k T e.
Proof.
  induction e using trm_ind'; introv Hc Hk; eauto; inversions Hc; cbn; f_equal;
    try (match goal with
         | IH: forall T n k, ?P1 -> ?P2 -> ?e1 = open_te_rec k T ?e1 |- _ => apply* IH
         end);
    try apply* closed_id;
    try lia.
  - unfold open_typlist_rec.
    rewrite <- List.map_id at 1.
    apply* List.map_ext_in.
    intro U.
    rewrite List.Forall_forall in *.
    lets* HC: H2 U.
    lets*: closed_id U T n k.
  - rewrite <- List.map_id at 1.
    apply* List.map_ext_in.
    intros cl clin.
    rewrite List.Forall_forall in *.
    destruct cl as [clA clT].
    f_equal.
    lets* IH: H (clause clA clT) T (n + clA) (k + clA).
    cbn in IH.
    apply* IH.
    + lets* Hcl: H5 (clause clA clT).
    + lia.
Qed.

Lemma open_te_rec_term : forall e U,
  term e -> forall k, e = open_te_rec k U e.
Proof.
  introv Hterm. intros.
  lets* Hc: te_closed_id e U 0 k.
  apply Hc.
  - apply* term_te_closed.
  - lia.
Qed.

Lemma open_ee_rec_term_core : forall e j v u i, i <> j ->
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof.
  induction e using trm_ind'; introv Neq Hopen; simpl in *; inversion Hopen; f_equal*.
  - crush_eq. crush_eq. subst. intuition.
  - rewrite List.Forall_forall in *.
    rewrite List.map_map in H2.
    rewrite <- List.map_id at 1.
    apply* List.map_ext_in.
    intros cl clin.
    lets* Hcleq: ext_in_map H2 clin.
    destruct cl.
    inversion* Hcleq.
    f_equal.
    lets* IH: H clin (S j) (S i).
Qed.

Lemma open_ee_rec_type_core : forall e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) ->
  e = open_ee_rec i u e.
Proof.
  induction e using trm_ind'; introv Ho; simpls; inversion Ho; f_equal*.
  - rewrite List.Forall_forall in *.
    rewrite List.map_map in H2.
    rewrite <- List.map_id at 1.
    apply* List.map_ext_in.
    intros cl clin.
    lets* Hcleq: ext_in_map H2 clin.
    destruct cl.
    inversion* Hcleq.
    f_equal.
    lets* IH: H clin (j + clArity) (S i).
Qed.

Lemma open_ee_rec_type_many : forall As k u e,
  open_te_many_var As e =
  open_ee_rec k u (open_te_many_var As e) ->
  e = open_ee_rec k u e.
  induction As as [| Ah Ats]; introv Heq.
  - cbn in Heq. eauto.
  - cbn in Heq.
    fold (open_te_many_var Ats (e open_te_var Ah)) in Heq.
    lets* IH: IHAts k u (e open_te_var Ah) Heq.
    apply* open_ee_rec_type_core.
Qed.

Lemma open_ee_rec_term : forall u e,
  term e -> forall k, e = open_ee_rec k u e.
Proof.
  induction 1; intro k;
    simpl; f_equal*.
  - unfolds open_ee. pick_fresh x.
    apply* (@open_ee_rec_term_core e1 0 (trm_fvar lam_var x)).

  - unfolds open_te.
    pick_fresh X.
    apply* (@open_ee_rec_type_core e1 0 (typ_fvar X)).

  - unfolds open_ee. pick_fresh x.
    apply* (@open_ee_rec_term_core v1 0 (trm_fvar fix_var x)).

  - unfolds open_ee. pick_fresh x.
    apply* (@open_ee_rec_term_core e2 0 (trm_fvar lam_var x)).
  - rewrite <- List.map_id at 1.
    apply List.map_ext_in.
    intros cl clin.
    destruct cl as [clA clT].
    f_equal.

    lets* fresh_alphas: exist_alphas L clA.
    inversion fresh_alphas as [Alphas [Hlen [Hdist Hnotin]]].
    pick_fresh x.
    assert (xfresh: x \notin L); eauto.


    lets* IHcl: H1 clin Alphas x.
    cbn in IHcl.
    lets* IHcl2: IHcl Hlen Hdist Hnotin xfresh.

    assert (Hpart: open_te_many_var Alphas clT =
                   open_ee_rec (S k) u (open_te_many_var Alphas clT)).
    + unfolds open_ee.
      eapply open_ee_rec_term_core.
      2: {
        apply* IHcl2.
      }
      lia.
    + apply* open_ee_rec_type_many.
Qed.

Lemma rewrite_open_tt_many_gadt : forall OTs GTs N,
    open_tt_many OTs (typ_gadt GTs N) =
    typ_gadt (List.map (open_tt_many OTs) GTs) N.
  induction OTs as [| OTh OTt]; introv.
  - cbn. rewrite* List.map_id.
  - cbn.
    assert (List.map (fun T : typ => open_tt_many OTt (open_tt T OTh)) GTs = List.map (open_tt_many OTt) (List.map (open_tt_rec 0 OTh) GTs)).
    + rewrite List.map_map.
      apply* List.map_ext.
    + rewrite H.
      apply IHOTt.
Qed.

Lemma open_tt_many_closed : forall As T,
    type T ->
    open_tt_many As T = T.
  induction As; introv Hcl.
  - cbn. trivial.
  - cbn. unfold open_tt.
    rewrite* <- open_tt_rec_type.
Qed.
