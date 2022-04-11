Set Implicit Arguments.
Require Import GMuAnnot.Prelude.
Require Import GMuAnnot.InfrastructureFV.
Require Import GMuAnnot.InfrastructureOpen.
Require Import TLC.LibLogic.
Require Import TLC.LibLN.
(* large portions of this are based on the TLC formalisation of FSub *)


Lemma subst_tt_fresh : forall Z U T,
  Z \notin fv_typ T -> subst_tt Z U T = T.
Proof.
  induction T using typ_ind' ; simpl; intros; f_equal*.
  - case_var*.
  - symmetry.
    apply map_id.
    introv Lin.
    handleforall.
    symmetry.
    apply* Hforall.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_tt_open_tt_rec : forall T1 T2 X P n, type P ->
  subst_tt X P (open_tt_rec n T2 T1) =
  open_tt_rec n (subst_tt X P T2) (subst_tt X P T1).
Proof.
  introv WP. generalize n.
  induction T1 using typ_ind' ; intros k; simpls; f_equal*.
  - crush_compare.
  - case_var*. rewrite* <- open_tt_rec_type.
  - rewrite* List.map_map.
    rewrite* List.map_map.
    apply List.map_ext_in.
    handleforall.
    introv Lin.
    apply* Hforall.
Qed.

Lemma subst_tt_open_tt : forall T1 T2 X P, type P ->
  subst_tt X P (open_tt T1 T2) =
  open_tt (subst_tt X P T1) (subst_tt X P T2).
Proof.
  unfold open_tt. autos* subst_tt_open_tt_rec.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_tt_open_tt_var : forall X Y U T, Y <> X -> type U ->
  (subst_tt X U T) open_tt_var Y = subst_tt X U (T open_tt_var Y).
Proof.
  introv Neq Wu. rewrite* subst_tt_open_tt.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_tt_intro : forall X T2 U,
  X \notin fv_typ T2 -> type U ->
  open_tt T2 U = subst_tt X U (T2 open_tt_var X).
Proof.
  introv Fr Wu. rewrite* subst_tt_open_tt.
  rewrite* subst_tt_fresh. simpl. case_var*.
Qed.

Lemma subst_commutes_with_unrelated_opens : forall Xs T V Y,
    (forall X, List.In X Xs -> X <> Y) ->
    type V ->
    subst_tt Y V (open_tt_many_var Xs T) =
    (open_tt_many_var Xs (subst_tt Y V T)).
  induction Xs as [| Xh Xt]; introv Hneq Htyp.
  - cbn. eauto.
  - cbn.
    fold (open_tt_many_var Xt (T open_tt_var Xh)).
    fold (open_tt_many_var Xt (subst_tt Y V T open_tt_var Xh)).
    rewrite* subst_tt_open_tt_var; eauto with listin.
Qed.

Lemma subst_intro_commutes_opens : forall Xs T Y V,
    Y \notin fv_typ T ->
    (forall X, List.In X Xs -> X <> Y) ->
    type V ->
    open_tt_many_var Xs (open_tt T V) =
    subst_tt Y V (open_tt_many_var Xs (T open_tt_var Y)).
  induction Xs as [| Xh Xt]; introv Hfv Hneq Htyp.
  - cbn. apply* subst_tt_intro.
  - cbn.
    fold (open_tt_many_var Xt (open_tt T V open_tt_var Xh)).
    fold (open_tt_many_var Xt ((T open_tt_var Y) open_tt_var Xh)).
    rewrite* subst_commutes_with_unrelated_opens.
    f_equal.
    rewrite* <- subst_tt_open_tt_var.
    + rewrite* <- subst_tt_intro.
    + apply* Hneq. cbn; eauto.
    + eauto with listin.
Qed.

Lemma sublist_tail_prop : forall A (Uh : A) (Ut : list A) (P : A -> Prop),
  (forall U : A, List.In U (Uh :: Ut) -> P U) ->
  forall U : A, List.In U Ut -> P U.
  introv Hbigger Hin.
  apply* Hbigger.
  cbn.
  eauto.
Qed.

Lemma sublist_head_prop : forall A (Uh : A) (Ut : list A) (P : A -> Prop),
  (forall U : A, List.In U (Uh :: Ut) -> P U) ->
  P Uh.
  introv Hbigger.
  apply* Hbigger.
  cbn.
  eauto.
Qed.

Lemma subst_tt_intro_many : forall Xs T Us,
    length Xs = length Us ->
    DistinctList Xs ->
    (forall X, List.In X Xs -> X \notin fv_typ T) ->
    (forall X U, List.In X Xs -> List.In U Us -> X \notin fv_typ U) ->
    (forall U, List.In U Us -> type U) ->
    open_tt_many Us T = subst_tt_many Xs Us (open_tt_many_var Xs T).
  induction Xs as [| Xh Xt]; introv Hleneq Hdistinct HXfv HXUfv XUtyp.
  - destruct Us.
    + cbv. trivial.
    + inversions Hleneq.
  - destruct Us as [| Uh Ut].
    + inversions Hleneq.
    + cbn.
      fold (open_tt_many_var Xt (T open_tt_var Xh)).
      rewrite* <- subst_intro_commutes_opens; eauto with listin.
      * apply* IHXt; try solve [intuition; eauto with listin].
        -- inversion* Hdistinct.
        -- introv XiXt.
           lets* Hless: fv_smaller T Uh 0.
           fold (open_tt T Uh) in Hless.
           intro Hin.
           apply Hless in Hin.
           rewrite in_union in Hin.
           destruct Hin as [Hin | Hin].
           ++ apply* HXfv. listin.
           ++ apply* HXUfv; listin.
      * inversions Hdistinct.
        introv XiXt.
        intro. subst. contradiction.
Qed.


(** Substitution for a fresh name is identity. *)

Lemma subst_te_fresh : forall X U e,
  X \notin fv_trm e -> subst_te X U e = e.
Proof.
  induction e using trm_ind'; simpl; intros; f_equal*; autos* subst_tt_fresh.
  - symmetry.
    apply map_id. introv Lin.
    symmetry.
    apply* subst_tt_fresh.
  - apply* IHe.
    rewrite notin_union in H0.
    destruct H0.
    lets*: fv_fold_general H0.
  - unfold map_clause_trm_trm.
    rewrite List.Forall_forall in *.
    rewrite <- List.map_id.
    apply List.map_ext_in.
    intros cl clin.
    lets* Heq: H cl clin.
    destruct cl.
    f_equal.
    apply* Heq.
    rewrite notin_union in H0.
    destruct H0.
    lets*: fv_fold_in_clause.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_te_open_te : forall e T X U, type U ->
  subst_te X U (open_te e T) =
  open_te (subst_te X U e) (subst_tt X U T).
Proof.
  intros. unfold open_te. generalize 0.
  induction e using trm_ind'; intro n0; simpls; f_equal*;
    autos* subst_tt_open_tt_rec.
  - unfold open_typlist_rec.
    rewrite List.map_map.
    rewrite List.map_map.
    apply List.map_ext.
    intro.
    apply* H0.
  - unfold map_clause_trm_trm.
    repeat rewrite List.map_map.
    apply List.map_ext_in.
    intros cl clin.
    rewrite List.Forall_forall in *.
    lets* Heq: H0 cl clin.
    destruct cl.
    f_equal.
    eauto.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_te_open_te_var : forall X Y U e, Y <> X -> type U ->
  (subst_te X U e) open_te_var Y = subst_te X U (e open_te_var Y).
Proof.
  introv Neq Wu. rewrite* subst_te_open_te.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_te_intro : forall X U e,
  X \notin fv_trm e -> type U ->
  open_te e U = subst_te X U (e open_te_var X).
Proof.
  introv Fr Wu. rewrite* subst_te_open_te.
  rewrite* subst_te_fresh. simpl. case_var*.
Qed.


(** Substitution for a fresh name is identity. *)
Lemma subst_ee_fresh : forall x k u e,
  x \notin fv_trm e -> subst_ee x k u e = e.
Proof.
  induction e using trm_ind'; simpl; intros; f_equal*.
  - case_if*.
    inversions C.
    false* in_singleton_self.
  - apply IHe.
    rewrite notin_union in H0.
    destruct H0.
    lets*: fv_fold_base_clause.
  - unfold map_clause_trm_trm.
    rewrite <- List.map_id.
    apply List.map_ext_in.
    intros cl clin.
    rewrite List.Forall_forall in *.
    lets* Heq: H clin.
    unfold clauseTerm in Heq.
    lets Hfv: fv_fold_in_clause.
    lets* Hfv2: Hfv cl clauses.
    unfold clauseTerm in Hfv2.
    destruct cl.
    f_equal.
    apply Heq.
    rewrite notin_union in H0.
    destruct H0.
    apply* Hfv2.
Qed.

(** Substitution distributes on the open operation. *)
Lemma subst_ee_open_ee : forall t1 t2 u k x, term u ->
  subst_ee x k u (open_ee t1 t2) =
  open_ee (subst_ee x k u t1) (subst_ee x k u t2).
Proof.
  intros. unfold open_ee. generalize 0.
  induction t1 using trm_ind'; intro n0; simpls; f_equal*.
  - crush_eq.
  - case_if*. rewrite* <- open_ee_rec_term.
  - unfold map_clause_trm_trm.
    repeat rewrite List.map_map.
    apply List.map_ext_in.
    intros cl clin.
    rewrite List.Forall_forall in *.
    lets* IH: H0 clin.
    destruct cl.
    f_equal.
    eauto.
Qed.

(** Substitution and open_var for distinct names commute. *)
Lemma subst_ee_open_ee_var : forall vk x y k u e, y <> x -> term u ->
  open_ee (subst_ee x k u e) (trm_fvar vk y) = subst_ee x k u (open_ee e (trm_fvar vk y)).
Proof.
  introv Neq Wu. rewrite* subst_ee_open_ee.
  simpl. case_if*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_ee_intro : forall vk x u e,
  x \notin fv_trm e -> term u ->
  open_ee e u = subst_ee x vk u (open_ee e (trm_fvar vk x)).
Proof.
  introv Fr Wu. rewrite* subst_ee_open_ee.
  rewrite* subst_ee_fresh. simpl. case_if*.
Qed.

(** Interactions between type substitutions in terms and opening
  with term variables in terms. *)

Lemma subst_te_open_ee_var : forall Z P vk x e,
  open_ee (subst_te Z P e) (trm_fvar vk x) = subst_te Z P (open_ee e (trm_fvar vk x)).
Proof.
  introv. unfold open_ee. generalize 0.
  induction e using trm_ind'; intros; simpl; f_equal*.
  - crush_eq.
  - unfold map_clause_trm_trm.
    repeat rewrite List.map_map.
    apply List.map_ext_in.
    intros cl clin.
    rewrite List.Forall_forall in *.
    lets* IH: H clin.
    destruct cl.
    f_equal.
    eauto.
Qed.

(** Interactions between term substitutions in terms and opening
  with type variables in terms. *)

Lemma subst_ee_open_te_var : forall z k u e X, term u ->
  (subst_ee z k u e) open_te_var X = subst_ee z k u (e open_te_var X).
Proof.
  introv. unfold open_te. generalize 0.
  induction e using trm_ind'; intros; simpl; f_equal*.
  - case_if*. symmetry. autos* open_te_rec_term.
  - unfold map_clause_trm_trm.
    repeat rewrite List.map_map.
    apply List.map_ext_in.
    intros cl clin.
    rewrite List.Forall_forall in *.
    lets* IH: H clin.
    destruct cl.
    f_equal.
    eauto.
Qed.

(** Substitutions preserve local closure. *)

Lemma subst_map_reverse_type : forall Tparams Z P,
    type P ->
    (forall Tparam : typ,
        List.In Tparam Tparams -> type P -> type (subst_tt Z P Tparam)) ->
    forall Tparam : typ, List.In Tparam (List.map (subst_tt Z P) Tparams) -> type Tparam.
  introv HP HTP.
  introv Tin.
  apply List.in_map_iff in Tin.
  destruct Tin as [T Tand].
  destruct Tand as [Teq Tin].
  rewrite <- Teq.
  apply* HTP.
Qed.

Lemma subst_tt_type : forall T Z P,
  type T -> type P -> type (subst_tt Z P T).
Proof.
  induction 1; intros; simpl; auto.
  - case_var*.
  - apply_fresh* type_all as X. rewrite* subst_tt_open_tt_var.
  - econstructor.
    apply* subst_map_reverse_type.
Qed.

Lemma subst_commutes_with_unrelated_opens_te_te : forall Xs e V Y,
    (forall X, List.In X Xs -> X <> Y) ->
    type V ->
    subst_te Y V (open_te_many_var Xs e) =
    (open_te_many_var Xs (subst_te Y V e)).
  induction Xs as [| Xh Xt]; introv Hneq Htyp.
  - cbn. eauto.
  - cbn.
    fold (open_te_many_var Xt (e open_te_var Xh)).
    fold (open_te_many_var Xt (subst_te Y V e open_te_var Xh)).
    rewrite* subst_te_open_te_var; eauto with listin.
Qed.

Lemma subst_commutes_with_unrelated_opens_te_ee : forall Xs e v y k,
    term v ->
    subst_ee y k v (open_te_many_var Xs e) =
    (open_te_many_var Xs (subst_ee y k v e)).
  induction Xs as [| Xh Xt]; introv Htyp.
  - cbn. eauto.
  - cbn.
    fold (open_te_many_var Xt (e open_te_var Xh)).
    fold (open_te_many_var Xt (subst_ee y k v e open_te_var Xh)).
    rewrite* subst_ee_open_te_var; eauto with listin.
Qed.

Lemma subst_te_term : forall e Z P,
    term e -> type P -> term (subst_te Z P e)
with subst_te_value : forall e Z P,
    value e -> type P -> value (subst_te Z P e).
Proof.
  - lets: subst_tt_type. induction 1; intros; cbn; auto.
    + constructor*.
      apply* subst_map_reverse_type.
    + apply_fresh* term_abs as x. rewrite* subst_te_open_ee_var.
    + apply_fresh* term_tabs as x.
      rewrite* subst_te_open_te_var.
      rewrite* subst_te_open_te_var.
    + apply_fresh* term_fix as x.
      rewrite* subst_te_open_ee_var.
      rewrite* subst_te_open_ee_var.
    + apply_fresh* term_let as x. rewrite* subst_te_open_ee_var.
    + econstructor; eauto.
      intros cl clinmap Alphas x Hlen Hdist Afresh xfresh xfreshA.
      destruct cl as [clA clT].
      unfold map_clause_trm_trm in clinmap.
      lets cl2: clinmap.
      apply List.in_map_iff in cl2.
      destruct cl2 as [[cl'A cl'T] [cl'eq cl'in]].
      inversion cl'eq. subst.
      cbn.
      lets* IH: H2 cl'in Alphas x Hlen Hdist.
      cbn in IH.
      instantiate (1:=(L \u \{ Z })) in Afresh.
      assert (Hpull:
          open_te_many_var Alphas (subst_te Z P cl'T) open_ee_varlam x
          =
          subst_te Z P (open_te_many_var Alphas cl'T open_ee_varlam x)
        ).
      * rewrite <- subst_commutes_with_unrelated_opens_te_te.
        rewrite* subst_te_open_ee_var.
        -- intros A AAlpha.
           assert (A \notin L \u \{ Z }); solve [apply* Afresh | eauto].
        -- eauto.
      * rewrite Hpull.
        apply* IH.
        introv Ain.
        assert (A \notin L \u \{ Z}); eauto.
  - lets: subst_tt_type; induction 1; intros; cbn; auto;
      match goal with
      | H: term _ |- _ => rename H into Hterm end.
    + apply value_abs.
      inversions Hterm.
      apply_fresh* term_abs as x.
      rewrite* subst_te_open_ee_var.
    + apply value_tabs. inversion Hterm.
      apply_fresh* term_tabs as x.
      rewrite* subst_te_open_te_var.
      rewrite* subst_te_open_te_var.
    + constructor*.
      inversions Hterm.
      constructor*.
    + constructor*.
      constructor*.
      * apply* value_is_term.
      * apply* subst_map_reverse_type.
        inversion* Hterm.
Qed.


(* this may be problematic as I now require e2 to be value not only term, but maybe it will be enough? *)
Lemma subst_ee_term : forall e1 Z e2 k,
    term e1 -> value e2 -> term (subst_ee Z k e2 e1)
with subst_ee_value : forall e1 Z e2 k,
    value e1 -> value e2 -> value (subst_ee Z k e2 e1).
Proof.
  - induction 1; intros; simpl; auto.
    + case_if*. apply~ value_regular.
    + apply_fresh* term_abs as y. rewrite* subst_ee_open_ee_var.
      apply~ value_regular.
    + apply_fresh* term_tabs as Y; rewrite* subst_ee_open_te_var;
        apply~ value_regular.
    + apply_fresh* term_fix as y; rewrite* subst_ee_open_ee_var;
        apply~ value_regular.
    + apply_fresh* term_let as y. rewrite* subst_ee_open_ee_var;
                                    apply~ value_regular.
    + econstructor; eauto.
      intros cl clinmap Alphas x Hlen Hdist Afresh xfresh xfreshA.
      destruct cl as [clA clT].
      unfold map_clause_trm_trm in clinmap.
      lets cl2: clinmap.
      apply List.in_map_iff in cl2.
      destruct cl2 as [[cl'A cl'T] [cl'eq cl'in]].
      inversion cl'eq. subst.
      cbn.
      lets* IH: H1 cl'in Alphas x Hlen Hdist.
      cbn in IH.
      instantiate (1:=(L \u \{ Z })) in Afresh.
      rewrite* <- subst_commutes_with_unrelated_opens_te_ee.
      * rewrite* subst_ee_open_ee_var.
        apply* IH.
        intros A AAlpha.
        assert (A \notin L \u \{ Z }); solve [apply* Afresh | eauto].
        apply~ value_regular.
      * apply~ value_regular.
  - induction 1; intros; simpl; auto;
      try match goal with
      | H: term (trm_abs _ _) |- _ => rename H into Hterm
      | H: term (trm_tabs _) |- _ => rename H into Hterm
      end.
    + apply value_abs. inversions Hterm.
      apply_fresh* term_abs as y. rewrite* subst_ee_open_ee_var.
      apply~ value_regular.
    + apply value_tabs; inversions Hterm.
      apply_fresh* term_tabs as Y; rewrite* subst_ee_open_te_var;
        apply~ value_regular.
    + case_if~.
    + inversions H1.
      constructor*.
    + econstructor.
      * econstructor.
        -- apply* value_is_term.
        -- inversion* H.
      * apply* IHvalue.
Qed.

(* Lemma adding_free_is_ok : forall A E F, *)
(*     ok (E & F) -> *)
(*     A # E -> *)
(*     A # F -> *)
(*     ok (E & (withtyp A) & F)%env. *)
(*   induction F using env_ind; introv Hok HE HF. *)
(*   - rewrite concat_empty_r. *)
(*     constructor*. *)
(*   - rewrite concat_assoc. *)
(*     rewrite concat_assoc in Hok. *)
(*     apply ok_push_inv in Hok. *)
(*     econstructor. *)
(*     + apply* IHF. *)
(*     + simpl_dom. *)
(*       rewrite notin_union. *)
(*       rewrite notin_union. *)
(*       split*. *)
(* Qed. *)

(* Lemma adding_free_is_ok_many : forall As E F, *)
(*     ok (E & F) -> *)
(*     DistinctList As -> *)
(*     (forall A, List.In A As -> A \notin dom E) -> *)
(*     (forall A, List.In A As -> A \notin dom F) -> *)
(*     ok (add_types E As & F). *)
(*   induction As as [| Ah Ats]; introv Hok HD HE HF. *)
(*   - cbn. eauto. *)
(*   - cbn. *)
(*     rewrite <- concat_assoc. *)
(*     apply IHAts; eauto with listin. *)
(*     + rewrite concat_assoc. *)
(*       apply adding_free_is_ok; eauto with listin. *)
(*     + inversion* HD. *)
(*     + introv Hin. *)
(*       simpl_dom. *)
(*       rewrite notin_union. *)
(*       split. *)
(*       * apply* notin_singleton. *)
(*         inversions HD. *)
(*         intro; subst. contradiction. *)
(*       * eauto with listin. *)
(* Qed. *)

Lemma subst_idempotent : forall U Z P,
    Z \notin fv_typ P ->
    subst_tt Z P U = subst_tt Z P (subst_tt Z P U).
  induction U using typ_ind'; introv FV; try solve [cbn; eauto].
  - cbn.
    case_if.
    + rewrite* subst_tt_fresh.
    + cbn. case_if. eauto.
  - cbn.
    rewrite* <- IHU1.
    rewrite* <- IHU2.
  - cbn.
    rewrite* <- IHU1.
    rewrite* <- IHU2.
  - cbn.
    rewrite* <- IHU.
  - cbn. f_equal.
    rewrite List.map_map.
    apply* List.map_ext_in.
    introv ain.
    rewrite List.Forall_forall in *.
    eauto.
Qed.

Lemma subst_idempotent_through_many_open : forall Tts Z U P,
    type P ->
    Z \notin fv_typ P ->
    subst_tt Z P (open_tt_many Tts U) =
    subst_tt Z P (open_tt_many Tts (subst_tt Z P U)).
  induction Tts; introv TP FV.
  - cbn. apply* subst_idempotent.
  - cbn.
    rewrite* IHTts.
    rewrite* (IHTts Z (open_tt (subst_tt Z P U) a) P).
    f_equal. f_equal.
    repeat rewrite* subst_tt_open_tt.
    f_equal.
    apply* subst_idempotent.
Qed.

Lemma subst_removes_var : forall T U Z,
    Z \notin fv_typ U ->
    Z \notin fv_typ (subst_tt Z U T).
  induction T using typ_ind'; introv FU; cbn; eauto.
  - case_if; cbn; eauto.
  - rewrite list_fold_map.
    rewrite List.Forall_forall in *.
    apply* notin_fold.
Qed.

Lemma subst_commutes_open_tt_many : forall Ts Z P U,
    type P ->
    Z \notin fv_typ P ->
    Z \notin fv_typ U ->
    subst_tt Z P (open_tt_many Ts U) =
    open_tt_many (List.map (subst_tt Z P) Ts) U.
  induction Ts as [| Th Tts]; introv TP FP FU.
  - cbn. apply* subst_tt_fresh.
  - cbn.
    rewrite* subst_idempotent_through_many_open.
    rewrite* subst_tt_open_tt.
    rewrite* (@subst_tt_fresh Z P U).
    apply* IHTts.
    unfold open_tt.
    lets* FO: fv_open U (subst_tt Z P Th) 0.
    destruct FO as [FO | FO].
    + rewrite FO.
      apply notin_union; split*.
      apply* subst_removes_var.
    + rewrite* FO.
Qed.

(* Lemma add_types_map_subst_tb : forall As Z P, *)
(*     map (subst_tb Z P) (add_types empty As) *)
(*     = *)
(*     add_types empty As. *)
(*   induction As as [| Ah Ats]; introv. *)
(*   - cbn. autorewrite with rew_env_map. trivial. *)
(*   - cbn. autorewrite with rew_env_map. cbn. rewrite IHAts. trivial. *)
(* Qed. *)

(* Lemma add_types_through_map : forall Z P E F As, *)
(*     map (subst_tb Z P) (add_types E As & F) *)
(*     = *)
(*     add_types (map (subst_tb Z P) E) As & (map (subst_tb Z P) F). *)
(*   intros. *)
(*   autorewrite with rew_env_map. *)
(*   f_equal. *)
(*   rewrite <- (concat_empty_r E). *)
(*   rewrite add_types_assoc. *)
(*   autorewrite with rew_env_map. *)
(*   rewrite add_types_assoc. *)
(*   f_equal. *)
(*   apply add_types_map_subst_tb. *)
(* Qed. *)


Fixpoint subst_te_many (Xs : list var) (Us : list typ) (e : trm) :=
  match (Xs, Us) with
  (* | ((List.cons X Xt), (List.cons U Ut)) => subst_tt X U (subst_tt_many Xt Ut T) *)
  | ((List.cons X Xt), (List.cons U Ut)) => subst_te_many Xt Ut (subst_te X U e)
  | _ => e
  end.

Lemma subst_commutes_with_unrelated_opens_te : forall Xs e V Y,
    (forall X, List.In X Xs -> X <> Y) ->
    type V ->
    subst_te Y V (open_te_many_var Xs e) =
    (open_te_many_var Xs (subst_te Y V e)).
  induction Xs as [| Xh Xt]; introv Hneq Htyp.
  - cbn. eauto.
  - cbn.
    fold (open_te_many_var Xt (e open_te_var Xh)).
    fold (open_te_many_var Xt (subst_te Y V e open_te_var Xh)).
    rewrite* subst_te_open_te_var; eauto with listin.
Qed.

Lemma subst_intro_commutes_opens_te : forall Xs e Y V,
    Y \notin fv_trm e ->
    (forall X, List.In X Xs -> X <> Y) ->
    type V ->
    open_te_many_var Xs (open_te e V) =
    subst_te Y V (open_te_many_var Xs (e open_te_var Y)).
  induction Xs as [| Xh Xt]; introv Hfv Hneq Htyp.
  - cbn. apply* subst_te_intro.
  - cbn.
    fold (open_te_many_var Xt (open_te e V open_te_var Xh)).
    fold (open_te_many_var Xt ((e open_te_var Y) open_te_var Xh)).
    rewrite* subst_commutes_with_unrelated_opens_te.
    f_equal.
    rewrite* <- subst_te_open_te_var.
    + rewrite* <- subst_te_intro.
    + apply* Hneq. cbn; eauto.
    + eauto with listin.
Qed.

Lemma subst_te_intro_many : forall Xs e Us,
    length Xs = length Us ->
    DistinctList Xs ->
    (forall X, List.In X Xs -> X \notin fv_trm e) ->
    (forall X U, List.In X Xs -> List.In U Us -> X \notin fv_typ U) ->
    (forall U, List.In U Us -> type U) ->
    open_te_many Us e = subst_te_many Xs Us (open_te_many_var Xs e).
  induction Xs as [| Xh Xt]; introv Hleneq Hdistinct HXfv HXUfv XUtyp.
  - destruct Us.
    + cbv. trivial.
    + inversions Hleneq.
  - destruct Us as [| Uh Ut].
    + inversions Hleneq.
    + cbn.
      fold (open_te_many_var Xt (e open_te_var Xh)).
      inversions Hdistinct.
      rewrite IHXt; auto with listin.
      * f_equal.
        rewrite <- subst_intro_commutes_opens_te; eauto with listin.
        introv Xin.
        intro; subst. contradiction.
      * introv Xin.
        apply fv_open_te; eauto with listin.
Qed.

Lemma subst_tt_many_free : forall As Ts T,
    (forall A, List.In A As -> A \notin fv_typ T) ->
    T = subst_tt_many As Ts T.
  induction As; introv Afresh.
  - cbn. trivial.
  - destruct Ts.
    + cbn. trivial.
    + cbn. rewrite <- IHAs.
      * symmetry. apply subst_tt_fresh.
        auto with listin.
      * intros.
        rewrite subst_tt_fresh;
          auto with listin.
Qed.

Lemma subst_te_many_commutes_open : forall As Ts e x vk,
    length As = length Ts ->
    (forall A, List.In A As -> x <> A) ->
    open_ee (subst_te_many As Ts e) (trm_fvar vk x)
    =
    subst_te_many As Ts (open_ee e (trm_fvar vk x)).
  induction As as [| Ah Ats]; introv Hlen Afresh.
  - cbn. auto.
  - destruct Ts as [| Th Tts]; cbn in Hlen; try congruence.
    cbn. fold (open_ee (subst_te_many Ats Tts (subst_te Ah Th e)) (trm_fvar vk x)).
    rewrite IHAts; auto with listin.
    f_equal.
    apply subst_te_open_ee_var.
Qed.

Lemma subst_tb_id_on_fresh : forall E Z P,
    Z \notin fv_env E ->
    map (subst_tb Z P) E = E.
  induction E using env_ind; introv FE.
  - rewrite map_empty. trivial.
  - rewrite map_push.
    destruct v.
    rewrite fv_env_extend in FE.
    f_equal.
    + apply* IHE.
    + cbn.
      f_equal. f_equal.
      apply subst_tt_fresh. auto.
Qed.

Lemma subst_tt_many_id_on_fresh : forall T As Ps,
    (forall A, List.In A As -> A \notin fv_typ T) ->
    subst_tt_many As Ps T = T.
  induction As; destruct Ps; intros; try solve [cbn in *; congruence].
  cbn.
  rewrite subst_tt_fresh.
  - apply IHAs; auto with listin.
  - auto with listin.
Qed.

Lemma subst_tb_many_id_on_fresh_env : forall E As Ps,
    length As = length Ps ->
    (forall A, List.In A As -> A \notin fv_env E) ->
    map (subst_tb_many As Ps) E = E.
  intros.
  rewrite map_def.
  rewrite <- LibList_map.
  symmetry.
  rewrite <- map_id; auto.
  intros vb xin.
  destruct vb. cbn.
  f_equal; auto.
  unfold subst_tb_many. destruct b.
  rewrite subst_tt_many_id_on_fresh; auto.
  intros.
  induction E as [| B E].
  - contradiction.
  - lets HA: H0 H1.
    cbn in HA. fold (fv_env E) in HA.
    lets [? | ?]: List.in_inv xin; subst; cbn in HA; auto.
    apply IHE; auto.
    intros A' Ain.
    lets HA': H0 Ain.
    destruct B; destruct b; cbn in HA'. fold (fv_env E) in HA'.
    auto.
Qed.

Lemma subst_commute:
  forall (X : var) (U : typ) (A : var) (P T : typ),
    X <> A ->
    A \notin fv_typ U ->
    subst_tt X U (subst_tt A P T) = subst_tt A (subst_tt X U P) (subst_tt X U T).
Proof.
  induction T using typ_ind'; introv Neq Fr; cbn; auto;
    try solve [
          rewrite~ IHT1; rewrite~ IHT2
        ].
  - repeat case_if; subst; cbn; repeat case_if; eauto.
    rewrite~ subst_tt_fresh.
  - rewrite~ IHT.
  - rewrite List.Forall_forall in *.
    f_equal.
    repeat rewrite List.map_map.
    apply List.map_ext_in.
    intros T Tin.
    apply~ H.
Qed.

Lemma subst_ee_fix_term : forall e1 Z e2,
    term e1 -> term e2 -> term (subst_ee Z fix_var e2 e1)
with subst_ee_fix_value : forall e1 Z e2,
    value e1 -> term e2 -> value (subst_ee Z fix_var e2 e1).
Proof.
  - induction 1; intros; simpl; auto.
    + case_if*.
    + apply_fresh* term_abs as y. rewrite* subst_ee_open_ee_var.
    + apply_fresh* term_tabs as Y; rewrite* subst_ee_open_te_var;
        apply~ value_regular.
    + apply_fresh* term_fix as y; rewrite* subst_ee_open_ee_var;
        apply~ value_regular.
    + apply_fresh* term_let as y. rewrite* subst_ee_open_ee_var;
                                    apply~ value_regular.
    + econstructor; eauto.
      intros cl clinmap Alphas x Hlen Hdist Afresh xfresh xfreshA.
      destruct cl as [clA clT].
      unfold map_clause_trm_trm in clinmap.
      lets cl2: clinmap.
      apply List.in_map_iff in cl2.
      destruct cl2 as [[cl'A cl'T] [cl'eq cl'in]].
      inversion cl'eq. subst.
      cbn.
      lets* IH: H1 cl'in Alphas x Hlen Hdist.
      cbn in IH.
      instantiate (1:=(L \u \{ Z })) in Afresh.
      rewrite* <- subst_commutes_with_unrelated_opens_te_ee.
      * rewrite* subst_ee_open_ee_var.
        apply* IH.
        intros A AAlpha.
        assert (A \notin L \u \{ Z }); solve [apply* Afresh | eauto].
  - induction 1; intros; simpl; auto;
      try match goal with
      | H: term (trm_abs _ _) |- _ => rename H into Hterm
      | H: term (trm_tabs _) |- _ => rename H into Hterm
      end.
    + apply value_abs. inversions Hterm.
      apply_fresh* term_abs as y. rewrite* subst_ee_open_ee_var.
    + apply value_tabs; inversions Hterm.
      apply_fresh* term_tabs as Y; rewrite* subst_ee_open_te_var;
        apply~ value_regular.
    + case_if~.
      inversions C.
      congruence.
    + constructor*.
      inversions H1.
      constructor*.
    + inversions H.
      constructor*.
Qed.
