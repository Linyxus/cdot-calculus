(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Require Import Coq.Program.Equality.
Require Import Definitions TightTyping SemanticSubtyping PreciseTyping.
Require Import Replacement Binding Narrowing Subenvironments Weakening.

Ltac inv_repl_typ_rcd :=
  match goal with
  | H : repl_typ _ _ _ (typ_rcd _) |- _ => inversion H; subst; clear H
end.

Ltac inv_repl_typ_rec :=
  match goal with
  | H : repl_typ _ _ _ (typ_bnd _) |- _ => inversion H; subst; clear H
end.

Ltac inv_repl_dec :=
  match goal with
  | H : repl_dec _ _ _ _ |- _ => inversion H; subst; clear H
end.

Ltac inv_repl_typ_rcd_full := inv_repl_typ_rcd; inv_repl_dec.

Ltac inv_repl_typ_all :=
  match goal with
  | H : repl_typ _ _ _ (typ_all _ _) |- _ => inversion H; subst; clear H
end.

Lemma subtyp_sngl_pq1_t : forall G p q S S' T U,
    G ⊢!!! p : {{ q }} ->
    G ⊢!!! q : U ->
    G ⊢# S <: T ->
    repl_typ p q S S' ->
    G ⊢# S' <: T.
Proof.
  introv Hp Hq Hst Hr.
  destruct repl_swap as [repl_swap _].
  apply repl_swap in Hr.
  eauto.
Qed.

Lemma subtyp_sngl_pq2_t : forall G p q S T T' U,
    G ⊢!!! p : {{ q }} ->
    G ⊢!!! q : U ->
    G ⊢# S <: T ->
    repl_typ p q T T' ->
    G ⊢# S <: T'.
Proof.
  introv Hp Hq Hst Hr.
  eapply subtyp_trans_t. apply Hst. eauto.
Qed.

Lemma subtyp_sngl_qp1_t : forall G p q S S' T U,
    G ⊢!!! p : {{ q }} ->
    G ⊢!!! q : U ->
    G ⊢# S <: T ->
    repl_typ q p S S' ->
    G ⊢# S' <: T.
Proof.
  introv Hp Hq Hst Hr.
  destruct repl_swap as [repl_swap _].
  apply repl_swap in Hr.
  eauto.
Qed.

Lemma subtyp_sngl_qp2_t : forall G p q S T T' U,
    G ⊢!!! p : {{ q }} ->
    G ⊢!!! q : U ->
    G ⊢# S <: T ->
    repl_typ q p T T' ->
    G ⊢# S <: T'.
Proof.
  introv Hp Hq Hst Hr.
  eapply subtyp_trans_t. apply Hst. eauto.
Qed.

Lemma invert_subtyp_typ_s : forall G A S1 T1 S2 T2,
    G ⊢{} typ_rcd {A >: S1 <: T1} <: typ_rcd {A >: S2 <: T2} ->
    G ⊢# S2 <: S1 /\ G ⊢# T1 <: T2.
Proof.
  introv Hsub.
  remember (typ_rcd {A >: S1 <: T1}) as typ1 in Hsub.
  remember (typ_rcd {A >: S2 <: T2}) as typ2 in Hsub.
  gen S1 T1 S2 T2.
  induction Hsub; intros; try inversion Heqtyp1; try inversion Heqtyp2.
  - subst T. inversion H0. eauto.
  - subst. eauto.
  - subst. clear H2 H3.
    specialize (IHHsub S1 T1).
    inversion H1; subst.
    inversion H6; subst.
    -- assert (G ⊢# T0 <: S1 /\ G ⊢# T1 <: T2) as Hg.
       {
         apply IHHsub with (S2 := T0) (T3 := T2); trivial.
       }
       destruct Hg as [Hg1 Hg2].
       split; try trivial.
       eapply subtyp_sngl_pq1_t.
       exact H.
       exact H0.
       exact Hg1.
       exact H7.
    -- assert (G ⊢# S2 <: S1 /\ G ⊢# T1 <: T0) as Hg.
       {
         apply IHHsub with (S3 := S2) (T2 := T0); trivial.
       }
       destruct Hg as [Hg1 Hg2].
       split; auto.
       eauto.
  - subst. clear H2 H3.
    specialize (IHHsub S1 T1).
    inversion H1; subst. inversion H6; subst; clear H6.
    -- assert (G ⊢# T0 <: S1 /\ G ⊢# T1 <: T2) as [Hg1 Hg2].
       {
         apply IHHsub with (S2 := T0) (T3 := T2); trivial.
       }
       split; auto.
       eapply subtyp_sngl_qp1_t.
       exact H. exact H0. exact Hg1. exact H7.
    -- assert (G ⊢# S2 <: S1 /\ G ⊢# T1 <: T0) as [Hg1 Hg2].
       {
         apply IHHsub with (S3 := S2) (T2 := T0); trivial.
       }
       split; auto.
       eauto.
  - subst. clear H2 H3.
    inversion H1; subst. inversion H6; subst; clear H6.
    -- assert (G ⊢# S2 <: T0 /\ G ⊢# T1 <: T2) as [Hg1 Hg2].
       {
         apply IHHsub with (S1 := T0) (T3 := T1) (S3 := S2) (T4 := T2); trivial.
       }
       split; auto.
       destruct repl_swap as [Hs _]. apply Hs in H7.
       eauto.
     -- assert (G ⊢# S2 <: S1 /\ G ⊢# T0 <: T2) as [Hg1 Hg2].
        {
          apply IHHsub with (S3 := S1) (T1 := T0) (S4 := S2) (T3 := T2); trivial.
        }
        split; auto. destruct repl_swap as [Hs _]. eauto.
  - subst; clear H2 H3.
    inversion H1; subst. inversion H6; subst; clear H6.
    -- assert (G ⊢# S2 <: T0 /\ G ⊢# T1 <: T2) as [Hg1 Hg2].
       {
         apply IHHsub with (S1 := T0) (T3 := T1) (S3 := S2) (T4 := T2); trivial.
       }
       split; auto.
       destruct repl_swap as [Hs _]. apply Hs in H7.
       eauto.
     -- assert (G ⊢# S2 <: S1 /\ G ⊢# T0 <: T2) as [Hg1 Hg2].
        {
          apply IHHsub with (S3 := S1) (T1 := T0) (S4 := S2) (T3 := T2); trivial.
        }
        split; auto. destruct repl_swap as [Hs _]. eauto.
Qed.

Lemma invert_subtyp_trm_s : forall G a T1 T2,
    G ⊢{} typ_rcd {a ⦂ T1} <: typ_rcd {a ⦂ T2} ->
    G ⊢{} T1 <: T2.
Proof.
  introv Hsub.
  remember (typ_rcd {a ⦂ T1}) as typ1 in Hsub.
  remember (typ_rcd {a ⦂ T2}) as typ2 in Hsub.
  gen T1 T2.
  induction Hsub; introv Heq1; introv Heq2;
    inversion Heq1;
    inversion Heq2;
    subst; eauto;
    try (subst T; inversion Heq2); eauto;
    try (inversion Heq2; subst; eauto);
    try (inv_repl_typ_rcd_full; eauto).
Qed.

Lemma invert_subtyp_all_s : forall G S1 T1 S2 T2,
    inert G ->
    G ⊢{} ∀(S1) T1 <: ∀(S2) T2 ->
    G ⊢# S2 <: S1 /\ (exists L, forall x, x \notin L ->
       G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2).
Proof.
  introv H0 Hsub.
  match goal with
  | H : G ⊢{} ?S <: ?T |- _ => remember S as typ1; remember T as typ2
  end.
  gen S1 S2 T1 T2.
  induction Hsub; introv Heq1; introv Heq2;
    try inversion Heq1;
    try inversion Heq2;
    subst; auto.
  - inversion Heq2; subst. split; try constructor.
    exists (\{} : fset var). eauto.
  - inv_repl_typ_all.
    -- split.
       apply subtyp_sngl_pq1_t with (p := p) (q := q) (S := T0) (U := U); auto.
       apply* IHHsub. specialize (IHHsub H0 S1 T0 T1 eq_refl T2 eq_refl) as [_ IH].
       destruct IH as [L IH]. exists (L \u dom G). introv Hn.
       apply* narrow_subtyping. eapply subenv_push.
       + eauto.
       + eauto.
       + eauto.
       + apply subtyp_trans with (T := T0); try constructor.
         eapply subtyp_sngl_qp. apply* precise_to_general3.
         apply* precise_to_general3. apply* repl_swap.
    -- split.
       apply* IHHsub. specialize (IHHsub H0 _ _ _ eq_refl _ eq_refl) as [_ [L IH]].
       repeat (
         match goal with
         | H : G ⊢!!! _ : _ |- _ => apply precise_to_general3 in H
         end
       ).
       exists (L \u dom G). introv Hn. eapply subtyp_trans.
       + apply* IH.
       + eapply subtyp_sngl_pq; try apply* weaken_ty_trm.
         apply* repl_open_var; apply* typed_paths_named.
  - inv_repl_typ_all.
    -- split.
       apply subtyp_sngl_qp1_t with (p := p) (q := q) (S := T0) (U := U); auto.
       apply* IHHsub. specialize (IHHsub H0 S1 T0 T1 eq_refl T2 eq_refl) as [_ IH].
       destruct IH as [L IH]. exists (L \u dom G). introv Hn.
       apply* narrow_subtyping. eapply subenv_push.
       + eauto.
       + eauto.
       + eauto.
       + apply subtyp_trans with (T := T0); try constructor.
         eapply subtyp_sngl_pq. apply* precise_to_general3.
         apply* precise_to_general3. apply* repl_swap.
    -- split.
       apply* IHHsub. specialize (IHHsub H0 _ _ _ eq_refl _ eq_refl) as [_ [L IH]].
       repeat (
         match goal with
         | H : G ⊢!!! _ : _ |- _ => apply precise_to_general3 in H
         end
       ).
       exists (L \u dom G). introv Hn. eapply subtyp_trans.
       + apply* IH.
       + eapply subtyp_sngl_qp; try apply* weaken_ty_trm.
         apply* repl_open_var; apply* typed_paths_named.
  - inv_repl_typ_all.
    -- specialize (IHHsub H0 _ _ _ eq_refl _ eq_refl).
       split.
       apply subtyp_sngl_pq2_t with (p := p) (T := T0) (q := q) (U := U); auto.
       apply* IHHsub.
       destruct IHHsub as [_ [L IH]]. exists (L \u dom G). introv Hn.
       apply* IH.
    -- specialize (IHHsub H0 _ _ _ eq_refl _ eq_refl).
       split. apply* IHHsub. destruct IHHsub as [_ [L IH]].
       exists (L \u dom G). introv Hn.
       repeat (
         match goal with
         | H : G ⊢!!! _ : _ |- _ => apply precise_to_general3 in H
         end
       ).
       apply subtyp_trans with (T := open_typ x T0).
       + eapply subtyp_sngl_qp; try apply* weaken_ty_trm.
         apply* repl_open_var; try apply* typed_paths_named. apply* repl_swap.
       + apply* IH.
  - inv_repl_typ_all.
    -- specialize (IHHsub H0 _ _ _ eq_refl _ eq_refl).
       split.
       apply subtyp_sngl_qp2_t with (p := p) (T := T0) (q := q) (U := U); auto.
       apply* IHHsub.
       destruct IHHsub as [_ [L IH]]. exists (L \u dom G). introv Hn.
       apply* IH.
    -- specialize (IHHsub H0 _ _ _ eq_refl _ eq_refl).
       split. apply* IHHsub. destruct IHHsub as [_ [L IH]].
       exists (L \u dom G). introv Hn.
       repeat (
         match goal with
         | H : G ⊢!!! _ : _ |- _ => apply precise_to_general3 in H
         end
       ).
       apply subtyp_trans with (T := open_typ x T0).
       + eapply subtyp_sngl_pq; try apply* weaken_ty_trm.
         apply* repl_open_var; try apply* typed_paths_named. apply* repl_swap.
       + apply* IH.
  - split; eauto.
Qed.

Lemma invert_subtyp_all_t : forall G S1 T1 S2 T2,
    inert G ->
    G ⊢# ∀(S1) T1 <: ∀(S2) T2 ->
    G ⊢# S2 <: S1 /\ (exists L, forall x, x \notin L ->
       G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2).
Proof.
  introv H0 Hsub. apply* invert_subtyp_all_s. apply* tight_to_semantic.
Qed.

Lemma invert_subtyp_typ_s_label : forall G A1 S1 T1 A2 S2 T2,
    G ⊢{} typ_rcd {A1 >: S1 <: T1} <: typ_rcd {A2 >: S2 <: T2} ->
    A1 = A2.
Proof.
  introv Hs.
  remember (typ_rcd {A1 >: S1 <: T1}) as typ1 in Hs.
  remember (typ_rcd {A2 >: S2 <: T2}) as typ2 in Hs.
  rename Heqtyp1 into Heq1.
  rename Heqtyp2 into Heq2.
  gen S1 T1 S2 T2.
  induction Hs; intros.
  - (* top *)
    subst. inversion Heq2.
  - (* bot *)
    inversion Heq1.
  - (* refl *)
    subst. inversion Heq2. trivial.
  - (* and11 *)
    inversion Heq1.
  - (* and12 *)
    inversion Heq1.
  - (* and2 *)
    inversion Heq2.
  - (* fld *)
    inversion Heq1.
  - (* typ *)
    inversion Heq1. inversion Heq2. subst. trivial.
  - (* sngl_pq2 *)
    specialize (IHHs _ _ Heq1).
    subst T'. inversion H1; subst. inversion H6; subst.
    -- specialize (IHHs T0 T2). auto.
    -- specialize (IHHs S2 T0). auto.
  - (* sngl_qp2 *)
    specialize (IHHs _ _ Heq1). subst T'.
    inversion H1; subst. inversion H6; subst.
    -- specialize (IHHs T0 T2). auto.
    -- specialize (IHHs S2 T0). auto.
  - (* sngl_pq1 *)
    subst S'. inversion H1; subst. inversion H6; subst; apply* IHHs.
  - (* sngl_qp1 *)
    subst S'. inversion H1; subst. inversion H6; subst; apply* IHHs.
  - (* sel2 *)
    inversion Heq2.
  - (* sel1 *)
    inversion Heq1.
  - (* all *)
    inversion Heq1.
Qed.

Theorem invert_subtyp_typ_t : forall G A S1 T1 S2 T2,
    inert G ->
    G ⊢# typ_rcd {A >: S1 <: T1} <: typ_rcd {A >: S2 <: T2} ->
    G ⊢# S2 <: S1 /\ G ⊢# T1 <: T2.
Proof.
  introv Hi Hs.
  eapply invert_subtyp_typ_s.
  apply tight_to_semantic; eauto.
Qed.

(** * Unique typing *)

Lemma invert_subtyp_and2_s : forall G S T U,
    G ⊢{} S <: typ_and T U ->
    G ⊢{} S <: T /\ G ⊢{} S <: U.
Proof.
  introv H.
  remember (typ_and T U) as and1 in H. rename Heqand1 into He.
  gen T U.
  induction H; introv He.
  - (* top *)
    inversion He.
  - (* bot *)
    auto.
  - (* refl *)
    subst T. eauto.
  - (* and11 *)
    specialize (IHsubtyp_s _ _ He). destruct IHsubtyp_s as [IH1 IH2].
    eauto.
  - (* and12 *)
    specialize (IHsubtyp_s _ _ He). destruct IHsubtyp_s as [IH1 IH2].
    eauto.
  - (* and2 *)
    inversion He; subst. eauto.
  - (* fld *)
    inversion He.
  - (* typ *)
    inversion He.
  - (* sngl_pq2 *)
    subst T'. inversion H1; subst.
    -- specialize (IHsubtyp_s T1 U0).
       assert (G ⊢{} S <: T1 /\ G ⊢{} S <: U0) as [Hg1 Hg2].
       {
         apply IHsubtyp_s. auto.
       }
       split; auto. eauto.
    -- specialize (IHsubtyp_s T0 T1).
       assert (G ⊢{} S <: T0 /\ G ⊢{} S <: T1) as [Hg1 Hg2].
       {
         apply IHsubtyp_s. auto.
       }
       split; auto. eauto.
  - (* sngl_qp2 *)
    subst T'. inversion H1; subst.
    -- specialize (IHsubtyp_s T1 U0).
       assert (G ⊢{} S <: T1 /\ G ⊢{} S <: U0) as [Hg1 Hg2].
       {
         apply IHsubtyp_s. auto.
       }
       split; auto. eauto.
    -- specialize (IHsubtyp_s T0 T1).
       assert (G ⊢{} S <: T0 /\ G ⊢{} S <: T1) as [Hg1 Hg2].
       {
         apply IHsubtyp_s. auto.
       }
       split; auto. eauto.
  - (* sngl_qp1 *)
    specialize (IHsubtyp_s _ _ He) as [Hg1 Hg2].
    eauto.
  - (* sngl_pq1 *)
    specialize (IHsubtyp_s _ _ He) as [Hg1 Hg2].
    eauto.
  - (* sel2 *)
    inversion He.
  - (* sel1 *)
    specialize (IHsubtyp_s _ _ He) as [Hg1 Hg2]. eauto.
  - (* all *)
    inversion He.
Qed.

Lemma reduce_subtyp_rcd2_s : forall G U1 U2 A S T,
    G ⊢{} U1 <: U2 ->
    U2 ↘ typ_rcd {A >: S <: T} ->
    G ⊢{} U1 <: typ_rcd {A >: S <: T}.
Proof.
  introv Hs [ls Hu].
  remember (typ_rcd {A >: S <: T}) as typ.
  induction Hu.
  - (* typ *)
    inversion Heqtyp; subst; clear Heqtyp. auto.
  - (* fld *)
    inversion Heqtyp.
  - (* rec *)
    inversion Heqtyp.
  - (* andl *)
    apply invert_subtyp_and2_s in Hs as [Hs1 Hs2].
    eauto.
  - (* andr *)
    apply invert_subtyp_and2_s in Hs as [Hs1 Hs2].
    eauto.
Qed.

Lemma rcd_with_unique_typ_in_label : forall U L A S T,
    rcd_with_unique_typ U L (typ_rcd {A >: S <: T}) ->
    A \in L.
Proof.
  introv H.
  remember (typ_rcd (dec_typ A S T)) as T1.
  induction H.
  - (* typ *) inversion HeqT1. subst. apply in_singleton_self.
  - (* fld *) inversion HeqT1.
  - inversion HeqT1.
  - (* andl *)
    specialize (IHrcd_with_unique_typ1 HeqT1).
    rewrite in_union. left. auto.
  - (* andr *)
    specialize (IHrcd_with_unique_typ2 HeqT1).
    rewrite in_union. right. auto.
Qed.

Lemma subtyp_s_trm_typ_false : forall G a U A S T,
    ~ G ⊢{} typ_rcd {a ⦂ U} <: typ_rcd {A >: S <: T}.
Proof.
  introv Hn.
  remember (typ_rcd {a ⦂ U}) as trm1.
  remember (typ_rcd {A >: S <: T}) as typ2.
  rename Heqtrm1 into Heq1. rename Heqtyp2 into Heq2.
  gen U S T.
  induction Hn; intros.
  - (* top *)
    inversion Heq2.
  - (* bot *)
    inversion Heq1.
  - (* refl *)
    subst. inversion Heq2.
  - (* and11 *)
    inversion Heq1.
  - (* and12 *)
    inversion Heq1.
  - (* and2 *)
    inversion Heq2.
  - (* fld *)
    inversion Heq2.
  - (* typ *)
    inversion Heq1.
  - (* sngl_pq2 *)
    subst. inversion H1; subst. inversion H6; subst; apply* IHHn.
  - (* sngl_qp2 *)
    subst. inversion H1; subst. inversion H6; subst; apply* IHHn.
  - (* sngl_pq1 *)
    subst S'. inversion H1; subst. inversion H6; subst.
    apply* IHHn.
  - (* sngl_qp1 *)
    subst S'. inversion H1; subst. inversion H6; subst.
    apply* IHHn.
  - (* sel2 *)
    inversion Heq2.
  - (* sel1 *)
    inversion Heq1.
  - (* all *)
    inversion Heq1.
Qed.

Lemma subtyp_s_rec_typ_false : forall G U A S T,
    ~ G ⊢{} μ U <: typ_rcd {A >: S <: T}.
Proof.
  introv Hs. remember (μ U) as t1. remember (typ_rcd {A >: S <: T}) as t2.
  gen U S T.
  induction Hs; introv Heq1; introv Heq2;
    try inversion Heq1;
    try inversion Heq2.
  - subst T. inversion Heq2.
  - subst; inv_repl_typ_rcd_full; apply* IHHs.
  - subst; inv_repl_typ_rcd_full; apply* IHHs.
  - subst. inv_repl_typ_rec. apply* IHHs.
  - subst. inv_repl_typ_rec. apply* IHHs.
Qed.

Lemma invert_subtyp_and1_s_rcd : forall G U1 U2 D,
    G ⊢{} typ_and U1 U2 <: typ_rcd D ->
    G ⊢{} U1 <: typ_rcd D \/ G ⊢{} U2 <: typ_rcd D.
Proof.
  introv Hs.
  remember (typ_and U1 U2) as and1 in Hs.
  remember (typ_rcd D) as rcd2 in Hs.
  rename Heqand1 into He1. rename Heqrcd2 into He2.
  gen U1 U2 D.
  induction Hs; intros.
  - (* top *)
    inversion He2.
  - (* bot *)
    inversion He1.
  - (* refl *)
    subst T. inversion He2.
  - (* and11 *)
    inversion He1. subst. left; auto.
  - (* and12 *)
    inversion He2. subst. inversion He1. subst.
    right. auto.
  - (* and2 *)
    inversion He2.
  - (* fld *)
    inversion He1.
  - (* typ *)
    inversion He1.
  - (* sngl_pq2 *)
    subst T'. inversion H1; subst.
    assert (typ_and U1 U2 = typ_and U1 U2) as Heq1. trivial.
    assert (typ_rcd D1 = typ_rcd D1) as Heq2. trivial.
    specialize (IHHs _ _ Heq1 _ Heq2) as [IH1 | IH2].
    -- left. eauto.
    -- right. eauto.
  - (* sngl_qp2 *)
    subst T'. inversion H1; subst.
    assert (typ_and U1 U2 = typ_and U1 U2) as Heq1. trivial.
    assert (typ_rcd D1 = typ_rcd D1) as Heq2. trivial.
    specialize (IHHs _ _ Heq1 _ Heq2) as [IH1 | IH2].
    -- left. eauto.
    -- right. eauto.
  - (* sngl_pq1 *)
    subst S'. inversion H1; subst.
    -- assert (typ_and T1 U2 = typ_and T1 U2) as Heq1. trivial.
       assert (typ_rcd D = typ_rcd D) as Heq2. trivial.
       specialize (IHHs _ _ Heq1 _ Heq2) as [IH1 | IH2].
       + left. eauto.
       + right. eauto.
    -- assert (typ_and U1 T1 = typ_and U1 T1) as Heq1. trivial.
       assert (typ_rcd D = typ_rcd D) as Heq2. trivial.
       specialize (IHHs _ _ Heq1 _ Heq2) as [IH1 | IH2].
       + left. eauto.
       + right. eauto.
  - (* sngl_qp1 *)
    subst S'. inversion H1; subst.
    -- assert (typ_and T1 U2 = typ_and T1 U2) as Heq1. trivial.
       assert (typ_rcd D = typ_rcd D) as Heq2. trivial.
       specialize (IHHs _ _ Heq1 _ Heq2) as [IH1 | IH2].
       + left. eauto.
       + right. eauto.
    -- assert (typ_and U1 T1 = typ_and U1 T1) as Heq1. trivial.
       assert (typ_rcd D = typ_rcd D) as Heq2. trivial.
       specialize (IHHs _ _ Heq1 _ Heq2) as [IH1 | IH2].
       + left. eauto.
       + right. eauto.
  - (* sel2 *)
    inversion He2.
  - (* sel1 *)
    inversion He1.
  - (* all *)
    inversion He1.
Qed.

Lemma rcd_with_unique_typ_notin_labels : forall G U L T1 A S T,
    rcd_with_unique_typ U L T1 ->
    A \notin L ->
    ~ G ⊢{} U <: typ_rcd (dec_typ A S T).
Proof.
  intros G U L T1 A S T H1 Hn Ha.
  induction H1.
  - (* typ *)
    rewrite -> notin_singleton in Hn.
    apply invert_subtyp_typ_s_label in Ha.
    subst A0. apply Hn. trivial.
  - (* fld *)
    eapply subtyp_s_trm_typ_false. apply Ha.
  - apply* subtyp_s_rec_typ_false.
  - (* andl *)
    apply notin_union in Hn. destruct Hn as [Hn1 Hn2].
    apply invert_subtyp_and1_s_rcd in Ha.
    destruct Ha.
    -- specialize (IHrcd_with_unique_typ1 Hn1 H0). contradiction.
    -- specialize (IHrcd_with_unique_typ2 Hn2 H0). contradiction.
  - (* andl *)
    apply notin_union in Hn. destruct Hn as [Hn1 Hn2].
    apply invert_subtyp_and1_s_rcd in Ha.
    destruct Ha.
    -- specialize (IHrcd_with_unique_typ1 Hn1 H0). contradiction.
    -- specialize (IHrcd_with_unique_typ2 Hn2 H0). contradiction.
Qed.

Lemma reduce_subtyp_rcd1_s : forall G U1 A S1 T1 S2 T2,
    G ⊢{} U1 <: typ_rcd {A >: S2 <: T2} ->
    U1 ↘ typ_rcd {A >: S1 <: T1} ->
    G ⊢{} typ_rcd {A >: S1 <: T1} <: typ_rcd {A >: S2 <: T2}.
Proof.
  introv Hs [ls Hu].
  remember (typ_rcd {A >: S1 <: T1}) as typ1 in Hu.
  rename Heqtyp1 into He.
  induction Hu.
  - (* typ *)
    inversion He; subst. auto.
  - (* fld *)
    inversion He.
  - inversion He.
  - (* andl *)
    apply invert_subtyp_and1_s_rcd in Hs as [Hs | Hs].
    -- auto.
    -- subst T0.
       apply rcd_with_unique_typ_in_label in Hu1.
       pose proof (disjoint_in_notin H Hu1) as Hni.
       contradict Hs. eapply rcd_with_unique_typ_notin_labels.
       apply Hu2. apply Hni.
  - (* andr *)
    apply invert_subtyp_and1_s_rcd in Hs as [Hs | Hs].
    -- subst.
       apply rcd_with_unique_typ_in_label in Hu2.
       apply disjoint_comm in H.
       pose proof (disjoint_in_notin H Hu2) as Hni.
       contradict Hs. eapply rcd_with_unique_typ_notin_labels.
       apply Hu1. apply Hni.
    -- auto.
Qed.

Lemma reduce_subtyp_rcd_both_s : forall G U1 U2 A S1 T1 S2 T2,
    U1 ↘ typ_rcd {A >: S1 <: T1} ->
    U2 ↘ typ_rcd {A >: S2 <: T2} ->
    G ⊢{} U1 <: U2 ->
    G ⊢{} typ_rcd {A >: S1 <: T1} <: typ_rcd {A >: S2 <: T2}.
Proof.
  introv Hu1 Hu2 Hsub.
  pose proof (reduce_subtyp_rcd2_s _ _ _ _ _ _ Hsub Hu2) as H1.
  pose proof (reduce_subtyp_rcd1_s _ _ _ _ _ _ _ H1 Hu1) as H2.
  auto.
Qed.

Lemma invert_subtyp_rcd_s : forall G U1 U2 A S1 T1 S2 T2,
    U1 ↘ typ_rcd {A >: S1 <: T1} ->
    U2 ↘ typ_rcd {A >: S2 <: T2} ->
    G ⊢{} U1 <: U2 ->
    G ⊢# S2 <: S1 /\ G ⊢# T1 <: T2.
Proof.
  introv Hu1 Hu2 Hsub.
  pose proof (reduce_subtyp_rcd_both_s _ _ _ _ _ _ _ _ Hu1 Hu2 Hsub).
  pose proof (invert_subtyp_typ_s _ _ _ _ _ _ H). auto.
Qed.

Lemma invert_subtyp_rcd_t : forall G U1 U2 A S1 T1 S2 T2,
    inert G ->
    U1 ↘ typ_rcd {A >: S1 <: T1} ->
    U2 ↘ typ_rcd {A >: S2 <: T2} ->
    G ⊢# U1 <: U2 ->
    G ⊢# S2 <: S1 /\ G ⊢# T1 <: T2.
Proof.
  introv Hi Hu1 Hu2 Hsub.
  apply* invert_subtyp_rcd_s.
  apply* tight_to_semantic.
Qed.

Lemma subst_typ_rcd_with_unique_typ : forall x p U L T,
    rcd_with_unique_typ U L T ->
    rcd_with_unique_typ (subst_typ x p U) L (subst_typ x p T).
Proof.
  introv Hu. induction Hu; simpl; eauto.
Qed.

Lemma subst_typ_rcd_has_unique_typ : forall x p U T,
    U ↘ T ->
    subst_typ x p U ↘ subst_typ x p T.
Proof.
  introv [ls H]. exists ls.
  apply* subst_typ_rcd_with_unique_typ.
Qed.

  (* - (* typ *) *)
  (* - (* fld *) *)
  (* - (* andl *) *)
  (* - (* andr *) *)

Lemma open_typ_p_fv :
  (forall T p i,
    fv_typ (open_rec_typ_p i p T) = fv_typ T
  \/ fv_typ (open_rec_typ_p i p T) = fv_path p \u fv_typ T) /\
  (forall D p i,
    fv_dec (open_rec_dec_p i p D) = fv_dec D
  \/ fv_dec (open_rec_dec_p i p D) = fv_path p \u fv_dec D).
Proof.
  apply typ_mutind; intros; subst; simpl in *; eauto.
  - specialize (H p i). specialize (H0 p i).
    destruct H; destruct H0; rewrite H; rewrite H0;
      eauto using union_assoc, union_comm, union_comm_assoc, union_empty_r.
    rewrite union_comm_assoc. rewrite union_assoc. rewrite union_assoc. rewrite union_same.
    eauto using union_assoc.
  - destruct p; simpl. destruct p0; simpl.
    destruct a; simpl; repeat cases_if; simpl;
      repeat rewrite union_same; repeat rewrite union_empty_l; repeat rewrite union_empty_r; eauto using union_comm.
  - specialize (H p i). specialize (H0 p (S i)).
    destruct H; destruct H0; rewrite H; rewrite H0;
      eauto using union_assoc, union_comm, union_comm_assoc, union_empty_r.
    rewrite union_comm_assoc. rewrite union_assoc. rewrite union_assoc. rewrite union_same.
    eauto using union_assoc.
  - destruct p; simpl. destruct p0; simpl.
    destruct a; simpl; repeat cases_if; simpl;
      repeat rewrite union_same; repeat rewrite union_empty_l; repeat rewrite union_empty_r; eauto using union_comm.
  - specialize (H p i). specialize (H0 p i).
    destruct H; destruct H0; rewrite H; rewrite H0;
      eauto using union_assoc, union_comm, union_comm_assoc, union_empty_r.
    rewrite union_comm_assoc. rewrite union_assoc. rewrite union_assoc. rewrite union_same.
    eauto using union_assoc.
Qed.

Lemma open_trm_p_fv :
  (forall t p i,
      fv_trm (open_rec_trm_p i p t) = fv_trm t
    \/ fv_trm (open_rec_trm_p i p t) = fv_path p \u fv_trm t) /\
  (forall v p i,
      fv_val (open_rec_val_p i p v) = fv_val v
    \/ fv_val (open_rec_val_p i p v) = fv_path p \u fv_val v) /\
  (forall d p i,
      fv_def (open_rec_def_p i p d) = fv_def d
    \/ fv_def (open_rec_def_p i p d) = fv_path p \u fv_def d) /\
  (forall ds p i,
      fv_defs (open_rec_defs_p i p ds) = fv_defs ds
    \/ fv_defs (open_rec_defs_p i p ds) = fv_path p \u fv_defs ds) /\
  (forall d p i,
      fv_defrhs (open_rec_defrhs_p i p d) = fv_defrhs d
    \/ fv_defrhs (open_rec_defrhs_p i p d) = fv_path p \u fv_defrhs d).
Proof.
  apply trm_mutind;
    intros; subst; simpl in *; eauto.
  - destruct p; simpl. destruct p1; simpl. destruct a; simpl;
    repeat cases_if; simpl; destruct p0; simpl; destruct a; simpl;
      repeat cases_if; simpl; destruct a0; simpl;
      repeat rewrite union_same; repeat rewrite union_empty_l; repeat rewrite union_empty_r; eauto using union_comm.
  - specialize (H p i). specialize (H0 p (S i)).
    destruct H; destruct H0; rewrite H; rewrite H0;
      eauto using union_assoc, union_comm, union_comm_assoc, union_empty_r.
    rewrite union_comm_assoc. rewrite union_assoc. rewrite union_assoc. rewrite union_same.
    eauto using union_assoc.
  - destruct p; simpl. destruct p0; simpl.
    destruct a; simpl;
      repeat cases_if; simpl;
      repeat rewrite union_same; repeat rewrite union_empty_l; repeat rewrite union_empty_r;
      eauto using union_comm.
  - destruct open_typ_p_fv as [HTv _].
    specialize (HTv t p (S i)) as H0.
    specialize (H p (S i)).
    destruct H; destruct H0; rewrite H; rewrite H0;
      eauto using union_assoc, union_comm, union_comm_assoc, union_empty_r.
    rewrite union_comm_assoc. rewrite union_assoc. rewrite union_assoc. rewrite union_same.
    eauto using union_assoc.
  - destruct open_typ_p_fv as [HTv _].
    specialize (HTv t p i) as H0.
    specialize (H p (S i)).
    destruct H; destruct H0; rewrite H; rewrite H0;
      eauto using union_assoc, union_comm, union_comm_assoc, union_empty_r.
    rewrite union_comm_assoc. rewrite union_assoc. rewrite union_assoc. rewrite union_same.
    eauto using union_assoc.
  - destruct open_typ_p_fv as [HTv _].
    specialize (HTv t0 p i) as H0. exact H0.
  - specialize (H p i). specialize (H0 p i).
    destruct H; destruct H0; rewrite H; rewrite H0;
      eauto using union_assoc, union_comm, union_comm_assoc, union_empty_r.
    rewrite union_comm_assoc. rewrite union_assoc. rewrite union_assoc. rewrite union_same.
    eauto using union_assoc.
  - destruct p; simpl; destruct p0; simpl.
    destruct a; simpl;
      repeat cases_if; simpl;
      repeat rewrite union_same; repeat rewrite union_empty_l; repeat rewrite union_empty_r;
      eauto using union_comm.
Qed.

Lemma open_typ_fv :
  (forall T z i,
    fv_typ (open_rec_typ i z T) = fv_typ T
  \/ fv_typ (open_rec_typ i z T) = \{z} \u fv_typ T) /\
  (forall D z i,
    fv_dec (open_rec_dec i z D) = fv_dec D
  \/ fv_dec (open_rec_dec i z D) = \{z} \u fv_dec D).
Proof.
  apply typ_mutind; intros; subst; simpl in *; eauto.
  - specialize (H z i). specialize (H0 z i).
    destruct H; destruct H0; rewrite H; rewrite H0;
      eauto using union_assoc, union_comm, union_comm_assoc, union_empty_r.
    rewrite union_comm_assoc. rewrite union_assoc. rewrite union_assoc. rewrite union_same.
    eauto using union_assoc.
  - destruct p; simpl. destruct a; simpl; repeat cases_if; simpl;
      eauto using union_assoc, union_comm, union_comm_assoc, union_empty_r.
  - specialize (H z i). specialize (H0 z (S i)).
    destruct H; destruct H0; rewrite H; rewrite H0;
      eauto using union_assoc, union_comm, union_comm_assoc, union_empty_r.
    rewrite union_comm_assoc. rewrite union_assoc. rewrite union_assoc. rewrite union_same.
    eauto using union_assoc.
  - destruct p; simpl. destruct a; simpl; repeat cases_if; simpl;
      eauto using union_assoc, union_comm, union_comm_assoc, union_empty_r.
  - specialize (H z i). specialize (H0 z i).
    destruct H; destruct H0; rewrite H; rewrite H0;
      eauto using union_assoc, union_comm, union_comm_assoc, union_empty_r.
    rewrite union_comm_assoc. rewrite union_assoc. rewrite union_assoc. rewrite union_same.
    eauto using union_assoc.
Qed.

Lemma open_trm_fv :
  (forall t z i,
      fv_trm (open_rec_trm i z t) = fv_trm t
    \/ fv_trm (open_rec_trm i z t) = \{z} \u fv_trm t) /\
  (forall v z i,
      fv_val (open_rec_val i z v) = fv_val v
    \/ fv_val (open_rec_val i z v) = \{z} \u fv_val v) /\
  (forall d z i,
      fv_def (open_rec_def i z d) = fv_def d
    \/ fv_def (open_rec_def i z d) = \{z} \u fv_def d) /\
  (forall ds z i,
      fv_defs (open_rec_defs i z ds) = fv_defs ds
    \/ fv_defs (open_rec_defs i z ds) = \{z} \u fv_defs ds) /\
  (forall d z i,
      fv_defrhs (open_rec_defrhs i z d) = fv_defrhs d
    \/ fv_defrhs (open_rec_defrhs i z d) = \{z} \u fv_defrhs d).
Proof.
  apply trm_mutind;
    intros; subst; simpl in *; eauto.
  - unfold open_rec_path. destruct p. simpl. destruct p0. simpl.
    unfold open_rec_avar. destruct a; destruct a0; simpl; repeat cases_if; simpl;
      repeat rewrite union_same; repeat rewrite union_empty_l; repeat rewrite union_empty_r; eauto using union_comm.
  - specialize (H z i). specialize (H0 z (S i)).
    destruct H; destruct H0; subst; simpl; rewrite H; rewrite H0;
      eauto using union_comm, union_assoc, union_comm_assoc, union_same.
    right. rewrite union_comm_assoc. rewrite union_assoc. rewrite union_assoc. rewrite union_same.
    eauto using union_assoc.
  - unfold open_rec_path. destruct p; simpl.
    unfold open_rec_avar. destruct a; simpl; repeat cases_if; simpl.
      repeat rewrite union_same; repeat rewrite union_empty_l; repeat rewrite union_empty_r; eauto using union_comm.
      left. eauto. left. eauto.
  - destruct open_typ_fv as [H0 _]. specialize (H0 t z (S i)).
    specialize (H z (S i)).
    destruct H; destruct H0; subst; simpl; rewrite H; rewrite H0;
      eauto using union_comm, union_assoc, union_comm_assoc, union_same.
    right. rewrite union_comm_assoc. rewrite union_assoc. rewrite union_assoc. rewrite union_same.
    eauto using union_assoc.
  - destruct open_typ_fv as [H0 _]. specialize (H0 t z i).
    specialize (H z (S i)).
    destruct H; destruct H0; subst; simpl; rewrite H; rewrite H0;
      eauto using union_comm, union_assoc, union_comm_assoc, union_same.
    right. rewrite union_comm_assoc. rewrite union_assoc. rewrite union_assoc. rewrite union_same.
    eauto using union_assoc.
  - destruct open_typ_fv as [H0 _]. specialize (H0 t0 z i). exact H0.
  - specialize (H z i). specialize (H0 z i).
    destruct H; destruct H0; subst; simpl; rewrite H; rewrite H0;
      eauto using union_comm, union_assoc, union_comm_assoc, union_same.
    right. rewrite union_comm_assoc. rewrite union_assoc. rewrite union_assoc. rewrite union_same.
    eauto using union_assoc.
  - destruct p; simpl. destruct a; simpl; repeat cases_if; simpl;
      repeat rewrite union_same; repeat rewrite union_empty_l; repeat rewrite union_empty_r; eauto using union_comm.
Qed.

(** * Trivial types *)

Inductive trivial_dec : dec -> Prop :=
| td_typ_refl : forall A T, trivial_dec { A >: T <: T }
| td_typ_bot : forall A T, trivial_dec { A >: ⊥ <: T }
| td_typ_top : forall A T, trivial_dec { A >: T <: ⊤ }
| td_trm : forall a T, trivial_typ T -> trivial_dec { a ⦂ T }
| td_trm_sngl : forall a p, trivial_dec { a ⦂ {{ p }} }

with trivial_record_typ : typ -> fset label -> Prop :=
| trt_one : forall D l,
  trivial_dec D ->
  l = label_of_dec D ->
  trivial_record_typ (typ_rcd D) \{l}
| trt_cons: forall T ls D l,
  trivial_record_typ T ls ->
  trivial_dec D ->
  l = label_of_dec D ->
  l \notin ls ->
  trivial_record_typ (T ∧ typ_rcd D) (union ls \{l})

with trivial_typ : typ -> Prop :=
  | trivial_typ_all : forall S T, trivial_typ (∀(S) T)
  | trivial_typ_bnd : forall T ls,
      trivial_record_typ T ls ->
      trivial_typ (μ T).

Lemma inv_weaken_ty_path : forall G x S p T,
    ok (G & x ~ S) ->
    x \notin (fv_ctx_types G \u fv_path p \u fv_typ T) ->
    trivial_typ S ->
    G & x ~ S ⊢ trm_path p : T ->
    G ⊢ trm_path p : T
with inv_weaken_subtyp : forall G x S T U,
    ok (G & x ~ S) ->
    x \notin (fv_ctx_types G \u fv_typ T \u fv_typ U) ->
    trivial_typ S ->
    G & x ~ S ⊢ T <: U ->
    G ⊢ T <: U.
Proof.
  all: introv Hok Hx HS H.
  - dependent induction H.
    -- constructor. eapply binds_concat_left_inv. exact H.
       simpl in Hx. eauto.
    -- constructor. apply IHty_trm with (S0 := S) (x0 := x); eauto.
       destruct p0; simpl in *. eauto.
    -- constructor. apply IHty_trm with (S0 := S) (x0 := x); eauto.
       destruct p; simpl in *. eauto.
    -- apply ty_sngl with (q := q).
       * apply IHty_trm1 with (S0:=S) (x0:=x); eauto.
         destruct p; simpl in *. admit.
       * apply IHty_trm2 with (S0:=S) (x0:=x); eauto.
         admit.
    -- apply ty_path_elim with (T:=T). admit. admit.
    -- apply ty_rec_intro. apply IHty_trm with (S0:=S) (x0:=x); eauto.
       destruct (open_typ_p_fv) as [HTv _]. unfold open_typ_p.
       destruct (HTv T p 0); rewrite H0; eauto. simpl in Hx. eauto.
    -- apply ty_rec_elim. apply IHty_trm with (S0:=S) (x0:=x); eauto.
       simpl in *.
       destruct (open_typ_p_fv) as [HTv _]. unfold open_typ_p in Hx.
       destruct (HTv T p 0); rewrite H0 in Hx; eauto.
    -- apply ty_and_intro.
       * apply~ IHty_trm1; eauto. simpl in *; eauto.
       * apply~ IHty_trm2; eauto. simpl in *; eauto.
    -- apply ty_sub with (T:=T). apply~ IHty_trm; eauto.
       admit. apply~ inv_weaken_subtyp; eauto. admit.
Admitted.

(* Lemma inv_weaken_ty_trm : forall G1 G2 x S t T, *)
(*     ok (G1 & x ~ S & G2) -> *)
(*     x \notin (fv_ctx_types G1 \u fv_ctx_types G2 \u fv_trm t \u fv_typ T) -> *)
(*     trivial_typ S -> *)
(*     G1 & x ~ S & G2 ⊢ t : T -> *)
(*     G1 & G2 ⊢ t : T *)
(* with inv_weaken_ty_def : forall y bs G1 G2 x S d D, *)
(*     ok (G1 & x ~ S & G2) -> *)
(*     x \notin (fv_ctx_types G1 \u fv_ctx_types G2 \u fv_def d \u fv_dec D) -> *)
(*     trivial_typ S -> *)
(*     y; bs; G1 & x ~ S & G2 ⊢ d : D -> *)
(*     y; bs; G1 & G2 ⊢ d : D *)
(* with inv_weaken_ty_defs : forall y bs G1 G2 x S ds T, *)
(*     ok (G1 & x ~ S & G2) -> *)
(*     x \notin (fv_ctx_types G1 \u fv_ctx_types G2 \u fv_defs ds \u fv_typ T) -> *)
(*     trivial_typ S -> *)
(*     y; bs; G1 & x ~ S & G2 ⊢ ds :: T -> *)
(*     y; bs; G1 & G2 ⊢ ds :: T *)
(* with inv_weaken_subtyp : forall G1 G2 x S T U, *)
(*     ok (G1 & x ~ S & G2) -> *)
(*     x \notin (fv_ctx_types G1 \u fv_ctx_types G2 \u fv_typ T \u fv_typ U) -> *)
(*     trivial_typ S -> *)
(*     G1 & x ~ S & G2 ⊢ T <: U -> *)
(*     G1 & G2 ⊢ T <: U. *)
(* Proof. *)
(*   all: introv Hok Hx HS H. *)
(*   - dependent induction H. *)
(*     -- constructor. eapply binds_subst. *)
(*        exact H. simpl in Hx. eauto. *)
(*     -- fresh_constructor. rewrite <- concat_assoc. *)
(*        apply H0 with (S0:=S) (x0:=x); eauto 5; try rewrite -> concat_assoc; eauto 2. *)
(*        rewrite fv_ctx_types_push_eq. simpl in Hx. *)
(*        destruct open_trm_fv as [Htv _]. *)
(*        destruct open_typ_fv as [HTv _]. *)
(*        unfold open_trm. unfold open_typ. *)
(*        destruct (Htv t z 0); destruct (HTv U z 0); *)
(*          rewrite H1; rewrite H2; eauto. *)
(*     -- apply ty_all_elim with (S:=S0). *)
(*        * apply IHty_trm1 with (S1:=S) (x0:=x); eauto. *)
(*          simpl in Hx. simpl. *)
(*          destruct open_typ_p_fv as [HTv _]. unfold open_typ_p in Hx. *)
(*          specialize (HTv T q 0). destruct HTv. rewrite H1 in Hx. *)
(* Admitted. *)

Lemma inv_weaken_typ_inert : forall G x S p T,
    inert (G & x ~ S) ->
    x \notin (fv_ctx_types G \u fv_path p \u fv_typ T) ->
    G & x ~ S ⊢ trm_path p : T ->
    G ⊢ trm_path p : T
with inv_weaken_subtyp_inert : forall G x S T U,
    inert (G & x ~ S) ->
    x \notin (fv_ctx_types G \u fv_typ T \u fv_typ U) ->
    G & x ~ S ⊢ T <: U ->
    G ⊢ T <: U.
Admitted.



