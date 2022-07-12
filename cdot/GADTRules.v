(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** * Lemmas for inversion rules *)

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

(** ** Lemma 4.6 (Field inversion in <:##) *)
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
       apply~ narrow_subtyping. eapply subenv_push.
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
       apply~ narrow_subtyping. eapply subenv_push.
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

Lemma invert_subtyp_fld_s_label : forall G a1 a2 T1 T2,
    G ⊢{} typ_rcd {a1 ⦂ T1} <: typ_rcd {a2 ⦂ T2} ->
    a1 = a2.
Proof.
  introv Hs.
  dependent induction Hs; auto; inv_repl_typ_rcd; inv_repl_dec; apply* IHHs.
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
  - inversion Heqtyp.
  - (* andl *)
    apply invert_subtyp_and2_s in Hs as [Hs1 Hs2].
    eauto.
  - (* andr *)
    apply invert_subtyp_and2_s in Hs as [Hs1 Hs2].
    eauto.
Qed.

Lemma reduce_subtyp_fld2_s : forall G U1 U2 a T,
    G ⊢{} U1 <: U2 ->
    U2 ↘ typ_rcd {a ⦂ T} ->
    G ⊢{} U1 <: typ_rcd {a ⦂ T}.
Proof.
  introv Hs [ls Hu].
  dependent induction Hu.
  - (* fld *) auto.
  - (* andl *)
    apply invert_subtyp_and2_s in Hs as [Hs1 Hs2].
    eauto.
  - (* andr *)
    apply invert_subtyp_and2_s in Hs as [Hs1 Hs2].
    eauto.
Qed.

Lemma unique_membership_in_typ_labels : forall U L A S T,
    unique_membership U L (typ_rcd {A >: S <: T}) ->
    label_typ A \in L.
Proof.
  introv H.
  remember (typ_rcd (dec_typ A S T)) as T1.
  induction H.
  - (* typ *) inversion HeqT1. subst. apply in_singleton_self.
  - (* fld *) inversion HeqT1.
  - inversion HeqT1.
  - (* andl *)
    specialize (IHunique_membership1 HeqT1).
    rewrite in_union. left. auto.
  - (* andr *)
    specialize (IHunique_membership2 HeqT1).
    rewrite in_union. right. auto.
Qed.

Lemma unique_membership_in_trm_labels : forall U L a T,
    unique_membership U L (typ_rcd {a ⦂ T}) ->
    label_trm a \in L.
Proof.
  introv H.
  dependent induction H.
  - apply in_singleton_self.
  - (* andl *)
    specialize (IHunique_membership1 _ _ eq_refl).
    rewrite in_union. left. auto.
  - (* andr *)
    specialize (IHunique_membership2 _ _ eq_refl).
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

Lemma subtyp_s_typ_trm_false : forall G a U A S T,
    ~ G ⊢{} typ_rcd {A >: S <: T} <: typ_rcd {a ⦂ U}.
Proof.
  introv Hsub.
  dependent induction Hsub; inv_repl_typ_rcd; inv_repl_dec; apply* IHHsub.
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

Lemma subtyp_s_rec_fld_false : forall G U a T,
    ~ G ⊢{} μ U <: typ_rcd {a ⦂ T}.
Proof.
  introv Hs.
  dependent induction Hs;
    try solve [inv_repl_typ_rcd; inv_repl_dec;
      specialize (IHHs _ _ _ eq_refl eq_refl); false* IHHs];
    try solve [inv_repl_typ_rec; apply* IHHs].
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

Lemma unique_membership_notin_typ_labels : forall G U L T1 A S T,
    unique_membership U L T1 ->
    (label_typ A) \notin L ->
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
    -- specialize (IHunique_membership1 Hn1 H0). contradiction.
    -- specialize (IHunique_membership2 Hn2 H0). contradiction.
  - (* andl *)
    apply notin_union in Hn. destruct Hn as [Hn1 Hn2].
    apply invert_subtyp_and1_s_rcd in Ha.
    destruct Ha.
    -- specialize (IHunique_membership1 Hn1 H0). contradiction.
    -- specialize (IHunique_membership2 Hn2 H0). contradiction.
Qed.

Lemma unique_membership_notin_trm_labels : forall G U L T1 a T,
    unique_membership U L T1 ->
    (label_trm a) \notin L ->
    ~ G ⊢{} U <: typ_rcd {a ⦂ T}.
Proof.
  introv Hm Hn Hs.
  dependent induction Hm.
  - (* typ *) false* subtyp_s_typ_trm_false.
  - (* fld *)
    rewrite -> notin_singleton in Hn.
    apply invert_subtyp_fld_s_label in Hs.
    subst a0. false* Hn.
  - false* subtyp_s_rec_fld_false.
  - (* andl *)
    apply notin_union in Hn. destruct Hn as [Hn1 Hn2].
    apply invert_subtyp_and1_s_rcd in Hs.
    destruct Hs.
    -- specialize (IHHm1 Hn1 H0). contradiction.
    -- specialize (IHHm2 Hn2 H0). contradiction.
  - (* andl *)
    apply notin_union in Hn. destruct Hn as [Hn1 Hn2].
    apply invert_subtyp_and1_s_rcd in Hs.
    destruct Hs.
    -- specialize (IHHm1 Hn1 H0). contradiction.
    -- specialize (IHHm2 Hn2 H0). contradiction.
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
       apply unique_membership_in_typ_labels in Hu1.
       pose proof (disjoint_in_notin H Hu1) as Hni.
       contradict Hs. eapply unique_membership_notin_typ_labels.
       apply Hu2. apply Hni.
  - (* andr *)
    apply invert_subtyp_and1_s_rcd in Hs as [Hs | Hs].
    -- subst.
       apply unique_membership_in_typ_labels in Hu2.
       apply disjoint_comm in H.
       pose proof (disjoint_in_notin H Hu2) as Hni.
       contradict Hs. eapply unique_membership_notin_typ_labels.
       apply Hu1. apply Hni.
    -- auto.
Qed.

Lemma reduce_subtyp_fld1_s : forall G U1 a T1 T2,
    G ⊢{} U1 <: typ_rcd {a ⦂ T2} ->
    U1 ↘ typ_rcd {a ⦂ T1} ->
    G ⊢{} typ_rcd {a ⦂ T1} <: typ_rcd {a ⦂ T2}.
Proof.
  introv Hs [ls Hu].
  dependent induction Hu; auto.
  - (* andl *)
    apply invert_subtyp_and1_s_rcd in Hs as [Hs | Hs].
    -- auto.
    -- apply unique_membership_in_trm_labels in Hu1.
       pose proof (disjoint_in_notin H Hu1) as Hni.
       contradict Hs. eapply unique_membership_notin_trm_labels.
       apply Hu2. apply Hni.
  - (* andr *)
    apply invert_subtyp_and1_s_rcd in Hs as [Hs | Hs].
    -- subst.
       apply unique_membership_in_trm_labels in Hu2.
       apply disjoint_comm in H.
       pose proof (disjoint_in_notin H Hu2) as Hni.
       contradict Hs. eapply unique_membership_notin_trm_labels.
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

Lemma reduce_subtyp_fld_both_s : forall G U1 U2 a T1 T2,
    U1 ↘ typ_rcd {a ⦂ T1} ->
    U2 ↘ typ_rcd {a ⦂ T2} ->
    G ⊢{} U1 <: U2 ->
    G ⊢{} typ_rcd {a ⦂ T1} <: typ_rcd {a ⦂ T2}.
Proof.
  introv Hu1 Hu2 Hsub.
  pose proof (reduce_subtyp_fld2_s _ _ _ _ _ Hsub Hu2) as H1.
  pose proof (reduce_subtyp_fld1_s _ _ _ _ _ H1 Hu1) as H2.
  auto.
Qed.

Lemma invert_subtyp_rcd_s : forall G U1 A S1 T1 S2 T2,
    U1 ↘ typ_rcd {A >: S1 <: T1} ->
    G ⊢{} U1 <: typ_rcd {A >: S2 <: T2} ->
    G ⊢# S2 <: S1 /\ G ⊢# T1 <: T2.
Proof.
  introv Hu1 Hsub.
  lets Hr: (reduce_subtyp_rcd1_s _ _ _ _ _ _ _ Hsub Hu1).
  apply* invert_subtyp_typ_s.
Qed.

(** ** Lemma 4.3 (Type member inversion) *)
Lemma invert_subtyp_rcd_t : forall G U1 A S1 T1 S2 T2,
    inert G ->
    U1 ↘ typ_rcd {A >: S1 <: T1} ->
    G ⊢# U1 <: typ_rcd {A >: S2 <: T2}  ->
    G ⊢# S2 <: S1 /\ G ⊢# T1 <: T2.
Proof.
  introv Hi Hu1 Hsub.
  apply* invert_subtyp_rcd_s.
  apply* tight_to_semantic.
Qed.

Lemma invert_subtyp_fld_s : forall G U1 a T1 T2,
    U1 ↘ typ_rcd {a ⦂ T1} ->
    G ⊢{} U1 <: typ_rcd {a ⦂ T2} ->
    G ⊢{} T1 <: T2.
Proof.
  introv Hu1 Hsub.
  lets Hr: (reduce_subtyp_fld1_s _ _ _ _ _ Hsub Hu1).
  apply* invert_subtyp_trm_s.
Qed.

(** ** Lemma 4.2 (Field inversion)
    In an inert environment G, if G ⊢# U <: {a : T2} and U ↘ {a : T1},
    then G ⊢# T1 <: T2. *)
Lemma invert_subtyp_fld_t : forall G U1 a T1 T2,
    inert G ->
    U1 ↘ typ_rcd {a ⦂ T1} ->
    G ⊢# U1 <: typ_rcd {a ⦂ T2} ->
    G ⊢# T1 <: T2.
Proof.
  introv Hi Hu1 Hsub.
  apply semantic_to_tight.
  apply* invert_subtyp_fld_s.
  apply* tight_to_semantic.
Qed.

Lemma subst_unique_membership_labels : forall x p U L T,
    unique_membership U L T ->
    unique_membership (subst_typ x p U) L (subst_typ x p T).
Proof.
  introv Hu. induction Hu; simpl; eauto.
Qed.

Lemma subst_unique_membership : forall x p U T,
    U ↘ T ->
    subst_typ x p U ↘ subst_typ x p T.
Proof.
  introv [ls H]. exists ls.
  apply* subst_unique_membership_labels.
Qed.

  (* - (* typ *) *)
  (* - (* fld *) *)
  (* - (* andl *) *)
  (* - (* andr *) *)
