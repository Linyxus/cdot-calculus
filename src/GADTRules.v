(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Require Import Coq.Program.Equality.
Require Import Definitions TightTyping SemanticSubtyping PreciseTyping.
Require Import Replacement Binding.


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
