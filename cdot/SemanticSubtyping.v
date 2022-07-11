(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** * Invertible subtyping ⊢{} *)


Require Import Coq.Program.Equality.
Require Import Definitions RecordAndInertTypes PreciseTyping TightTyping InvertibleTyping Narrowing Replacement Binding Subenvironments Weakening.

Reserved Notation "G '⊢{}' T '<:' U" (at level 40, T at level 59).

Inductive subtyp_s : ctx -> typ -> typ -> Prop :=

(** [G ⊢{} T <: top] *)
| subtyp_top_s: forall G T,
    G ⊢{} T <: ⊤

(** [G ⊢{} bot <: T] *)
| subtyp_bot_s: forall G T,
    G ⊢{} ⊥ <: T

(** [G ⊢{} T <: T] *)
| subtyp_refl_s: forall G T,
    G ⊢{} T <: T

(** [G ⊢{} T <: S]       #<br>#
    [――――――――――――――――]   #<br>#
    [G ⊢{} T /\ U <: S]       *)
| subtyp_and11_s: forall G S T U,
    G ⊢{} T <: S ->
    G ⊢{} T ∧ U <: S

(** [G ⊢{} U <: S]       #<br>#
    [――――――――――――――――]   #<br>#
    [G ⊢{} T /\ U <: S]       *)
| subtyp_and12_s: forall G S T U,
    G ⊢{} U <: S ->
    G ⊢{} T ∧ U <: S

(** [G ⊢{} S <: T]       #<br>#
    [G ⊢{} S <: U]       #<br>#
    [――――――――――――――――]   #<br>#
    [G ⊢{} S <: T /\ U]       *)
| subtyp_and2_s: forall G S T U,
    G ⊢{} S <: T ->
    G ⊢{} S <: U ->
    G ⊢{} S <: T ∧ U

(** [G ⊢{} T <: U]           #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢{} {a: T} <: {a: U}]     *)
| subtyp_fld_s : forall G T U a,
    G ⊢{} T <: U ->
    G ⊢{} typ_rcd {a ⦂ T} <: typ_rcd {a ⦂ U}

(** [G ⊢# S2 <: S1]                   #<br>#
    [G ⊢# T1 <: T2]                   #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [G ⊢{} {A: S1..T1} <: {A: S2..T2}]     *)
| subtyp_typ_s: forall G S1 S2 T1 T2 A,
    G ⊢# S2 <: S1 ->
    G ⊢# T1 <: T2 ->
    G ⊢{} typ_rcd { A >: S1 <: T1 } <: typ_rcd { A >: S2 <: T2 }

(** [G ⊢!!! p: q.type]                 #<br>#
    [G ⊢!!! q: U]                      #<br>#
    [G ⊢{} S <: T]                      #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [G ⊢{} S <: [T[q/p,n]]              *)
| subtyp_sngl_pq2_s : forall G p q S T T' U,
    G ⊢!!! p : {{ q }} ->
    G ⊢!!! q : U ->
    repl_typ p q T T' ->
    G ⊢{} S <: T ->
    G ⊢{} S <: T'

(** [G ⊢!!! p: q.type]                 #<br>#
    [G ⊢!!! q: U]                      #<br>#
    [G ⊢{} S <: T]                      #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [G ⊢{} S <: [T[p/q,n]]              *)
| subtyp_sngl_qp2_s : forall G p q S T T' U,
    G ⊢!!! p : {{ q }} ->
    G ⊢!!! q : U ->
    repl_typ q p T T' ->
    G ⊢{} S <: T ->
    G ⊢{} S <: T'

(** [G ⊢!!! p: q.type]                 #<br>#
    [G ⊢!!! q: U]                      #<br>#
    [G ⊢{} S <: T]                      #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [G ⊢{} [S[q/p,n]] <: T              *)
| subtyp_sngl_pq1_s : forall G p q S S' T U,
    G ⊢!!! p : {{ q }} ->
    G ⊢!!! q : U ->
    repl_typ p q S S' ->
    G ⊢{} S <: T ->
    G ⊢{} S' <: T

(** [G ⊢!!! p: q.type]                 #<br>#
    [G ⊢!!! q: U]                      #<br>#
    [G ⊢{} S <: T]                      #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [G ⊢{} [S[p/q,n]] <: T              *)
| subtyp_sngl_qp1_s : forall G p q S S' T U,
    G ⊢!!! p : {{ q }} ->
    G ⊢!!! q : U ->
    repl_typ q p S S' ->
    G ⊢{} S <: T ->
    G ⊢{} S' <: T

(** [G ⊢!!! p: {A: T..T}] #<br>#
    [G ⊢{} S <: T] #<br>#
    [―――――――――――――――――――] #<br>#
    [G ⊢{} S <: p.A]         *)
| subtyp_sel2_s: forall G p A S T ,
    G ⊢!!! p : typ_rcd { A >: T <: T } ->
    G ⊢{} S <: T ->
    G ⊢{} S <: p ↓ A

(** [G ⊢!!! p: {A: T..T}] #<br>#
    [G ⊢{} T <: S] #<br>#
    [―――――――――――――――――――] #<br>#
    [G ⊢# p.A <: S]         *)
| subtyp_sel1_s: forall G p A S T,
    G ⊢!!! p : typ_rcd { A >: T <: T } ->
    G ⊢{} T <: S ->
    G ⊢{} p ↓ A <: S

(** [G ⊢# S2 <: S1]                #<br>#
    [G, x: S2 ⊢ T1^x <: T2^x]       #<br>#
    [x fresh]                       #<br>#
    [――――――――――――――――――――――――]      #<br>#
    [G ⊢# forall(S1)T1 <: forall(S2)T2]          *)
| subtyp_all_s: forall G S1 S2 T1 T2 L,
    G ⊢# S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2) ->
    G ⊢{} ∀(S1) T1 <: ∀(S2) T2
where "G '⊢{}' T '<:' U" := (subtyp_s G T U).

Hint Constructors subtyp_s.


Lemma trans_subtyp_top_s : forall G T U,
    G ⊢{} ⊤ <: T ->
    G ⊢{} U <: T.
Proof.
  intros G T U H. generalize dependent U.
  remember ⊤ as Top in H. rename HeqTop into Heq.
  induction H; intros.
  - (* top *)
    auto.
  - (* bot *)
    inversion Heq.
  - (* refl *)
    subst T. auto.
  - (* and11 *)
    inversion Heq.
  - (* and12 *)
    inversion Heq.
  - (* and2 *)
    specialize (IHsubtyp_s1 Heq).
    specialize (IHsubtyp_s2 Heq).
    eauto.
  - (* fld *)
    inversion Heq.
  - (* typ *)
    inversion Heq.
  - (* sngl_pq2 *)
    specialize (IHsubtyp_s Heq).
    specialize (IHsubtyp_s U0).
    eauto.
  - (* sngl_qp2 *)
    specialize (IHsubtyp_s Heq).
    specialize (IHsubtyp_s U0).
    eauto.
  - (* sngl_pq1 *)
    subst S'.
    inversion H1.
  - (* sngl_qp1 *)
    subst S'.
    inversion H1.
  - (* sel2 *)
    eauto.
  - (* sel1 *)
    inversion Heq.
  - (* all *)
    inversion Heq.
Qed.


Lemma trans_subtyp_and2_s : forall G S T U U1,
    (forall U1, G ⊢{} T <: U1 -> G ⊢{} S <: U1) ->
    (forall U1, G ⊢{} U <: U1 -> G ⊢{} S <: U1) ->
    G ⊢{} T ∧ U <: U1 ->
    G ⊢{} S <: U1.
Proof.
  intros G S T U U1 H1 H2 H.
  remember (T ∧ U) as And in H. rename HeqAnd into He.
  generalize dependent T.
  generalize dependent U.
  induction H; intros.
  - (* top *)
    auto.
  - (* bot *)
    inversion He.
  - (* refl *)
    subst T.
    apply subtyp_and2_s.
    -- apply H1. auto.
    -- apply H2. auto.
  - (* and11 *)
    inversion He; subst.
    apply H1. auto.
  - (* and12 *)
    inversion He; subst.
    apply H2. auto.
  - (* and2 *)
    specialize (IHsubtyp_s1 U0 H2 T0 H1 He).
    specialize (IHsubtyp_s2 U0 H2 T0 H1 He). eauto.
  - (* fld *)
    inversion He.
  - (* typ *)
    inversion He.
  - (* sngl_pq2 *)
    subst S0. specialize (IHsubtyp_s U0 H3 T0 H4).
    assert (T0 ∧ U0 = T0 ∧ U0) as Heq. trivial.
    specialize (IHsubtyp_s Heq).
    eauto.
  - (* sngl_qp2 *)
    subst S0. specialize (IHsubtyp_s U0 H3 T0 H4).
    assert (T0 ∧ U0 = T0 ∧ U0) as Heq. trivial.
    specialize (IHsubtyp_s Heq).
    eauto.
  - (* sngl_pq1 *)
    subst S'.
    inversion H1.
    -- subst.
       specialize (IHsubtyp_s U0 H3 T1).
       assert (forall U1, G ⊢{} T1 <: U1 -> G ⊢{} S <: U1) as H5.
       {
         intros. apply H4. eauto.
       }
       specialize (IHsubtyp_s H5). auto.
    -- subst.
       specialize (IHsubtyp_s T1).
       assert (forall U1, G ⊢{} T1 <: U1 -> G ⊢{} S <: U1) as H5.
       {
         intros. apply H3. eauto.
       }
       specialize (IHsubtyp_s H5 T0 H4).
       auto.
  - (* sngl_qp1 *)
    subst S'.
    inversion H1.
    -- subst.
       specialize (IHsubtyp_s U0 H3 T1).
       assert (forall U1, G ⊢{} T1 <: U1 -> G ⊢{} S <: U1) as H5.
       {
         intros. apply H4. eauto.
       } auto.
    -- subst.
       specialize (IHsubtyp_s T1).
       assert (forall U1, G ⊢{} T1 <: U1 -> G ⊢{} S <: U1) as H5.
       {
         intros. apply H3. eauto.
       }
       specialize (IHsubtyp_s H5 T0 H4).
       auto.
  - (* sel2 *)
    specialize (IHsubtyp_s U H2 T0 H1 He). eauto.
  - (* sel1 *)
    inversion He.
  - (* all *)
    inversion He.
Qed.


Lemma pt3_inert_pt2_sngl_invert' G p q T ls :
  inert G ->
  G ⊢!!! p : T ->
  G ⊢!! p : {{ q }}->
  record_typ T ls ->
  G ⊢!!! q : T.
Proof.
  intros Hi Hp Hpq Hin. gen q. induction Hp; introv Hpq.
  - pose proof (pt2_sngl_unique' Hi Hpq H) as ->. inversion Hin.
  - pose proof (pt2_sngl_unique Hi H Hpq) as ->. eauto.
Qed.


Lemma pt3_inert_sngl_invert' G p q T ls :
  inert G ->
  G ⊢!!! p : T ->
  G ⊢!!! p : {{ q }}->
  record_typ T ls ->
  G ⊢!!! q : T.
Proof.
  introv Hi Hp Hpq. gen T. dependent induction Hpq; introv Hp Hin;
                             [.. | apply* IHHpq];
                             eapply (pt3_inert_pt2_sngl_invert' _ _ _ _ ls Hi Hp); eauto.
Qed.


Lemma pt3_rcd_unique : forall G p A T1 T2,
    inert G ->
    G ⊢!!! p : typ_rcd {A >: T1 <: T1} ->
    G ⊢!!! p : typ_rcd {A >: T2 <: T2} ->
    T1 = T2.
Proof.
  introv Hi H1 H2.
  remember p as q in H2.
  generalize dependent q.
  remember (typ_rcd {A >: T1 <: T1}) as Typ in H1.
  induction H1; introv Heq H2.
  - subst.
    inversion H2; subst; clear H2.
    -- inversion H; subst; clear H.
       inversion H0; subst; clear H0.
       pose proof (pf_bnd_T2 Hi H1).
       destruct H0. subst.
       pose proof (pf_bnd_T2 Hi H).
       destruct H0. subst.
       pose proof (pf_T_unique Hi H1 H).
       inversion H0; subst. clear H0.
       eapply pf_dec_typ_unique. apply Hi.
       apply H1. apply H.
    -- pose proof (pt2_sngl_unique' Hi H0 H). inversion H2.
  - subst.
    inversion H2.
    -- subst. pose proof (pt2_sngl_unique' Hi H H0). inversion H3.
    -- subst. specialize (IHprecise_typing3 Hi).
       pose proof (pt2_sngl_unique Hi H H0). subst q.
       eapply IHprecise_typing3.
       trivial.
       trivial.
       auto.
Qed.


Lemma pt3_trans_qp : forall G p q bs T,
    inert G ->
    G ⊢!!! p : {{ q }} ->
    G ⊢!!! q •• bs : T ->
    G ⊢!!! p •• bs : T.
Proof.
  apply pt3_field_trans'.
Qed.


Lemma pt3_trans_rcd_pq : forall G p q bs ls T,
    inert G ->
    G ⊢!!! p : {{ q }} ->
    G ⊢!!! p •• bs : T ->
    record_typ T ls ->
    G ⊢!!! q •• bs : T.
Proof.
  introv Hi Hs Hf Hr.
  pose proof pt3_inert_sngl_invert'.
  apply H with (p := p •• bs) (ls := ls); try assumption.
  apply pt3_trans_trans with (T := T); try assumption.
Qed.


Lemma invert_subtyp_sel2_p : forall G p A S T,
    inert G ->
    G ⊢!!! p : typ_rcd { A >: T <: T } ->
    G ⊢{} S <: p ↓ A ->
    G ⊢{} S <: T.
Proof.
  introv Hi Hp Hs.
  remember (p ↓ A) as Sel in Hs.
  gen p.
  induction Hs; introv Hp He.
  - (* top *)
    inversion He.
  - (* bot *)
    auto.
  - (* refl *)
    subst T0. eauto.
  - (* and11 *)
    subst S.
    eauto.
  - (* and12 *)
    subst S. eauto.
  - (* and2 *)
    inversion He.
  - (* fld *)
    inversion He.
  - (* typ *)
    inversion He.
  - (* sngl_pq2 *)
    subst T'.
    inversion H1; subst.
    apply IHHs with (p0 := p •• bs); try assumption; try trivial.
    -- apply pt3_trans_qp with (q := q); try assumption.
  - (* sngl_qp2 *)
    subst T'.
    inversion H1; subst.
    apply IHHs with (p := q •• bs); try assumption; try trivial.
    eapply pt3_trans_rcd_pq with (p := p); try assumption. eauto.
  - (* sngl_pq1 *)
    subst. eauto.
  - (* sngl_qp1 *) eauto.
  - (* sel2 *)
    inversion He. subst.
    assert (T = T0) as HeqT.
    {
      eapply pt3_rcd_unique.
      apply Hi.
      apply Hp.
      apply H.
    }
    subst T. eauto.
  - (* sel1 *)
    subst S.
    eauto.
  - (* all *) inversion He.
Qed.


Lemma invert_subtyp_sel1_p : forall G p A T U,
    inert G ->
    G ⊢!!! p : typ_rcd { A >: T <: T } ->
    G ⊢{} p ↓ A <: U ->
    G ⊢{} T <: U.
Proof.
  intros G p A T U Hi H H0.
  remember (p ↓ A) as Sel in H0. rename HeqSel into He.
  generalize dependent p.
  induction H0; intros.
  - (* top *) eauto.
  - (* bot *) inversion He.
  - (* refl *) subst T0. eauto.
  - (* and11 *) inversion He.
  - (* and12 *) inversion He.
  - (* and2 *)
    specialize (IHsubtyp_s1 Hi p H He).
    specialize (IHsubtyp_s2 Hi p H He). eauto.
  - (* fld *) inversion He.
  - (* typ *) inversion He.
  - (* sngl_pq2 *)
    specialize (IHsubtyp_s Hi p0 H3 He).
    eauto.
  - (* sngl_qp2 *)
    specialize (IHsubtyp_s Hi p0 H3 He).
    eauto.
  - (* sngl_pq1 *)
    subst S'.
    inversion H1; subst.
    specialize (IHsubtyp_s Hi (p •• bs)).
    assert (G ⊢!!! p •• bs : typ_rcd {A >: T <: T}) as H4.
    {
      eapply pt3_field_trans'.
      apply Hi.
      apply H.
      apply H3.
    }
    specialize (IHsubtyp_s H4).
    apply IHsubtyp_s. trivial.
  - (* sngl_qp1 *)
    subst S'.
    inversion H1; subst.
    specialize (IHsubtyp_s Hi (q •• bs)).
    assert (G ⊢!!! q •• bs : typ_rcd {A >: T <: T}) as H4.
    {
      pose proof pt3_inert_sngl_invert'.
      eapply H4.
      apply Hi.
      apply H3.
      eapply pt3_trans_trans.
      apply Hi.
      apply H.
      apply H3.
      eauto.
    }
    specialize (IHsubtyp_s H4). eauto.
  - (* sel2 *)
    specialize (IHsubtyp_s Hi p0 H1 He).
    eauto.
  - (* sel1 *)
    inversion He; subst.
    pose proof (pt3_rcd_unique _ _ _ _ _ Hi H H1).
    subst. auto.
  - (* all *)
    inversion He.
Qed.


Lemma trans_subtyp_fld_s : forall G a S T U,
    inert G ->
    (forall U1, G ⊢{} T <: U1 -> G ⊢{} S <: U1) ->
    G ⊢{} typ_rcd {a ⦂ T} <: U ->
    G ⊢{} typ_rcd {a ⦂ S} <: U.
Proof.
  introv Hi H Hs.
  remember (typ_rcd {a ⦂ T}) as Fld.
  rename HeqFld into He.
  gen T.
  induction Hs; introv Htrans He.
  - (* top *)
    auto.
  - (* bot *)
    inversion He.
  - (* refl *)
    subst T. eauto.
  - (* and11 *)
    inversion He.
  - (* and12 *)
    inversion He.
  - (* and2 *)
    specialize (IHHs1 Hi T0 Htrans He).
    specialize (IHHs2 Hi T0 Htrans He).
    eauto.
  - (* fld *)
    inversion He; subst.
    eauto.
  - (* typ *)
    inversion He.
  - (* sngl_pq2 *)
    eauto.
  - (* sngl_qp2 *)
    eauto.
  - (* sngl_pq1 *)
    specialize (IHHs Hi).
    subst S'. inversion H1. subst.
    inversion H6. subst.
    specialize (IHHs T1).
    apply IHHs.
    -- introv Hsub.
       eauto.
    -- trivial.
  - (* sngl_qp1 *)
    specialize (IHHs Hi).
    subst S'. inversion H1. subst.
    inversion H6. subst.
    specialize (IHHs T1).
    apply IHHs.
    -- introv Hsub.
       eauto.
    -- trivial.
  - (* sel2 *)
    subst S0.
    specialize (IHHs Hi T0 Htrans).
    eauto.
  - (* sel1 *)
    inversion He.
  - (* all *)
    inversion He.
Qed.


Lemma trans_subtyp_typ_s : forall G A S1 S2 T1 T2 U,
    inert G ->
    G ⊢# S2 <: S1 ->
    G ⊢# T1 <: T2 ->
    G ⊢{} typ_rcd {A >: S2 <: T2} <: U ->
    G ⊢{} typ_rcd {A >: S1 <: T1} <: U.
Proof.
  introv Hi Hs Ht H.
  remember (typ_rcd {A >: S2 <: T2}) as typ2 in H.
  gen S2 T2.
  induction H; intros.
  - (* top *)
    auto.
  - (* bot *)
    inversion Heqtyp2.
  - (* refl *)
    subst. eauto.
  - (* and11 *)
    inversion Heqtyp2.
  - (* and12 *)
    inversion Heqtyp2.
  - (* and2 *)
    specialize (IHsubtyp_s1 Hi S2 Hs T2 Ht Heqtyp2).
    specialize (IHsubtyp_s2 Hi S2 Hs T2 Ht Heqtyp2).
    eauto.
  - (* fld *)
    inversion Heqtyp2.
  - (* typ *)
    inversion Heqtyp2; subst. clear Heqtyp2.
    eauto.
  - (* sngl_pq2 *)
    eauto.
  - (* sngl_qp2 *)
    eauto.
  - (* sngl_pq1 *)
    subst S'.
    specialize (IHsubtyp_s Hi).
    inversion H1; subst.
    inversion H7; subst.
    -- apply IHsubtyp_s with (S2 := T0) (T3 := T2); eauto.
    -- apply IHsubtyp_s with (S3 := S2) (T2 := T0); eauto.
       destruct repl_swap as [repl_swap _].
       specialize (repl_swap _ _ _ _ H8).
       eauto.
  - (* sngl_qp1 *)
    subst S'.
    specialize (IHsubtyp_s Hi).
    inversion H1; subst.
    inversion H7; subst.
    -- apply IHsubtyp_s with (S2 := T0) (T3 := T2); eauto.
    -- apply IHsubtyp_s with (S3 := S2) (T2 := T0); eauto.
       destruct repl_swap as [repl_swap _].
       specialize (repl_swap _ _ _ _ H8). eauto.
  - (* sel2 *)
    eauto.
  - (* sel1 *)
    inversion Heqtyp2.
  - (* all *)
    inversion Heqtyp2.
Qed.


Lemma trans_subtyp_all_s : forall G L S1 S2 T1 T2 U,
    inert G ->
    G ⊢# S2 <: S1 ->
    (forall x, x \notin L -> G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2) ->
    G ⊢{} typ_all S2 T2 <: U ->
    G ⊢{} typ_all S1 T1 <: U.
Proof.
  introv Hi Htrans1 Htrans2 Hsub.
  remember (typ_all S2 T2) as all2 in Hsub.
  gen S2 T2 L.
  induction Hsub; intros.
  - (* top *)
    auto.
  - (* bot *)
    inversion Heqall2.
  - (* refl *)
    subst. eauto.
  - (* and11 *)
    inversion Heqall2.
  - (* and12 *)
    inversion Heqall2.
  - (* and2 *)
    specialize (IHHsub1 Hi S2 Htrans1 T2 Heqall2 L Htrans2).
    specialize (IHHsub2 Hi S2 Htrans1 T2 Heqall2 L Htrans2).
    eauto.
  - (* fld *)
    inversion Heqall2.
  - (* typ *)
    inversion Heqall2.
  - (* sngl_pq2 *)
    eauto.
  - (* sngl_qp2 *)
    eauto.
  - (* sngl_pq1 *)
    specialize (IHHsub Hi).
    subst S'. inversion H1; subst.
    -- assert (forall x, x \notin (L \u dom G) -> G & x ~ T0 ⊢ open_typ x T1 <: open_typ x T2).
       {
         introv Hnin.
         apply notin_union in Hnin.
         destruct Hnin as [Hn1 Hn2].
         specialize (Htrans2 _ Hn1).
         eapply narrow_subtyping.
         - apply Htrans2.
         - apply subenv_push.
           -- auto.
           -- eauto.
           -- eauto.
           -- pose proof (precise_to_general3 H) as Hpq.
              pose proof (precise_to_general3 H0) as Hq.
              eapply subtyp_sngl_pq.
              apply Hpq. apply Hq. assumption.
       }
       apply IHHsub with (S2 := T0) (T3 := T2) (L := L \u dom G); try assumption; eauto.
    -- apply IHHsub with (S3 := S2) (T2 := T0) (L := L \u dom G); try assumption; auto.
       introv Hn. apply notin_union in Hn. destruct Hn as [Hn1 Hn2].
       pose proof (precise_to_general3 H) as Hpq.
       pose proof (precise_to_general3 H0) as Hq.
       specialize (Htrans2 _ Hn1).
       assert (G & x ~ S2 ⊢ open_typ x T2 <: open_typ x T0). {
        apply subtyp_sngl_qp with (p := p) (q := q) (U := U).
        + apply weaken_ty_trm; try assumption. eauto.
        + apply weaken_ty_trm; try assumption. eauto.
        + apply repl_open_var.
          destruct repl_swap as [repl_swap _]. apply repl_swap in H6.
          apply H6.
          ++ eapply typed_paths_named. apply Hq.
          ++ eapply typed_paths_named. apply Hpq.
      }
      eapply subtyp_trans. apply Htrans2. auto.
  - (* sngl_qp1 *)
    specialize (IHHsub Hi).
    subst S'. inversion H1; subst.
    -- assert (forall x, x \notin (L \u dom G) -> G & x ~ T0 ⊢ open_typ x T1 <: open_typ x T2).
       {
         introv Hnin.
         apply notin_union in Hnin.
         destruct Hnin as [Hn1 Hn2].
         specialize (Htrans2 _ Hn1).
         eapply narrow_subtyping.
         - apply Htrans2.
         - apply subenv_push.
           -- auto.
           -- eauto.
           -- eauto.
           -- pose proof (precise_to_general3 H) as Hpq.
              pose proof (precise_to_general3 H0) as Hq.
              eapply subtyp_sngl_qp.
              apply Hpq. apply Hq. assumption.
       }
       apply IHHsub with (S2 := T0) (T3 := T2) (L := L \u dom G); try assumption; eauto.
    -- apply IHHsub with (S3 := S2) (T2 := T0) (L := L \u dom G); try assumption; auto.
       introv Hn. apply notin_union in Hn. destruct Hn as [Hn1 Hn2].
       pose proof (precise_to_general3 H) as Hpq.
       pose proof (precise_to_general3 H0) as Hq.
       specialize (Htrans2 _ Hn1).
       assert (G & x ~ S2 ⊢ open_typ x T2 <: open_typ x T0). {
        destruct repl_swap as [repl_swap _]. apply repl_swap in H6.
        apply subtyp_sngl_pq with (p := p) (q := q) (U := U).
        + apply weaken_ty_trm; try assumption. eauto.
        + apply weaken_ty_trm; try assumption. eauto.
        + apply repl_open_var.
          apply H6.
          ++ eapply typed_paths_named. apply Hpq.
          ++ eapply typed_paths_named. apply Hq.
      }
      eapply subtyp_trans. apply Htrans2. auto.
  - (* sel2 *)
    eauto.
  - (* sel1 *)
    inversion Heqall2.
  - (* all *)
    inversion Heqall2. subst.
    clear Heqall2.
    apply subtyp_all_s with (L := L \u L0 \u dom G).
    -- eauto.
    -- introv Hn.
       apply notin_union in Hn. destruct Hn as [Hn1 Hn2].
       apply notin_union in Hn2. destruct Hn2 as [Hn2 Hn3].
       pose proof (H0 _ Hn1) as H0.
       pose proof (Htrans2 _ Hn2) as H1.
       apply tight_to_general in H.
       assert (G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T3) as H2.
       {
         eapply narrow_subtyping.
         - apply H1.
         - eapply subenv_push.
           -- auto.
           -- eauto.
           -- eauto.
           -- auto.
       }
       eapply subtyp_trans. apply H2. apply H0.
Qed.

Theorem trans_subtyp_s : forall G S T U,
    inert G ->
    G ⊢{} S <: T ->
    G ⊢{} T <: U ->
    G ⊢{} S <: U.
Proof.
  introv Hi H1 H2.
  generalize dependent U.
  induction H1; intros.
  - (* top *)
    apply trans_subtyp_top_s. auto.
  - (* bot *) auto.
  - (* refl *)
    auto.
  - (* and11 *)
    apply subtyp_and11_s.
    apply IHsubtyp_s.
    exact Hi.
    auto.
  - (* and12 *)
    apply subtyp_and12_s.
    apply IHsubtyp_s; auto.
  - (* and2 *)
    eapply trans_subtyp_and2_s.
    apply IHsubtyp_s1.
    exact Hi.
    apply IHsubtyp_s2.
    exact Hi.
    apply H2.
  - (* fld *)
    specialize (IHsubtyp_s Hi).
    eapply trans_subtyp_fld_s.
    -- exact Hi.
    -- apply IHsubtyp_s.
    -- exact H2.
  - (* typ *)
    eapply trans_subtyp_typ_s; try assumption.
    -- apply H.
    -- apply H0.
    -- apply H2.
  - (* sngl_pq2 *)
    apply IHsubtyp_s. exact Hi.
    destruct repl_swap as [Hr _].
    apply Hr in H1.
    eauto.
  - (* sngl_qp2 *)
    apply IHsubtyp_s. exact Hi.
    destruct repl_swap as [Hr _].
    apply Hr in H1.
    eauto.
  - (* sngl_pq1 *)
    eauto.
  - (* sngl_qp1 *)
    eauto.
  - (* sel2 *)
    pose proof (invert_subtyp_sel1_p _ _ _ _ _ Hi H H2).
    eauto.
  - (* sel1 *)
    specialize (IHsubtyp_s Hi).
    eauto.
  - (* all *)
    eapply trans_subtyp_all_s; try assumption.
    apply H.
    apply H0.
    apply H2.
Qed.


Theorem semantic_to_tight : forall G S T,
    G ⊢{} S <: T -> G ⊢# S <: T.
Proof.
  introv H. induction H; eauto.
  - apply subtyp_trans_t with (T := S).
    -- destruct repl_swap as [Hr _]. apply Hr in H1.
       eauto.
    -- auto.
  - apply subtyp_trans_t with (T := S).
    -- destruct repl_swap as [Hr _]. apply Hr in H1.
       eauto.
    -- auto.
Qed.


Theorem tight_to_semantic : forall G S T,
    inert G ->
    G ⊢# S <: T -> G ⊢{} S <: T.
Proof.
  introv Hi H.
  induction H; eauto.
  apply trans_subtyp_s with (T := T); auto.
Qed.

  (* - (* top *) *)
  (* - (* bot *) *)
  (* - (* refl *) *)
  (* - (* and11 *) *)
  (* - (* and12 *) *)
  (* - (* and2 *) *)
  (* - (* fld *) *)
  (* - (* typ *) *)
  (* - (* sngl_pq2 *) *)
  (* - (* sngl_qp2 *) *)
  (* - (* sngl_pq1 *) *)
  (* - (* sngl_qp1 *) *)
  (* - (* sel2 *) *)
  (* - (* sel1 *) *)
  (* - (* all *) *)
