(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** * Converting General Typing To Tight Typing *)

Set Implicit Arguments.

Require Import Sequences.
Require Import Coq.Program.Equality.
Require Import Definitions RecordAndInertTypes PreciseTyping TightTyping InvertibleTyping
        Narrowing Replacement ReplacementTyping GADTRules.

(** ** Sel-<: Replacement *)


(** This lemma strengthens the tight [Sel-<:-#] and [<:-Sel-#] subtyping rules
    ([subtyp_sel1_t] and [subtyp_sel2_t]) by replacing the ⊢!!!
    premise with a ⊢# premise: #<br>#
    if [G ⊢# p: {A: S..U}] then [G ⊢# S <: p.A <: U] *)
Lemma sel_replacement: forall G p A S U,
    inert G ->
    G ⊢# trm_path p : typ_rcd {A >: S <: U} ->
    G ⊢# p↓A <: U /\ G ⊢# S <: p↓A.
Proof.
  introv Hi Hty.
  pose proof (replacement_closure Hi Hty) as Hinv.
  pose proof (repl_to_precise_rcd Hi Hinv) as [T [Ht [Hs1 Hs2]]].
  split.
  - apply subtyp_sel1_t in Ht. apply subtyp_trans_t with (T:=T); auto.
  - apply subtyp_sel2_t in Ht. apply subtyp_trans_t with (T:=T); auto.
Qed.

(** If [Γ ⊢# p] then [Γ ⊢!! p] *)
Lemma tight_to_prec_exists G p T :
  inert G ->
  G ⊢# trm_path p : T ->
  exists U, G ⊢!! p : U.
Proof.
  intros Hi Hp. pose proof (replacement_closure Hi Hp).
  apply repl_to_inv in H as [? ?]. apply inv_to_prec in H as [? ?]. apply* pt2_exists.
Qed.

(** ** Sngl-<: Replacement *)

(** This lemma strengthens the tight [Sngl-<:-#] and [<:-Sngl-#] subtyping rules
    ([subtyp_sngl_pq_t] and [subtyp_sngl_qp_t]) by replacing the ⊢!!! premise
    with a ⊢# premise: #<br>#
    if [G ⊢# p: q.type] and [q] is well-typed then [G ⊢# T <: T[q/p] <: T] *)
Lemma sngl_replacement: forall G p q T U S,
    inert G ->
    G ⊢# trm_path p: {{ q }} ->
    G ⊢# trm_path q : S ->
    repl_typ p q T U ->
    G ⊢# T <: U /\ G ⊢# U <: T.
Proof.
  introv Hi Hp Hr.
  apply (tight_to_prec_exists Hi) in Hr as [V Hq].
  lets Hc: (replacement_closure Hi Hp).
  pose proof (repl_to_invertible_sngl Hi Hc Hq) as [r [W [Hpt [Hq' [-> | Hpq]]]]];
    pose proof (inv_to_precise_sngl Hi Hpt (pt3 Hq')) as [r' [Ht [-> | Hrc']]].
  - split. eauto. apply repl_swap in H. eauto.
  - split.
    + destruct (repl_insert r H) as [X [Hr1 Hr2]].
      eapply subtyp_sngl_pq_t. eapply pt3_sngl_trans3. apply Ht. eauto. eauto. eauto.
    + destruct (repl_insert r' H) as [X [Hr1 Hr2]].
      apply subtyp_trans_t with (T:=X).
      * apply repl_swap in Hr2. eauto.
      * apply repl_swap in Hr1. eauto.
  - split.
    + destruct (repl_insert r H) as [X [Hr1 Hr2]].
      apply subtyp_trans_t with (T:=X); eauto.
    + destruct (repl_insert r H) as [X [Hr1 Hr2]].
      apply subtyp_trans_t with (T:=X).
      apply repl_swap in Hr2. eauto. apply repl_swap in Hr1. eauto.
  - split.
    + destruct (repl_insert r' H) as [X [Hr1 Hr2]].
      apply subtyp_trans_t with (T:=X).
      * eauto.
      * destruct (repl_insert r Hr2) as [S' [Hr1' Hr2']].
        apply subtyp_trans_t with (T:=S'); eauto.
    + destruct (repl_insert r H) as [X [Hr1 Hr2]].
      apply subtyp_trans_t with (T:=X).
      * apply repl_swap in Hr2. eauto.
      * destruct (repl_insert r' Hr1) as [S' [Hr1' Hr2']].
        apply subtyp_trans_t with (T:=S').
        ** apply repl_swap in Hr2'. eauto.
        ** apply repl_swap in Hr1'. eauto.
Qed.

(** ** General to Tight [⊢ to ⊢#] *)
(** In an inert environment, general typing ([ty_trm] [⊢]) can
    be reduced to tight typing ([ty_trm_t] [⊢#]).

    [inert G]           #<br>#
    [G ⊢ t: T]          #<br>#
    [――――――――――――――]    #<br>#
    [G ⊢# t: T] #<br># #<br>#

    and                 #<br># #<br>#
    [inert G]           #<br>#
    [G ⊢ S <: U]        #<br>#
    [――――――――――――――――]  #<br>#
    [G ⊢# S <: U]         *)
Lemma general_to_tight: forall G0,
  inert G0 ->
  (forall G t T,
     G ⊢ t : T ->
     G = G0 ->
     G ⊢# t : T) /\
  (forall G S U,
     G ⊢ S <: U ->
     G = G0 ->
     G ⊢# S <: U).
Proof.
  intros G0 Hi.
  apply ts_mutind; intros; subst;
    try solve [eapply sel_replacement; auto]; eauto.
  - specialize (H eq_refl).
    pose proof (invert_subtyp_rcd_t _ _ _ _ _ _ _ _ Hi e e0 H) as [Hg1 Hg2]. auto.
  - specialize (H eq_refl).
    pose proof (invert_subtyp_rcd_t _ _ _ _ _ _ _ _ Hi e e0 H) as [Hg1 Hg2]. auto.
  - specialize (H eq_refl). apply* invert_subtyp_all_t.
  - destruct* (sngl_replacement Hi (H eq_refl) (H0 eq_refl) r).
  - apply repl_swap in r. destruct* (sngl_replacement Hi (H eq_refl) (H0 eq_refl) r).
Qed.

(** The general-to-tight lemma, formulated for term typing. *)
Lemma general_to_tight_typing: forall G t T,
  inert G ->
  G ⊢ t : T ->
  G ⊢# t : T.
Proof.
  intros. apply* general_to_tight.
Qed.

(** If [Γ ⊢ p] then [Γ ⊢!!! p] *)
Lemma pt3_exists G p T :
  inert G ->
  G ⊢ trm_path p : T ->
  exists U, G ⊢!!! p : U.
Proof.
  intros Hi Hp. apply (general_to_tight_typing Hi) in Hp.
  apply tight_to_prec_exists in Hp as [? ?]; eauto.
Qed.

(** ** Proof Recipe *)
(** This tactic converts general typing of paths or values to as much precise typing
    as possible. *)
Ltac proof_recipe :=
  match goal with
  | [ Hg: ?G ⊢ _ : _,
      Hi: inert ?G |- _ ] =>
    apply (general_to_tight_typing Hi) in Hg;
    ((apply (replacement_closure Hi) in Hg) || (apply (replacement_closure_v Hi) in Hg));
    try lets Hok: (inert_ok Hi);
    try match goal with
        | [ Hr: ?G ⊢// _ : ∀(_) _,
            Hok: ok ?G |- _ ] =>
          destruct (repl_to_precise_typ_all Hi Hr) as [Spr [Tpr [Lpr [Hpr [Hspr1 Hspr2]]]]]
        | [ Hrv: ?G ⊢//v _ : μ _ |- _ ] =>
          apply (repl_to_invertible_obj Hi) in Hrv as [U' [Hrv Hrc]];
          apply (invertible_to_precise_obj Hi) in Hrv as [U'' [Hrv Hrc']];
          try match goal with
              | [ Hv: _ ⊢!v val_new ?T _ : μ ?U |- _ ] =>
                assert (T = U) as <- by (inversion Hv; subst*)
              end
        | [ Hrv: ?G ⊢//v _ : ∀(_) _ |- _ ] =>
           apply repl_val_to_precise_lambda in Hrv
              as [L1 [S1 [T1 [Hvpr [HS1 HS2]]]]]; auto
       end
  end.

(** If a path has a function type then its III-level precise type is
    also a function type that is a subtype of the former. *)
Lemma path_typ_all_to_precise: forall G p T U,
    inert G ->
    G ⊢ trm_path p : ∀(T) U ->
    (exists L T' U',
        G ⊢!!! p : ∀(T') U' /\
        G ⊢ T <: T' /\
        (forall y, y \notin L -> G & y ~ T ⊢ (open_typ y U') <: (open_typ y U))).
Proof.
  introv Hin Ht. proof_recipe. repeat eexists. eauto. apply* tight_to_general. eauto.
Qed.

(** If a value has a function type then the value is a function. *)
Lemma val_typ_all_to_lambda: forall G v T U,
    inert G ->
    G ⊢ trm_val v : ∀(T) U ->
    (exists L T' t,
        v = λ(T') t /\
        G ⊢ T <: T' /\
        (forall y, y \notin L -> G & y ~ T ⊢ (open_trm y t) : open_typ y U)).
Proof.
  introv Hin Ht. proof_recipe. inversions Hvpr.
  exists (L1 \u L \u (dom G)) S1 t. repeat split~.
  intros. assert (HL: y \notin L) by auto. assert (HL0: y \notin L1) by auto.
  specialize (HS2 y HL0).
  specialize (H2 y HL).
  eapply ty_sub; eauto. eapply narrow_typing in H2; eauto.
Qed.

Lemma invert_subtyp_all : forall G S1 T1 S2 T2,
    inert G ->
    G ⊢ ∀(S1) T1 <: ∀(S2) T2 ->
    G ⊢ S2 <: S1 /\ (exists L, forall x, x \notin L ->
       G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2).
Proof.
  introv H0 H.
  lets Hgt: (general_to_tight H0). destruct Hgt as [_ Hgt].
  apply Hgt in H; eauto 2.
  lets Ht: (invert_subtyp_all_t _ _ _ _ _ H0 H).
  destruct Ht as [Ht1 Ht2]. split; eauto 2.
  apply* tight_to_general.
Qed.

