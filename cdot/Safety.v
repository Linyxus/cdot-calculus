(** remove printing ~ *)

(** * Type Soundness *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List String.
Require Import Sequences.
Require Import Binding CanonicalForms Definitions GeneralToTight InvertibleTyping Lookup Narrowing
        Reduction PreciseTyping RecordAndInertTypes ReplacementTyping Replacement
        Subenvironments Substitution TightTyping Weakening.

Close Scope string_scope.

(** ** Safety wrt Term Reduction ⟼*)

Section Safety.

(** *** Reasoning about the precise type of objects *)

(** If the rhs of a type declaration is a signleton type [q.type] then
    [q] is well-typed *)
Lemma defs_typing_sngl_rhs z bs G ds T a q :
  z; bs; G ⊢ ds :: T ->
  record_has T {a ⦂ {{ q }}} ->
  exists T, G ⊢ trm_path q : T.
Proof.
  induction 1; intros Hr.
  - destruct D; inversions Hr. inversions H. eauto.
  - inversions Hr; auto. inversions H5. inversions H0. eauto.
Qed.

(** The [lookup_fields_typ] notation [x ==> T =bs=> U] denotes that
    if [T] is a recursive type then we can "look up" or "go down" a path
    [x.bs] inside of [T] yielding a type [U]. For example, if
    [T = μ(x: {a: μ(y: {b: μ(z: ⊤)})})] then
    [x ==> T =b,a=>⊤] *)
Reserved Notation "x '==>' T '=' bs '=>' U" (at level 40, T at level 20).

(** If [x ==> T =bs=> U] we will say that looking up the path
    [x.bs] in [T] yields [U].*)
Inductive lookup_fields_typ : var -> typ -> list trm_label -> typ -> Prop :=
| lft_empty : forall x T,
    x ==> T =nil=> T
| lft_cons : forall T bs U x a S,
    x ==> T =bs=> μ U ->
    record_has (open_typ_p (p_sel (avar_f x) bs) U) {a ⦂ S} ->
    x ==> T =a::bs=> S

where "x '==>' T '=' bs '=>' U" := (lookup_fields_typ x T bs U).

Hint Constructors lookup_fields_typ.

(** **** Properties of [lookup_fields_typ] *)

(** Looking up a path inside of an inert type yields an inert type *)
Lemma lft_inert x T bs U :
  inert_typ T ->
  x ==> T =bs=> μ U ->
  inert_typ (μ U).
Proof.
  intros Hi Hl. gen x U. induction bs; introv Hl; inversions Hl; eauto.
  specialize (IHbs _ _ H3).
  apply (inert_record_has _ IHbs) in H5 as [Hin | [? [=]]]. auto.
Qed.

(** The [lookup_fields_typ] relation is functional. *)
Lemma lft_unique x S bs T U :
  inert_typ S ->
  x ==> S =bs=> T ->
  x ==> S =bs=> U ->
  T = U.
Proof.
  intros Hi Hl1. gen U. induction Hl1; introv Hl2.
  - inversion Hl2; auto.
  - inversions Hl2. specialize (IHHl1 Hi _ H4) as [= ->].
    pose proof (lft_inert Hi Hl1). inversions H0.
    eapply unique_rcd_trm. apply* open_record_type_p. eauto. eauto.
Qed.

(** If looking up a path in [T] yields a function type then we cannot
    look up a longer path in [T] *)
Lemma lft_typ_all_inv x S bs cs V T U:
  inert_typ S ->
  x ==> S =bs=> ∀(T) U ->
  x ==> S =cs++bs=> V ->
  cs = nil.
Proof.
  gen x S bs T U V. induction cs; introv Hin Hl1 Hl2; auto.
  rewrite <- app_comm_cons in Hl2.
  inversions Hl2. specialize (IHcs _ _ _ _ _ _ Hin Hl1 H3) as ->.
  rewrite app_nil_l in H3.
  pose proof (lft_unique Hin Hl1 H3) as [= <-].
Qed.

(** If looking up a path in [T] yields a singleton type then we cannot
    look up a longer path in [T] *)
Lemma lft_typ_sngl_inv x S bs p cs V :
  inert_typ S ->
  x ==> S =bs=> {{ p }} ->
  x ==> S =cs++bs=> V ->
  cs = nil.
Proof.
  gen x S bs p V. induction cs; introv Hin Hl1 Hl2; auto.
  rewrite <- app_comm_cons in Hl2.
  inversions Hl2. specialize (IHcs _ _ _ _ _ Hin Hl1 H3) as ->.
  rewrite app_nil_l in H3.
  pose proof (lft_unique Hin Hl1 H3) as [= <-].
Qed.

(** If the definitions [ds] that correspond to a path [p] (here, [z.bs])
    have a type [Tᵖ], and looking up the path [x.cs] for some [x]
    in [Tᵖ] yields a type [μ(U)] then nested in [ds] are some definitions
    [ds'] such that under the path [p.cs], [ds'] can be typed with [U]#<sup>p.cs</sup>#. *)
Lemma lfs_defs_typing : forall cs z bs G ds T S U,
  z; bs; G ⊢ ds :: open_typ_p (p_sel (avar_f z) bs) T ->
  inert_typ S ->
  z ==> S =bs=> μ T ->
  z ==> S =cs++bs=> μ U ->
  exists ds', z; (cs++bs); G ⊢ ds' :: open_typ_p (p_sel (avar_f z) (cs++bs)) U.
Proof.
  induction cs; introv Hds Hin Hl1 Hl2.
  - rewrite app_nil_l in*. pose proof (lft_unique Hin Hl1 Hl2) as [= ->]. eauto.
  - rewrite <- app_comm_cons in *. inversions Hl2.
    specialize (IHcs _ _ _ _ _ _ _ Hds Hin Hl1 H3) as [ds' Hds'].
    pose proof (record_has_ty_defs Hds' H5) as [d [Hdh Hd]].
    inversions Hd. eauto.
Qed.

(** Suppose the declaration [d] corresponding to a path [z.bs]
    has type [{b: V}], and that [V=...∧ {a: q.type} ∧...].
    Then [q] is well-typed.
    *)
Lemma def_typing_rhs z bs G d a q U S cs T b V :
  z; bs; G ⊢ d : {b ⦂ V} ->
  inert_typ S ->
  z ==> S =bs=> μ T ->
  record_has (open_typ_p (p_sel (avar_f z) bs) T) {b ⦂ V} ->
  z ==> S =cs++b::bs=> μ U ->
  record_has (open_typ_p (p_sel (avar_f z) (cs++b::bs)) U) {a ⦂ {{ q }}} ->
  exists W, G ⊢ trm_path q : W.
Proof.
  intros Hds Hin Hl1 Hrd Hl2 Hr. inversions Hds.
  - Case "def_all"%string.
    eapply lft_cons in Hl1; eauto.
    pose proof (lft_typ_all_inv _ Hin Hl1 Hl2) as ->.
    rewrite app_nil_l in *.
    pose proof (lft_unique Hin Hl1 Hl2) as [=].
  - Case "def_new"%string.
    pose proof (ty_def_new _ _ eq_refl H2 H7 H8).
    assert (z ==> S =b::bs=> μ T0) as Hl1'. {
        eapply lft_cons. eauto. eauto.
    }
    pose proof (lfs_defs_typing _ H7 Hin Hl1' Hl2) as [ds' Hds'].
    pose proof (record_has_ty_defs Hds' Hr) as [d [Hdh Hd]].
    inversions Hd. eauto.
  - Case "def_path"%string.
    eapply lft_cons in Hl1; eauto.
    pose proof (lft_typ_sngl_inv _ Hin Hl1 Hl2) as ->.
    rewrite app_nil_l in *.
    pose proof (lft_unique Hin Hl1 Hl2) as [=].
Qed.

(** The same applies to the case where we type multiple declarations that contain
    [{b: V}] as a record. *)
Lemma defs_typing_rhs z bs G ds T a q U S cs T' b V :
  z; bs; G ⊢ ds :: T ->
  inert_typ S ->
  z ==> S =bs=> μ T' ->
  record_has (open_typ_p (p_sel (avar_f z) bs) T') {b ⦂ V} ->
  record_has T {b ⦂ V} ->
  z ==> S =cs++b::bs=> μ U ->
  record_has (open_typ_p (p_sel (avar_f z) (cs++b::bs)) U) {a ⦂ {{ q }}} ->
  exists V, G ⊢ trm_path q : V.
Proof.
  intros Hds Hin Hl1 Hr1 Hr2 Hl2 Hr.
  gen S a q U cs T' b V. dependent induction Hds; introv Hin; introv Hl1; introv Hl2; introv Hr Hr1 Hr2.
  - inversions Hr2. eapply def_typing_rhs; eauto.
  - specialize (IHHds _ Hin _ _ _ _ _ Hl1 _ Hl2 Hr _ Hr1).
    inversions Hr2; auto.
    inversions H4. clear IHHds.
    eapply def_typing_rhs; eauto.
Qed.

(** Looking up a path inside of a variable [x]'s environment type,
    given that we can type the path [x.bs] *)
Lemma pf_sngl_to_lft G x T bs W V :
  inert (G & x ~ μ T) ->
  G & x ~ (μ T) ⊢! p_sel (avar_f x) bs : W ⪼ V ->
  bs = nil \/
  exists b c bs' bs'' U V,
    bs = c :: bs' /\
    bs = bs'' ++ b :: nil /\
    x ==> (μ T) =bs'=> (μ U) /\
    record_has (open_typ x T) {b ⦂ V} /\
    record_has (open_typ_p (p_sel (avar_f x) bs') U) {c ⦂ W}.
Proof.
  intros Hi Hp. dependent induction Hp; eauto.
  simpl_dot. right. specialize (IHHp _ _ _ _ Hi JMeq_refl eq_refl)
    as [-> | [b [c [bs' [bs'' [S [V [-> [Hl [Hl2 [Hr1 Hr2]]]]]]]]]]].
  - Case "pf_bind"%string.
    pose proof (pf_binds Hi Hp) as ->%binds_push_eq_inv. repeat eexists; eauto.
    simpl. rewrite app_nil_l. eauto. rewrite open_var_typ_eq. eapply pf_record_has_T; eauto.
    eapply pf_record_has_T; eauto.
  - Case "pf_fld"%string.
    pose proof (pf_bnd_T2 Hi Hp) as [W ->].
    rewrite Hl.
    exists b a. eexists. exists (a :: bs''). repeat eexists; eauto.
    rewrite <- Hl. econstructor; eauto. rewrite <- Hl.
    apply* pf_record_has_T.
Qed.

(** Every value of type [T] has a precise type that is inert, well-formed,
    and is a subtype of [T]. *)
Lemma val_typing G x v T :
  inert G ->
  wf G ->
  G ⊢ trm_val v : T ->
  x # G ->
  exists T', G ⊢!v v : T' /\
        G ⊢ T' <: T /\
        inert_typ T' /\
        wf (G & x ~ T').
Proof.
  intros Hi Hwf Hv Hx. dependent induction Hv; eauto.
  - exists (∀(T) U). repeat split*. constructor; eauto. introv Hp.
    assert (binds x (∀(T) U) (G & x ~ ∀(T) U)) as Hb by auto. apply pf_bind in Hb; auto.
    destruct bs as [|b bs].
    + apply pf_binds in Hp; auto. apply binds_push_eq_inv in Hp as [=].
    + apply pf_sngl in Hp as [? [? [=]%pf_binds%binds_push_eq_inv]]; auto.
  - exists (μ T). assert (inert_typ (μ T)) as Hin. {
      lets Hv: (ty_new_intro_p T ds H H0).
      apply* pfv_inert.
    }
    repeat split*. pick_fresh z. assert (z \notin L) as Hz by auto.
    specialize (H z Hz). assert (z # G) as Hz' by auto.
    constructor*. introv Hp.
    assert (exists W, G & x ~ (μ T) ⊢ trm_path q : W) as [W Hq]. {
      assert (inert (G & x ~ μ T)) as Hi' by eauto.
      pose proof (pf_sngl_to_lft Hi' Hp) as [-> | [b [c [bs' [bs'' [U [V [-> [Hl1 [Hl2 [Hr1 Hr2]]]]]]]]]]].
      { apply pf_binds in Hp as [=]%binds_push_eq_inv; auto. }
      assert (x; nil; G & x ~ open_typ x T ⊢ open_defs x ds :: open_typ x T)
        as Hdx%open_env_last_defs. {
        apply rename_defs with (x:=z); auto.
      }
      destruct bs'' as [|bs'h bs't].
      + rewrite app_nil_l in *. inversions Hl1. inversions Hl2.
        eapply defs_typing_sngl_rhs. apply Hdx. rewrite* open_var_typ_eq.
      + rewrite <- app_comm_cons in Hl1. inversions Hl1.
        eapply defs_typing_rhs.
        apply Hdx.
        apply Hin.
        eauto.
        rewrite open_var_typ_eq in Hr1. apply Hr1.
        auto.
        apply Hl2.
        apply Hr2.
      + auto.
    }
    apply pt3_exists in Hq as [? Hq'%pt2_exists]; auto.
  - specialize (IHHv _ Hi Hwf eq_refl Hx). destruct_all. eexists; split*.
Qed.

(** Helper tactics for proving Preservation *)

Ltac lookup_eq :=
  match goal with
  | [Hl1: ?s ⟦ _ ⤳* defv ?t1 ⟧,
     Hl2: ?s ⟦ _ ⤳* defv ?t2 ⟧ |- _] =>
     apply (lookup_func Hl1) in Hl2; inversions Hl2
  end.

Ltac invert_red :=
  match goal with
  | [Hr: (_, _) ⟼ (_, _) |- _] => inversions Hr
  end.

Ltac solve_IH :=
  match goal with
  | [IH: _ ⫶ _ ->
         inert _ ->
         wf _ ->
         forall t', (_, _) ⟼ (_, _) -> _,
       Wt: _ ⫶ _,
       In: inert _,
       Wf: wf _,
       Hr: (_, _) ⟼ (_, ?t') |- _] =>
    specialize (IH Wt In Wf t' Hr); destruct_all
  end;
  match goal with
  | [Hi: _ & ?G' ⊢ _ : _ |- _] =>
    exists G'; repeat split; auto
  end.

Ltac solve_let :=
  invert_red; solve_IH; fresh_constructor; eauto; apply* weaken_rules.

Lemma matched_case_typing: forall γ G p q r A T0 T ds,
    inert G ->
    wf G ->
    γ ⫶ G ->
    G ⊢ trm_path p : T ->
    γ ⟦ p ⤳ defv (ν [q ↘ A](T0) ds) ⟧ ->
    γ ⟦ defp (open_path_p p q) ⤳* defp r ⟧ ->
    G ⊢ trm_path p : r ↓ A.
Proof.
  introv Hin Hwf Hwt Hp Hm1 Hm2.
  apply star_one in Hm1.
  lets Hcf: (canonical_forms_obj Hin Hwf Hwt Hm1 Hp).
  lets Hx: (path_sel_implies_typed_path Hin Hcf). destruct Hx as [U Hxp].
  assert (Hx: G ⊢ trm_path (open_path_p p q) : typ_rcd {A >: U <: U}) by apply* precise_to_general3.
  assert (Hrl: γ ⟦ defp r ⤳* defp r ⟧) by apply star_refl.
  lets Hrppp: (lookup_pres Hin Hwf Hwt Hxp Hm2). destruct Hrppp as [U0 Hrppp].
  lets Hrt: (precise_to_general3 Hrppp).
  lets Hd: (path_lookup_implies_sngl_typing Hin Hwf Hwt Hx Hrt Hm2 Hrl).
  apply ty_sub with (T:=open_path_p p q ↓ A); auto.
  apply subtyp_sngl_pq with (p:=(open_path_p p q)) (q:=r) (U:=U0); auto.
  apply repl_intro_path_sel.
Qed.

Lemma subtyp_and_extend_r : forall G S T U,
    G ⊢ S <: T ->
    G ⊢ S ∧ U <: T ∧ U.
Proof.
  introv Hsub. apply subtyp_and2.
  - eapply subtyp_trans. apply subtyp_and11. auto.
  - apply subtyp_and12.
Qed.

Lemma subtyp_and_extend_l : forall G S T U,
    G ⊢ T <: U ->
    G ⊢ S ∧ T <: S ∧ U.
Proof.
  introv Hsub. apply subtyp_and2.
  - apply subtyp_and11.
  - eapply subtyp_trans. apply subtyp_and12. auto.
Qed.

Lemma ty_lookup_trans : forall G γ p q T,
    inert G ->
    wf G ->
    γ ⫶ G ->
    γ ⟦ p ⤳ defp q ⟧ ->
    G ⊢ trm_path p : T ->
    G ⊢ trm_path q : T.
Proof.
  introv Hin Hwf Hwt Hl Hp.
  lets Hpp: (pt3_exists Hin Hp). destruct Hpp as [U Hpp].
  lets Hps: (lookup_step_sngl Hin Hwf Hwt Hpp Hl).
  lets Hqp: (lookup_step_pres Hin Hwf Hwt Hpp Hl). destruct Hqp as [U' Hqp].
  apply precise_to_general3 in Hqp.
  apply ty_sngl with (q := p).
  - apply ty_sub with (T := {{q}}). apply* ty_self.
    eapply subtyp_sngl_qp. exact Hps. exact Hqp. apply repl_intro_sngl.
  - auto.
Qed.

(** **** Preservation (Theorem 4.2) *)
(** If a term [γ|t] has type [T] and reduces to [γ'|t'] then the latter has
    the same type [T] under an extended environment that is inert, well-typed,
    and well-formed. *)
Lemma preservation: forall G γ t γ' t' T,
    γ ⫶ G ->
    inert G ->
    wf G ->
    (γ, t) ⟼ (γ', t') ->
    G ⊢ t : T ->
    exists G', inert G' /\
          wf (G & G') /\
          γ' ⫶ G & G' /\
          G & G' ⊢ t' : T.
Proof.
  introv Hwt Hi Hwf Hred Ht. gen t'.
  induction Ht; intros; try solve [invert_red].
  - invert_red. exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    apply* ty_lookup_trans.
  - Case "ty_all_elim"%string.
    match goal with
    | [Hp: _ ⊢ trm_path _ : ∀(_) _ |- _] =>
        pose proof (canonical_forms_fun Hi Hwf Hwt Hp) as [L [T' [t [Hl [Hsub Hty]]]]];
        invert_red
    end.
    + apply star_one in H1. lookup_eq.
      exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
      pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
      eapply subst_var_path; eauto. eauto. eauto.
    + (* reducing p in p q *)
      specialize (IHHt1 Hwt Hi Hwf _ H0). destruct IHHt1 as [G' [Hi' [Hwf' [Hwt' Ht']]]].
      exists G'. repeat split; auto. apply ty_all_elim with (S:=S). auto.
      apply* weaken_ty_trm.
    + (* reducing q in p q *)
      specialize (IHHt2 Hwt Hi Hwf _ H5). destruct IHHt2 as [G' [Hi' [Hwf' [Hwt' Ht']]]].
      exists G'. repeat split; auto. inversion H5. subst.
      lets Hqp: (pt3_exists Hi Ht2). destruct Hqp as [U Hqp].
      lets Hqs: (lookup_step_sngl Hi Hwf Hwt Hqp H0). apply* weaken_ty_trm.
      lets Hp': (ty_lookup_trans Hi Hwf Hwt H0 Ht2). auto.
      apply ty_sub with (T := open_typ_p p' T).
      * apply ty_all_elim with (S := S). auto. auto.
      * eapply subtyp_sngl_qp_repeat. exact Hqs. exact Hp'. apply repl_comp_open.
  - invert_red. exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    apply* ty_lookup_trans.
  - invert_red. exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    apply* ty_lookup_trans.
  - Case "ty_let"%string.
    destruct t; try solve [solve_let].
     + SCase "[t = (let x = v in u)] where v is a value"%string.
      repeat invert_red.
      match goal with
        | [Hn: ?x # ?s |- _] =>
          pose proof (well_typed_notin_dom Hwt Hn) as Hng
      end.
      pose proof (val_typing Hi Hwf Ht Hng) as [V [Hv [Hs [Hin Hwf']]]].
      exists (x ~ V). repeat split; auto.
      ** rewrite <- concat_empty_l. constructor~.
      ** constructor~. apply (precise_to_general_v Hv).
      ** rewrite open_var_trm_eq. eapply subst_fresh_var_path with (L:=L \u dom G \u \{x}). apply* ok_push.
         intros. apply* weaken_rules. apply ty_sub with (T:=V); auto. apply* weaken_subtyp.
    + SCase "[t = (let x = p in u)] where a is p variable"%string.
      repeat invert_red.
      * exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
        apply* subst_fresh_var_path.
      * exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
        fresh_constructor. apply* ty_lookup_trans.
  - Case "ty_case"%string.
    inversion Hred; subst.
    + (* matched *)
      lets Hcf: (matched_case_typing Hi Hwf Hwt Ht1 H10 H11).
      exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
      eapply subst_fresh_var_path. eauto. apply H.
      apply ty_and_intro.
      * eapply ty_self. exact Hcf.
      * apply Hcf.
    + (* unmatched: tag mismatch *)
      subst.
      exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    + (* unmatched: func value *)
      subst.
      exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    + (* reducing scrutinee path *)
      inversions H2.
      exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
      fresh_constructor. apply* ty_lookup_trans. exact Ht2.
      apply~ narrow_typing. apply~ subenv_last.
      apply subtyp_and_extend_r.
      lets Hpppp: (pt3_exists Hi Ht1). destruct Hpppp as [U0 Hpppp].
      lets Hlpp': (lookup_step_sngl Hi Hwf Hwt Hpppp H3).
      lets Hp': (ty_lookup_trans Hi Hwf Hwt H3 Ht1).
      eapply subtyp_sngl_qp. exact Hlpp'. exact Hp'. apply repl_intro_sngl.
    + (* reducing pattern path *)
      inversions H10.
      exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
      fresh_constructor. exact Ht1. apply* ty_lookup_trans.
      apply~ narrow_typing. apply~ subenv_last.
      apply subtyp_and_extend_l.
      lets Hqppp: (pt3_exists Hi Ht2). destruct Hqppp as [U0 Hqppp].
      lets Hlpp': (lookup_step_sngl Hi Hwf Hwt Hqppp H2).
      lets Hr': (ty_lookup_trans Hi Hwf Hwt H2 Ht2).
      eapply subtyp_sngl_qp. exact Hlpp'. exact Hr'. apply repl_intro_path_sel.
  - invert_red.
    exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    apply~ ty_lookup_trans. eauto. eauto. apply* ty_sngl.
  - invert_red.
    exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    apply~ ty_lookup_trans. eauto. eauto. apply* ty_self.
  - invert_red.
    exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    apply~ ty_lookup_trans. eauto. eauto. apply* ty_path_elim.
  - invert_red.
    exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    apply~ ty_lookup_trans. eauto. eauto. apply* ty_rec_intro.
  - invert_red.
    exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    apply~ ty_lookup_trans. eauto. eauto.
  - invert_red.
    exists (@empty typ). rewrite concat_empty_r. repeat split; auto.
    apply~ ty_lookup_trans. eauto. eauto. constructor*.
  - Case "ty_sub"%string.
    solve_IH.
    match goal with
    | [Hs: _ ⊢ _ <: _,
       Hg: _ & ?G' ⊢ _: _ |- _] =>
      apply weaken_subtyp with (G2:=G') in Hs;
      eauto
    end.
Qed.

(** **** Progress (Theorem 4.3) *)
(** Any well-typed term is either in normal form (i.e. a path or value) or can
    take a reduction step. *)
Lemma progress: forall G γ t T,
    inert G ->
    wf G ->
    γ ⫶ G ->
    G ⊢ t : T ->
    norm_form γ t \/ exists γ' t', (γ, t) ⟼ (γ', t').
Proof.
  introv Hi Hwf Hwt Ht.
  induction Ht; eauto.
  - apply ty_var in H. apply (pt3_exists Hi) in H as [U Hppp].
    apply (typ_to_lookup3 Hi Hwf Hwt) in Hppp as Hl. destruct Hl as [t Hl].
    destruct t; eauto.
  - specialize (IHHt1 Hi Hwf Hwt).
    destruct IHHt1.
    + inversions H.
      pose proof (canonical_forms_fun Hi Hwf Hwt Ht1). destruct_all.
      right*. apply star_one in H0 as Hl. lookup_eq.
      specialize (IHHt2 Hi Hwf Hwt). destruct IHHt2.
      * repeat eexists. eapply red_app. exact H0. inversions H. exact H6.
      * destruct_all. inversions H.
        repeat eexists. apply red_ctx_app2. eexists. exact H0.
        apply red_resolve. exact H5.
    + right*. destruct_all. inversions H.
      repeat eexists. apply red_ctx_app1.
      apply red_resolve. exact H1.
  - apply ty_new_elim in Ht.
    apply (pt3_exists Hi) in Ht as Hpppp. destruct Hpppp as [U Hpppp].
    apply (typ_to_lookup3 Hi Hwf Hwt) in Hpppp as Hl. destruct Hl as [t Hl].
    destruct t.
    + right*.
    + left*.
  - apply ty_rcd_intro in Ht.
    apply (pt3_exists Hi) in Ht as Hpppp. destruct Hpppp as [U Hpppp].
    apply (typ_to_lookup3 Hi Hwf Hwt) in Hpppp as Hl. destruct Hl as [t Hl].
    destruct t.
    + right*.
    + left*.
  - Case "ty_let"%string.
    destruct t; eauto.
    + right. pick_fresh z. exists (γ & z ~ v). eauto.
    + right. specialize (IHHt Hi Hwf Hwt) as [Hn | [γ' [t' Hr]]].
      { inversion Hn. } eauto.
    + right. specialize (IHHt Hi Hwf Hwt) as [Hn | [γ' [t' Hr]]].
      { inversion Hn. } eauto.
    + specialize (IHHt Hi Hwf Hwt) as [Hn | [γ' [t' Hr]]].
      { right. inversion Hn. subst. destruct_all. repeat eexists. apply red_let_path.
        exists x. auto.
      } eauto.
    + right. specialize (IHHt Hi Hwf Hwt) as [Hn | [γ' [t' Hr]]].
      { inversion Hn. } eauto.
  - Case "ty_case"%string.
    right.
    apply (pt3_exists Hi) in Ht1 as Hpppp. destruct Hpppp as [U0 Hpppp].
    apply (typ_to_lookup3 Hi Hwf Hwt) in Hpppp as Hl. destruct Hl as [t Hl].
    destruct t.
    + repeat eexists. apply red_ctx_case1. eauto.
    + apply (pt3_exists Hi) in Ht2 as Hqppp. destruct Hqppp as [U1 Hqppp].
      apply (typ_to_lookup3 Hi Hwf Hwt) in Hqppp as Hl2. destruct Hl2 as [t' Hl2].
      destruct t'.
      * repeat eexists. apply red_ctx_case2. exists v. auto. eauto.
      * destruct v.
        {
          destruct (classicT (t = A)).
          { subst. apply star_one in Hl as Hll.
            lets Hcf: (canonical_forms_obj Hi Hwf Hwt Hll Ht1).
            lets Hcfp0: (resolve_typeable_path_sel Hi Hwf Hwt Hcf).
            destruct Hcfp0 as [v [r0 [Hp0r Hrv]]].
            destruct (classicT (r0 = q)).
            - subst. repeat eexists. eapply red_case_match.
              eexists. exact Hrv.
              exact Hl. exact Hp0r.
            - repeat eexists. eapply red_case_else.
              eexists. eauto. eexists. eauto. eauto. eauto. left*.
          }
          {
            apply star_one in Hl as Hll.
            lets Hcf: (canonical_forms_obj Hi Hwf Hwt Hll Ht1).
            lets Hcfp0: (resolve_typeable_path_sel Hi Hwf Hwt Hcf).
            destruct Hcfp0 as [v [r0 [Hp0r Hrv]]].
            repeat eexists. eapply red_case_else.
            eexists. eauto. eexists. eauto. eauto. eauto. right*.
          }
        }
        {
          repeat eexists. eapply red_case_lambda. eauto.
        }
  - lets Ht: (ty_path_elim a Ht1 Ht2).
    apply (pt3_exists Hi) in Ht as Hpppp. destruct Hpppp as [U0 Hpppp].
    apply (typ_to_lookup3 Hi Hwf Hwt) in Hpppp as Hl. destruct Hl as [t Hl].
    destruct t.
    + right*.
    + left*.
Qed.

(** *** Safety *)

(** If a term [γ|t] has type [T] and reduces in a finite number of steps
    to [γ'|t'] then the latter is either in normal form and has type [T],
    or it can take a further step to a term [γ''|t''], where [t''] also
    has type [T]. *)
Lemma safety_helper G t1 t2 γ1 γ2 T :
  G ⊢ t1 : T ->
  inert G ->
  wf G ->
  γ1 ⫶ G ->
  (γ1, t1) ⟼* (γ2, t2) ->
  (exists γ3 t3 G3, (γ2, t2) ⟼ (γ3, t3) /\
               G3 ⊢ t3 : T /\
               γ3 ⫶ G3 /\
               wf G3 /\
               inert G3) \/
  (exists G2, norm_form γ2 t2 /\ G2 ⊢ t2 : T /\
               γ2 ⫶ G2 /\
               wf G2 /\
               inert G2).
Proof.
  intros Ht Hi Hwf Hwt Hr. gen G T. dependent induction Hr; introv Hi Hwf Hwt; introv Ht.
  - pose proof (progress Hi Hwf Hwt Ht) as [Hn | [γ' [t' Hr]]].
    right. exists G. eauto.
    left. pose proof (preservation Hwt Hi Hwf Hr Ht) as [G' [Hi' [Hwf' [Hwt' Ht']]]].
    exists γ' t' (G & G'). repeat split*. apply* inert_concat.
  - destruct b as [γ12 t12]. specialize (IHHr _ _ _ _ eq_refl eq_refl).
    pose proof (preservation Hwt Hi Hwf H Ht) as [G' [Hi' [Hwf' [Hwt' Ht']]]].
    specialize (IHHr _ (inert_concat Hi Hi' (well_typed_to_ok_G Hwt'))).
    eauto.
Qed.

Definition diverges := infseq red.
Definition cyclic_path γ p := infseq (lookup_step γ) (defp p).

(** **** Type Soundness (Theorem 4.1) *)
(** Reducing any well-typed program (i.e. term that can be typed in an empty context)
    results either
    - in a normal form (i.e. path or value) in a finite number of steps,
    - in an infinite reduction sequence. *)
Theorem safety t T :
  empty ⊢ t : T ->
  diverges (empty, t) \/
  (exists γ u G, (empty, t) ⟼* (γ, u) /\
            norm_form γ u /\
            G ⊢ u : T /\
            γ ⫶ G /\
            wf G /\
            inert G).
Proof.
  intros Ht.
  pose proof (infseq_or_finseq red (empty, t)) as [? | [[s u] [Hr Hn]]]; eauto.
  right. epose proof (safety_helper Ht inert_empty wfe_empty well_typed_empty Hr)
    as [[γ' [t' [G' [Hr' [Ht' Hwt]]]]] | [G [Hn' [Ht' [Hwt [Hwf Hi]]]]]].
  - false* Hn.
  - repeat eexists; eauto.
Qed.

End Safety.

(** ** Safety wrt Path Lookup ⤳ *)
Section PathSafety.

  (** Looking up any well-typed path in the value environment results either
    - in a value in a finite number of steps, or
    - in an infinite sequence of lookup operations, i.e. the path is cyclic *)
  Lemma path_safety G p T γ :
    inert G ->
    wf G ->
    γ ⫶ G ->
    G ⊢ trm_path p : T ->
    cyclic_path γ p \/ exists v, γ ⟦ defp p ⤳* defv v ⟧.
  Proof.
    intros Hi Hwf Hwt Hp.
    proof_recipe. apply repl_prec_exists in Hp as [U Hp].
    pose proof (infseq_or_finseq (lookup_step γ) (defp p)) as [? | [t [Hl Hirr]]]; eauto.
    right. destruct t; eauto.
    pose proof (lookup_pres Hi Hwf Hwt Hp Hl) as [S Hq].
    pose proof (typ_to_lookup3 Hi Hwf Hwt Hq) as [t Hl'].
    false* Hirr.
  Qed.

End PathSafety.


(** ** Extended Safety *)

Section ExtendedSafety.

  (** Extended reduction relation (combines term reduction ⟼ and lookup ⤳) *)
  Reserved Notation "t '↠' u" (at level 40).

  Inductive extended_red : sta * trm -> sta * trm -> Prop :=
  | er_red γ γ' t t':
      (γ, t) ⟼ (γ', t') ->
      (γ, t) ↠ (γ', t')
  | er_lookup γ p t:
      γ ⟦ p ⤳ t ⟧ ->
      (γ, trm_path p) ↠ (γ, deftrm t)
  where "t ↠ u" := (extended_red t u).

  Hint Constructors extended_red.

  (** Reflexive transitive closure of extended reduction *)
  Notation "t '↠*' u" := ((star extended_red) t u) (at level 40).

  (** Divergence of extended reduction *)
  Definition diverges' := infseq extended_red.

  Lemma extend_infseq γ t γ' t' :
        diverges' (γ, t) ->
        (γ', t') ↠* (γ, t) ->
        diverges' (γ', t').
  Proof.
    intros Hinf Hr. dependent induction Hr; auto.
    destruct b. specialize (IHHr _ _ _ _ Hinf eq_refl eq_refl).
    econstructor. apply H. auto.
  Qed.

  Lemma map_red_extend γ t γ' t':
    (γ, t) ⟼* (γ', t') ->
    (γ, t) ↠* (γ', t').
  Proof.
    intros Hr. dependent induction Hr; try destruct b; eauto.
  Qed.

  Lemma map_lookup_extend γ t t':
    star (lookup_step γ) t t' ->
    (γ, deftrm t) ↠*(γ, deftrm t').
  Proof.
    intros Hr. dependent induction Hr; eauto.
    destruct a. eapply star_trans. apply star_one. apply* er_lookup.
    auto. inversion H.
  Qed.

  (** **** Extended Soundness (Theorem 5.2) *)
  (** Reducing any well-typed program (i.e. term that can be typed in an empty context)
      using the extended reduction relation (that includes term reduction and path lookup)
      results either
      - in a value in a finite number of steps, or
      - in an infinite reduction sequence. *)
  Theorem extended_safety t T :
    empty ⊢ t : T ->
    diverges' (empty, t) \/ exists γ v, (empty, t) ↠* (γ, trm_val v).
  Proof.
    intros Ht. pose proof (safety Ht) as [Hd | [γ [u [G [Hr [Hn [Hu [Hwt [Hwf Hi]]]]]]]]].
    - Case "term diverges"%string.
      left. inversions Hd. inversions H0. apply infseq_step with (b:=b); destruct b; auto.
      destruct b0. econstructor. apply er_red. apply H1.
      apply infseq_coinduction_principle with
          (X := fun st => exists γ1 t1,
                    st = (γ1, t1) /\ infseq red (γ1, t1)).
      intros st [γ' [t' [-> Hinf]]].
      + inversions Hinf. destruct b. eexists; split*.
      + eauto.
    - Case "term evaluates to normal form"%string.
      inversions Hn.
      + SCase "term evaluates to a path"%string.
        pose proof (path_safety Hi Hwf Hwt Hu) as [Hd | Hn].
        * SSCase "path lookup diverges"%string.
          left. assert (infseq extended_red (γ, trm_path p)). {
            clear Hwf Hwt Hr Hu Ht Hi G T t.
            apply infseq_coinduction_principle with
                (X := fun st => exists u, st = (γ, deftrm u) /\ infseq (lookup_step γ) u).
            + intros st [du [-> Hinf]].
              inversions Hinf. destruct b, du; try solve [inversion H].
              eexists; split*; apply* er_lookup.
              inversions H0. inversion H1. false* lookup_irred.
              false* lookup_irred.
            + eexists. split*. simpl. auto.
          }
          assert (star extended_red (empty, t) (γ, trm_path p)). {
            apply* map_red_extend.
          }
          apply* extend_infseq.
        * SSCase "path looks up to value"%string.
          destruct Hn as [v Hv]. right. exists γ v.
          eapply star_trans. eapply map_red_extend. eauto.
          apply map_lookup_extend in Hv. eauto.
      + SCase "term evaluates to a value"%string.
        right. exists γ v. apply* map_red_extend.
  Qed.

End ExtendedSafety.
