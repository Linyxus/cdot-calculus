(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** * Canonical Forms *)
(** This module proves the Canonical Forms Lemmas, which allow us
    to retrieve the shape of a value given its type. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List String.
Require Import Binding Definitions GeneralToTight InvertibleTyping Lookup Narrowing
        PreciseTyping Replacement ReplacementTyping RecordAndInertTypes Substitution
        Subenvironments TightTyping Weakening.
Require Import Sequences.

(** Converting a stable term to a general term *)
Definition deftrm t : trm :=
  match t with
  | defp p => trm_path p
  | defv v => trm_val v
  end.

(** If a tag is typable, then its encapsulating path is typable. *)
Lemma typable_tag : forall G p A q r T,
    inert G ->
    G ⊢ trm_val (val_tag p A q r) : T ->
    (exists U, G ⊢ trm_path q : U).
Proof.
  introv Hi Hg.
  apply (general_to_tight_typing Hi) in Hg.
  dependent induction Hg.
  - specialize (IHHg _ _ _ _ Hi eq_refl). exact IHHg.
  - apply tight_to_general in Hg1. eexists. eauto.
Qed.

(** ** Type preservation for path lookup *)

(** If the record [{a = t}] has type [{a: V}] then [t] is either
    - a function that has type [V],
    - an object [ν(U)ds] that has type [μ(U)], and [V=μ(U)], or
    - a well-typed path [q], and [V=q.type] *)
Lemma object_typing G x bs ds T a t V :
  inert G ->
  x; bs; G ⊢ ds :: T ->
  defs_has ds {a := t} ->
  record_has T {a ⦂ V} ->
  (exists U u, t = defv (λ(U) u) /\ G ⊢ deftrm t : V) \/
  (exists U ds', t = defv (ν(U) ds') /\
            x; (a :: bs); G ⊢ open_defs_p (p_sel (avar_f x) (a :: bs)) ds' ::
                                 open_typ_p (p_sel (avar_f x) (a :: bs)) U /\
            V = μ U) \/
  (exists q S, t = defp q /\ V = {{ q }} /\ G ⊢ trm_path q : S) \/
  (exists p A q q1 S, t = defv (val_tag p A q q1) /\ V = typ_tag q /\ G ⊢ trm_path q : S /\ G ⊢ deftrm t : V).
Proof.
  intros Hi Hds Hdh Hr.
  destruct (record_has_ty_defs Hds Hr) as [? [Hdh' Hdt]].
  destruct (defs_invert_trm Hdt) as [t' ->].
  pose proof (defs_has_inv Hdh Hdh') as <-. destruct t as [q | v]; simpl in *.
  - inversion* Hdt.
  - destruct v.
    * right. left. inversions Hdt.
      simpl in *. repeat eexists; auto.
    * left. inversions Hdt. eauto.
    * inversion Hdt. subst. right. right. right.
      destruct (typable_tag Hi H3). repeat eexists; eauto.
Qed.

(** If [p] looks up to [t] in a value environment, [p]'s environment type
    is [T] and [p]'s precise type is [U], then either [t] is
    - a function that has type [T],
    - an object [ν(S)ds] that has type [μ(S)], and [T] and [μ(s)] are equivalent, or
    - a well-typed path [q], and [T] is equivalent to [q.type] *)
Lemma lookup_step_preservation_prec1: forall G γ p px pbs t T U,
    inert G ->
    wf G ->
    γ ⫶ G ->
    γ ⟦ p ⤳ t ⟧ ->
    G ⊢! p : T ⪼ U ->
    p = p_sel (avar_f px) pbs ->
    (exists S u, t = defv (λ(S) u) /\ G ⊢ deftrm t : T) \/
    (exists S ds W T' G1 G2 pT,
        t = defv (ν(S) ds) /\
        T = μ T' /\
        G = G1 & px ~ pT & G2 /\
        px ; pbs; G ⊢ open_defs_p p ds :: open_typ_p p S /\
        G1 ⊩ S ⟿ W ⬳ T') \/
    (exists q r r' G1 G2 pT,
        t = defp q /\
        T = {{ r }} /\
        G = G1 & px ~ pT & G2 /\
        (r = r' \/ G1 ⊢!!! r : {{ r' }}) /\ (q = r' \/ G1 ⊢!!! q : {{ r' }})) \/
    (exists p1 A q q1 r r' G1 G2 pT,
        t = defv (val_tag p1 A q q1) /\
        T = typ_tag r /\
        G ⊢ deftrm t : (typ_tag q) /\
        G = G1 & px ~ pT & G2 /\
        G1 ⊩ r ⟿' r' ⬳ q).
Proof.
  introv Hi Hwf Hwt. gen p px pbs t T U.
  (* induction on well-formedness **)
  induction Hwt; introv Hs Hp Heq.
  - Case "G is empty"%string.
    false* lookup_empty.
  - Case "G is not empty"%string.
    pose proof (typed_paths_named (precise_to_general Hp)) as [px' [bs ->]].
    destruct (classicT (x = px')) as [-> | Hn].
    * SCase "x = px"%string.
      (* induction on ⟦⤳⟧ **)
      gen T U T0 px pbs.
      dependent induction Hs; introv Hwf Hi Hv; introv Hp; introv [= -> <-];
        try simpl_dot; try rewrite proj_rewrite in *.
      + SSCase "lookup_var"%string.
        apply binds_push_eq_inv in H1 as ->.
        lets Hb: (pf_binds Hi Hp). pose proof (binds_push_eq_inv Hb) as ->.
        apply binds_inert in Hb; auto.
        destruct v as [S ds | S u | p A q].
        ++ (* v is an object *)
           right. left.
           lets Hi': (inert_prefix Hi). lets Hwf': (wf_prefix Hwf).
           inversions Hb; proof_recipe.
           {
              apply (repl_to_invertible_tag_v Hi') in Hv as [U' [Hrv Hrc]].
              apply (invertible_to_precise_tag_v Hi') in Hrv as [U'' [Hrv Hrc']].
              inversion Hrv.
           }
           { inversion Hvpr. }
           inversions Hv. pick_fresh z. assert (z \notin L) as Hz by auto.
           apply H4 in Hz. repeat eexists.
           +++ rewrite concat_empty_r. eauto.
           +++ apply open_env_last_defs; auto.
               apply narrow_defs with (G:=G & px ~ open_typ px S). {
                 assert (open_defs_p (p_sel (avar_f px) nil) ds = open_defs px ds) as -> by rewrite* open_var_defs_eq.
                 assert (open_typ_p (p_sel (avar_f px) nil) S = open_typ px S) as -> by rewrite* open_var_typ_eq.
                 apply rename_defs with (x := z); auto.
               }
               apply subenv_last; auto. apply (repl_composition_open (pvar px)) in Hrc.
               eapply (repl_composition_open (pvar px)) in Hrc'.
               apply subtyp_trans with (T:=open_typ px U');
                 apply repl_composition_sub in Hrc'; apply repl_composition_sub in Hrc; destruct_all;
                   repeat rewrite open_var_typ_eq in *; auto. all: auto.
           +++ eauto.
           +++ eauto.
        ++ (* v is a function *) left. repeat eexists. apply* weaken_ty_trm.
        ++ (* v is a tag *)
           right. right. right.
           lets Hi': (inert_prefix Hi). lets Hwf': (wf_prefix Hwf).
           inversions Hb; proof_recipe.
           2: { inversion Hvpr. }
           2: { inversion Hv. }
           apply (repl_to_invertible_tag_v Hi') in Hv as [p' [Hrv Hrc]].
           apply (invertible_to_precise_tag_v Hi') in Hrv as [p'' [Hrv Hrc']].
           inversions Hrv.
           repeat eexists.
           +++ simpl. apply ty_tag.
               apply weaken_ty_trm. assumption. apply* inert_ok.
               apply weaken_ty_trm. assumption. apply* inert_ok.
           +++ rewrite concat_empty_r. eauto.
           +++ eauto.
           +++ eauto.
      + SSCase "lookup_sel_p"%string.
        destruct (pf_path_sel _ _ Hi Hp) as [V Hp'].
        specialize (IHHs _ _ _ Hwt IHHwt _ H0 H JMeq_refl eq_refl _ Hwf Hi Hv _ _ Hp' _ _ eq_refl)
          as [[? [? [[=] ?]]] |
              [[? [? [? [? [? [? [? [[=]]]]]]]]] |
               [[? [? [? [? [? [? [[= ->] [[=] ?]]]]]]]] | ]]].
        right. right. right. destruct_all. subst.
        inversions H2.
      + SSCase "lookup_sel_v"%string.
        destruct (pf_path_sel _ _ Hi Hp) as [V Hp'].
        specialize (IHHs _ _ _ Hwt IHHwt _ H0 H JMeq_refl eq_refl _ Hwf Hi Hv _ _ Hp' _ _ eq_refl)
          as [[? [? [[=] ?]]] |
              [[S [ds' [W [T'' [G1 [G2 [pT [[= -> ->] [[= ->] [Heq [Hds Hrc]]]]]]]]]]] |
               [[? [? [? [? [? [? [[= ->] [-> [[= ->] ?]]]]]]]]]|]]].
        {
          lets H': (defs_has_open (p_sel (avar_f px) f) H1). simpl in *.
          lets Hr: (pf_record_has_U Hi Hp').
          rewrite Heq in Hi, Hwf.
          pose proof (repl_comp_trans_open (p_sel (avar_f px) f)
                                          (inert_prefix (inert_prefix Hi))
                                          Hrc) as Hrc_op.
          pose proof (repl_comp_trans_record_has Hrc_op Hr) as [V [W' [Hrh [Hrc1' Hrc2']]]].
          rewrite <- concat_empty_r in Heq at 1.
          assert (G2 = empty) as ->. {
            eapply env_ok_inv. eauto. rewrite concat_empty_r. rewrite <- Heq, concat_empty_r in Hi. auto.
          }
          repeat rewrite concat_empty_r in *. apply eq_push_inv in Heq as [_ [<- <-]].
          assert (G & px ~ T0 ⊢ V <: T1 /\ G & px ~ T0 ⊢ T1 <: V) as [HVT HTV]. {
            apply repl_composition_sub in Hrc2'. apply repl_composition_sub in Hrc1'.
            destruct_all.
            split; apply weaken_subtyp; eauto.
          }
          lets Hot: (object_typing Hi Hds H' Hrh).
          destruct Hot as [[U' [u [Heq Ht']]] |
                          [[U' [ds'' [Heq [Hds'' ->]]]] |
                            [[q [V' [Heq1 [-> Hq]]]] |
                            [p [A [q [q1 [V' [Heq1 Hq]]]]]]]]].
          ++ (* lambda *)
            destruct t; inversions Heq. destruct v0; inversions H3.
            left. repeat eexists. eauto.
          ++ destruct t as [|]; inversions Heq. destruct v0 as [X ds | |]; inversions H3. fold open_rec_defs_p in Hds''.
            right. left.
            pose proof (repl_comp_bnd_inv1 Hrc1') as [Y ->]. pose proof (repl_comp_bnd_inv2 Hrc2') as [Z ->].
            repeat eexists; eauto.
            +++ apply repl_comp_bnd' in Hrc1'. rewrite concat_empty_r. eauto.
            +++ apply repl_comp_bnd' in Hrc1'. apply Hrc1'.
            +++ apply* repl_comp_bnd'.
          ++ destruct t; inversions Heq1. right. right. left.
            pose proof (repl_comp_sngl_inv1 Hrc1') as [r ->]. pose proof (repl_comp_sngl_inv2 Hrc2') as [r' ->].
            pose proof (pf_sngl_U Hp) as ->.
            pose proof (sngl_typed Hi Hwf Hp) as [V Hr'%pt3].
            pose proof (pt3_exists Hi Hq) as [V'' Hp3].
            pose proof (repl_comp_to_prec' Hi Hwf Hrc2' Hr')
              as [-> | Hpr];
              pose proof (repl_comp_to_prec' Hi Hwf Hrc1' Hp3)
              as [<- | Hpr']; clear Hrc1' Hrc2';
                repeat eexists; try rewrite concat_empty_r; eauto.
          ++ simpl in *. destruct t; inversions Heq1. destruct v0; inversions H3.
             simpl in *.
             right. right. right. destruct Hq as [[= ->] [Hp1 Hp1']].
             pose proof (repl_comp_tag_inv1 Hrc1') as [Y ->].
             pose proof (repl_comp_tag_inv2 Hrc2') as [Z ->].
             repeat eexists; eauto.
             +++ apply repl_comp_tag' in Hrc1'. rewrite concat_empty_r. eauto.
             +++ apply repl_comp_tag' in Hrc2'. apply Hrc2'.
             +++ apply* repl_comp_tag'.
      }
      {
        destruct_all. inversion H2.
      }
    * SCase "x <> x0"%string.
      apply pf_strengthen in Hp; auto. apply lookup_strengthen_one in Hs; auto.
      inversions Heq.
      specialize (IHHwt (inert_prefix Hi) (wf_prefix Hwf) _ _ _ _ _ _ Hs Hp eq_refl)
        as [[? [? [[= ->]]]] |
              [[? [? [? [? [? [? [? [-> [-> [-> [Hds [? ?]]]]]]]]]]]] |
               [[? [? [? [? [? [? [[= ->] [[= ->] [-> [? ?]]]]]]]]]]|]]].
      + left. repeat eexists. apply* weaken_ty_trm.
      + right. left. repeat eexists. rewrite concat_assoc. eauto.
        apply* weaken_ty_defs. all: eauto.
      + right. right. left. repeat eexists.
        rewrite concat_assoc.
        all: eauto.
      + destruct_all. subst.
        right. right. right. repeat eexists; eauto. apply* weaken_ty_trm.
        rewrite concat_assoc.
        all: eauto.
  Unshelve. all: solve_ex_typ_L.
Qed.

(** If [p] looks up to [t] in a value environment and [p]'s II-level precise type
    is [T], then either [t] is
    - a function that has type [T], and [T] is [p]'s precise type,
    - an object [ν(S)ds] that has type [μ(S)], and [T] and [μ(s)] are equivalent, or
    - a well-typed path [q], and [T] is equivalent to [q.type] *)
Lemma lookup_step_preservation_prec2 G γ p px pbs t T :
    inert G ->
    wf G ->
    γ ⫶ G ->
    γ ⟦ p ⤳ t ⟧ ->
    G ⊢!! p : T ->
    p = p_sel (avar_f px) pbs ->
    (exists S U u, t = defv (λ(S) u) /\ G ⊢ deftrm t : U /\ G ⊢! p : U ⪼ T) \/
    (exists S ds W U G1 G2 pT,
        t = defv (ν(S) ds) /\
        G ⊢! p : μ U ⪼ T /\
        G = G1 & px ~ pT & G2 /\
        px ; pbs; G ⊢ open_defs_p p ds :: open_typ_p p S /\
        G1 ⊩ S ⟿ W ⬳ U) \/
    (exists q r r' G1 G2 pT,
        t = defp q /\
        T = {{ r }} /\
        G = G1 & px ~ pT & G2 /\
        (r = r' \/ G1 ⊢!!! r : {{ r' }}) /\ (r' = q \/ G1 ⊢!!! q : {{ r' }})) \/
    (exists p1 A q q1 r r' G1 G2 pT,
        t = defv (val_tag p1 A q q1) /\
        T = typ_tag r /\
        G ⊢ deftrm t : (typ_tag q) /\
        G = G1 & px ~ pT & G2 /\
        G1 ⊩ r ⟿' r' ⬳ q).
Proof.
  introv Hi Hwf Hwt Hs Hp Heq. gen γ t px pbs. induction Hp; introv Hwt; introv Hs; introv Heq.
  - destruct (lookup_step_preservation_prec1 Hi Hwf Hwt Hs H Heq)
      as [[? [? [[= ->]]]] |
          [[S [ds' [W [T'' [G1 [G2 [pT [-> [-> [-> [Hds [Hrc1 Hrc2]]]]]]]]]]]] |
           [[? [? [? [? [? [? [-> [-> [-> [? ?]]]]]]]]]]|]]].
    * left. repeat eexists; eauto.
    * right. left. repeat eexists; eauto.
    * pose proof (pf_sngl_U H) as ->. right. right. left. repeat eexists; eauto.
      destruct_all; eauto.
    * right. right. right. remember H0 as H1. clear HeqH1.
      destruct H0 as [_ [_ [_ [_ [? [? [_ [_ [_ [_ [Heqt _]]]]]]]]]]]. subst T.
      apply pf_tag_U in H as Hx. subst U. auto.
  - clear IHHp2. simpl_dot. specialize (IHHp1 Hi Hwf _ Hwt).
    gen q U. dependent induction Hs; simpl_dot; introv Hp IHHp1 Hv.
    * specialize (IHHp1 _ Hs _ _ eq_refl) as [[? [? [? [[=] ?]]]] |
                                  [[? [? [? [? [? [? [? [[=] ?]]]]]]]] |
                                   [[q' [r [r' [G1 [G2 [pT [[= <-] [[= ->] [-> [Hrc1 Hrc2]]]]]]]]]]|]]].
      { right. right. left. exists (q • a) (r • a).
        pose proof (inert_prefix (inert_prefix Hi)) as Hi'.
        pose proof (wf_prefix (wf_prefix Hwf)) as Hwf'.
        destruct Hrc1 as [-> | Hr1]; destruct Hrc2 as [-> | Hr2].
        ** repeat eexists; eauto.
        ** repeat eexists; eauto. right. apply* pt3_field_elim_p.
          apply* pt3_trans2.
          pose proof (sngl_typed3 Hi' Hwf' Hr2) as [_ [T Ht]%pt2_exists].
          constructor. rewrite <- concat_assoc in *. apply* pt2_fld_strengthen.
        ** repeat eexists. right. apply* pt3_field_elim_p.
          rewrite <- concat_assoc in *. apply* pt3_fld_strengthen.
          left*.
        ** pose proof (field_elim_q3) as Hf.
          rewrite <- concat_assoc in *.
          pose proof (pt3_weaken (inert_ok Hi) Hr1).
          specialize (Hf _ _ _ _ _ Hi H (pt3 Hv)) as [S Ht].
          repeat eexists. rewrite* concat_assoc.
          right. apply* pt3_field_elim_p.
          apply* pt3_fld_strengthen.
          right. apply* pt3_field_elim_p. apply* pt3_fld_strengthen.
          eapply pt3_trans2. eapply pt3_weaken. apply* inert_ok. apply Hr2.
          eapply pt3_weaken in Hr1. apply Ht. apply* inert_ok.
      }
      {
        destruct_all. inversion H0.
      }
    * specialize (IHHp1 _ Hs) as [[? [? [? [[= ->] ?]]]] |
                                  [[? [? [? [? [? [? [? [? [[=]%pf_sngl_T [[=] [HH [HHH ?]]]]]]]]]]]] |
                                   [[? [? [? [? [? [? [[=] ?]]]]]]]|]]]; auto.
      destruct_all. inversion H1.
Qed.

(** If [p] looks up to [t] in a value environment and [p]'s III-level precise type
    is an _inert_ type [T], then either [t] is
    - a function that has type [T],
    - an object [ν(S)ds] that has type [μ(S)], and [T] and [μ(s)] are equivalent, or
    - a well-typed path [q], and [q]'s type is [T] *)
Lemma lookup_step_preservation_inert_prec3: forall G γ p T t,
    inert G ->
    wf G ->
    γ ⫶ G ->
    γ ⟦ p ⤳ t ⟧ ->
    G ⊢!!! p : T ->
    inert_typ T ->
    (exists S U, T = ∀(S) U /\ G ⊢ deftrm t : ∀(S) U) \/
    (exists U, T = μ U /\
          ((exists S ds px pbs W, t = defv (ν(S) ds) /\
                               p = p_sel (avar_f px) pbs /\
                               px; pbs; G ⊢ open_defs_p p ds :: open_typ_p p S /\
                               G ⊩ S ⟿ W ⬳ U) \/
           (exists q, t = defp q /\ G ⊢!!! q : T))) \/
    (exists r, T = typ_tag r /\
        ((exists p1 A q q1 r', t = defv (val_tag p1 A q q1) /\
                         G ⊢ deftrm t : (typ_tag q) /\
                         G ⊩ r ⟿' r' ⬳ q) \/
         (exists q, t = defp q /\ G ⊢!!! q : T))).
Proof.
  introv Hi Hwf Hwt Hs Hp. gen t.
  pose proof (typed_paths_named (precise_to_general3 Hp)) as [px [pbs Heq]].
  dependent induction Hp; introv Hs Hit;
    destruct (lookup_step_preservation_prec2 Hi Hwf Hwt Hs H Heq)
                                as [[S' [U [u [[= ->] [Hv Hp']]]]] |
                                    [[S' [ds [W [U [G1 [G2 [pT [[= ->] [Hp' [-> [Hds [Hrc1 Hrc2]]]]]]]]]]]] |
                                     [[q' [r [r' [G1 [G2 [pT [[= ->] [[= ->] [Heq' [Hrc1 Hrc2]]]]]]]]]] |
                                      [p1 [A [q' [q'1 [r [r' [G1 [G2 [pT [[= ->] [[= ->] [Hq' [Heq' Hrc]]]]]]]]]]]]]]]]; simpl.
  - left. simpl in *. inversions Hit.
    * apply (pf_tag_T Hi) in Hp' as ->. proof_recipe.
      apply (repl_to_invertible_tag_v Hi) in Hv as [q' [Hrv Hrc]].
      apply (invertible_to_precise_tag_v Hi) in Hrv as [q'' [Hrv Hrc']].
      inversion Hrv.
    * apply (pf_forall_T Hi) in Hp' as ->. repeat eexists; eauto.
    * apply (pf_bnd_T Hi) in Hp' as ->. proof_recipe. inversion Hv.
  - right. left. inversions Hit.
    * apply (pf_tag_T Hi) in Hp' as [=].
    * apply (pf_forall_T Hi) in Hp' as [=].
    * apply (pf_bnd_T Hi) in Hp' as [= ->]. eexists. split*. left. repeat eexists; eauto;
      repeat apply* repl_composition_weaken; apply* inert_ok; apply* inert_prefix.
  - inversion Hit.
  - right. right. destruct Hrc as [Hrc1 Hrc2]. subst G.
    eexists. split. apply eq_refl. left. repeat eexists; eauto.
    repeat apply* repl_composition_p_weaken; apply* inert_ok; apply* inert_prefix.
    repeat apply* repl_composition_p_weaken; apply* inert_ok; apply* inert_prefix.
  - apply pf_sngl_T in Hp' as ->; auto. proof_recipe. inversions Hv. inversions H0. inversion H1.
  - apply (pf_sngl_T Hi) in Hp' as [=].
  - clear IHHp.
    assert (exists V, G ⊢!!! q' : V) as [V Hq']. {
      destruct Hrc1 as [-> | Hr]; destruct Hrc2 as [-> | Hr']; subst; rewrite <- concat_assoc in *; eauto.
      - eexists. apply* pt3_weaken.
      - apply sngl_typed3 in Hr as [S Ht]. eexists. apply* pt3_weaken. apply* inert_prefix. apply* wf_prefix.
      - eexists. apply* pt3_weaken.
    }
    lets Hok: (inert_ok Hi). rewrite Heq' in Hok.
    destruct Hrc1 as [-> | Hr]; destruct Hrc2 as [-> | Hr']; inversions Hit.
    + right. right. repeat eexists; eauto.
    + left; repeat eexists; apply* precise_to_general3.
    + right. left. eexists. split*.
    + right. right. repeat eexists; eauto. right. repeat eexists; eauto. apply* pt3_sngl_trans3.
      repeat apply* pt3_weaken.
    + left. repeat eexists. apply* precise_to_general3. apply* pt3_sngl_trans3.
      repeat apply* pt3_weaken.
    + right. left. eexists. split*. right. eexists. split*.
      apply* pt3_sngl_trans3. repeat apply* pt3_weaken.
    + right. right. repeat eexists; eauto. right.
      repeat eexists; eauto. do 2 eapply pt3_weaken in Hr.
      pose proof (pt3_inert_sngl_invert Hi Hp Hr (inert_typ_tag _)) as Hr'.
      exact Hr'. all: eauto. apply* inert_ok. apply* inert_prefix.
    + left. repeat eexists.
      do 2 eapply pt3_weaken in Hr.
      pose proof (pt3_inert_sngl_invert Hi Hp Hr (inert_typ_all _ _)) as Hr'.
      apply* precise_to_general3. all: eauto; apply* inert_ok. apply* inert_prefix.
    + right. left. eexists. split*. right. eexists. split*.
      do 2 eapply pt3_weaken in Hr.
      apply* (pt3_inert_sngl_invert Hi Hp Hr).
      all: eauto; apply* inert_ok. apply* inert_prefix.
    + right. right. repeat eexists; eauto. right.
      repeat eexists; eauto.
      eapply pt3_sngl_trans3. repeat apply* pt3_weaken.
      apply* pt3_inert_sngl_invert. repeat apply* pt3_weaken.
    + left. repeat eexists. apply precise_to_general3.
      eapply pt3_sngl_trans3. repeat apply* pt3_weaken.
      apply* pt3_inert_sngl_invert. repeat apply* pt3_weaken.
    + right. left. eexists. split*. right. eexists. split*.
      eapply pt3_sngl_trans3. repeat apply* pt3_weaken.
      apply* pt3_inert_sngl_invert. repeat apply* pt3_weaken.
Qed.

(** If [p] looks up to [t] in a value environment and [p]'s III-level precise type
    is a function type, then [t] has the same function type *)
Lemma lookup_step_preservation_prec3_fun G γ p T S t :
  inert G ->
  wf G ->
  γ ⫶ G ->
  γ ⟦ p ⤳ t ⟧ ->
  G ⊢!!! p : ∀(T) S ->
  G ⊢ deftrm t : ∀(T) S.
Proof.
  intros Hi Hwf Hwt Hs Hp.
  destruct (lookup_step_preservation_inert_prec3 Hi Hwf Hwt Hs Hp) as
      [[? [? [-> Ht]]] | [[? [[=] ?]]| [r [Heq _]]]]; auto.
  inversion Heq.
Qed.

Lemma subtyp_tag_equiv_path_qp_step: forall G p q,
    typed_path_repl_comp_qp G q p ->
    G ⊢ typ_tag q <: typ_tag p.
Proof.
  introv Hqp. inversions Hqp.
  eapply subtyp_sngl_qp. apply* precise_to_general.
  apply* precise_to_general2. eauto.
Qed.

Lemma subtyp_tag_equiv_path_pq_step: forall G p q,
    typed_path_repl_comp_qp G q p ->
    G ⊢ typ_tag p <: typ_tag q.
Proof.
  introv Hqp. inversions Hqp.
  eapply subtyp_sngl_pq. apply* precise_to_general.
  apply* precise_to_general2. eauto.
Qed.

Lemma ty_tag_equiv_path_qp_step: forall G t p q,
    typed_path_repl_comp_qp G q p ->
    G ⊢ t : typ_tag q ->
    G ⊢ t : typ_tag p.
Proof.
  introv Hqp Hq. inversions Hqp.
  eapply ty_sub.
  exact Hq.
  eapply subtyp_sngl_qp. apply* precise_to_general.
  apply* precise_to_general2. eauto.
Qed.

Lemma ty_tag_equiv_path_pq_step: forall G t p q,
    typed_path_repl_comp_qp G q p ->
    G ⊢ t : typ_tag p ->
    G ⊢ t : typ_tag q.
Proof.
  introv Hqp Hq. inversions Hqp.
  eapply ty_sub.
  exact Hq.
  eapply subtyp_sngl_pq. apply* precise_to_general.
  apply* precise_to_general2. eauto.
Qed.

Lemma subtyp_tag_equiv_path_qp : forall G p q,
    G ⊢ q ⟿' p ->
    G ⊢ typ_tag q <: typ_tag p.
Proof.
  introv Hqp.
  dependent induction Hqp; eauto 2.
  apply subtyp_trans with (T:=typ_tag b); eauto 1.
  apply* subtyp_tag_equiv_path_pq_step.
Qed.

Lemma subtyp_tag_equiv_path_pq : forall G p q,
    G ⊢ q ⟿' p ->
    G ⊢ typ_tag p <: typ_tag q.
Proof.
  introv Hqp.
  dependent induction Hqp; eauto 2.
  apply subtyp_trans with (T:=typ_tag b); eauto 1.
  apply* subtyp_tag_equiv_path_qp_step.
Qed.

Lemma ty_tag_equiv_path_qp : forall G t p q,
    G ⊢ q ⟿' p ->
    G ⊢ t : typ_tag q ->
    G ⊢ t : typ_tag p.
Proof.
  introv Hqp Hq.
  dependent induction Hqp; eauto 2. specialize (IHHqp Hq).
  eapply ty_tag_equiv_path_pq_step. exact H. exact IHHqp.
Qed.

Lemma ty_tag_equiv_path_pq : forall G t p q,
    G ⊢ q ⟿' p ->
    G ⊢ t : typ_tag p ->
    G ⊢ t : typ_tag q.
Proof.
  introv Hqp Hq.
  dependent induction Hqp; eauto 2. apply IHHqp.
  eapply ty_tag_equiv_path_qp_step. exact H. exact Hq.
Qed.

(** If [p] looks up to [t] in a value environment and [p]'s III-level precise type
    is a tag type, then [t] has the same tag type *)
Lemma lookup_step_preservation_prec3_tag G γ p r t :
  inert G ->
  wf G ->
  γ ⫶ G ->
  γ ⟦ p ⤳ t ⟧ ->
  G ⊢!!! p : typ_tag r ->
  G ⊢ deftrm t : typ_tag r.
Proof.
  intros Hi Hwf Hwt Hs Hp.
  destruct (lookup_step_preservation_inert_prec3 Hi Hwf Hwt Hs Hp) as
      [[? [? [-> Ht]]] | [[? [[=] ?]]| [r' [Heq Hq]]]]; auto. inversions Heq.
  destruct_all.
  - subst. simpl in *. eapply ty_tag_equiv_path_pq. exact H1.
    eapply ty_tag_equiv_path_qp. exact H2. exact H0.
  - subst. simpl in *. apply* precise_to_general3.
Qed.

(** The following two lemmas are needed only for path safety (not for term safety) *)

(** If a well-typed path [p] looks up to a path [q] then [q] is also well-typed. *)
Lemma lookup_step_pres G p T q γ :
  inert G ->
  wf G ->
  γ ⫶ G ->
  G ⊢!!! p : T ->
  γ ⟦ p ⤳ defp q ⟧ ->
  exists U, G ⊢!!! q : U.
Proof.
  intros Hi Hwf Hwt Hp Hl.
  apply pt2_exists in Hp as [U Hp].
  pose proof (named_lookup_step Hl) as [x [bs Heq]].
  pose proof (lookup_step_preservation_prec2 Hi Hwf Hwt Hl Hp Heq)
    as [[? [? [? [[=] ?]]]] |
        [[? [? [? [? [? [? [? [[=] ?]]]]]]]] |
         [[r' [r [G1 [G2 [pT [S [[= ->] [-> [-> [[-> | Hr] [-> | Hr']]]]]]]]]]]|]]].
  - apply sngl_typed2 in Hp as [U Hr]; eauto.
  - eexists. do 2 apply* pt3_weaken. apply inert_ok in Hi.
    apply* ok_concat_inv_l.
  - apply sngl_typed3 in Hr as [U Hr]; eauto.
    eexists. do 2 apply* pt3_weaken. apply inert_ok in Hi.
    apply* ok_concat_inv_l. do 2 apply* inert_prefix.
  - eexists. do 2 apply* pt3_weaken. apply inert_ok in Hi.
    apply* ok_concat_inv_l.
  - destruct_all. inversion H.
Qed.

(** If a well-typed path [p] looks up to a path [q] then [q] is also well-typed. *)
Lemma lookup_step_sngl G p T q γ :
  inert G ->
  wf G ->
  γ ⫶ G ->
  G ⊢!!! p : T ->
  γ ⟦ p ⤳ defp q ⟧ ->
  G ⊢ trm_path p: {{ q }}.
Proof.
  intros Hi Hwf Hwt Hp Hl.
  apply pt2_exists in Hp as [U Hp].
  pose proof (named_lookup_step Hl) as [x [bs Heq]].
  pose proof (lookup_step_preservation_prec2 Hi Hwf Hwt Hl Hp Heq)
    as [[? [? [? [[=] ?]]]] |
        [[? [? [? [? [? [? [? [[=] ?]]]]]]]] |
         [[r' [r [G1 [G2 [pT [S [[= ->] [-> [-> [[-> | Hr] [-> | Hr']]]]]]]]]]]|]]].
  - eauto.
    apply* precise_to_general2.
  - assert (Hr'': G2 & x ~ S & pT ⊢!!! r' : {{ G1 }}). {
      do 2 apply* pt3_weaken. apply inert_ok in Hi.
      apply* ok_concat_inv_l.
    }
    assert (Hg: exists U, G2 & x ~ S & pT ⊢!!! G1: U). {
      apply* sngl_typed3.
    }
    destruct Hg as [U Hg].
    eapply ty_sub.
    + apply* precise_to_general2.
    + eapply subtyp_sngl_qp. apply* precise_to_general3.
      apply* precise_to_general3. apply repl_intro_sngl.
  - assert (Hr': G2 & x ~ S & pT ⊢!!! r: {{ r' }}). {
      do 2 apply* pt3_weaken. apply* inert_ok.
      apply* inert_prefix.
    }
    assert (Hr'': exists U, G2 & x ~ S & pT ⊢!!! r' : U). {
      eapply sngl_typed3. exact Hi. exact Hwf. exact Hr'.
    }
    destruct Hr'' as [U Hr''].
    eapply ty_sub.
    + apply* precise_to_general3.
    + eapply subtyp_sngl_pq.
      apply* precise_to_general3.
      apply* precise_to_general3.
      apply repl_intro_sngl.
  - assert (Hrf: G2 & x ~ S & pT ⊢!!! r: {{G1}}). {
      do 2 apply* pt3_weaken. apply* inert_ok. apply* inert_prefix.
    }
    assert (Hrf': G2 & x ~ S & pT ⊢!!! r': {{G1}}). {
      do 2 apply* pt3_weaken. apply* inert_ok. apply* inert_prefix.
    }
    assert (Hg: exists U, G2 & x ~ S & pT ⊢!!! G1: U). {
      apply* sngl_typed3.
    }
    destruct Hg as [U Hg].
    assert (Hrr: G2 & x ~ S & pT ⊢ trm_path r: {{r'}}). {
      apply~ shared_sngl_pq; apply* precise_to_general3.
    }
    eapply ty_sub.
    + apply* precise_to_general3.
    + apply subtyp_sngl_pq with (p:=r) (q:=r') (U:={{G1}}).
      auto. apply* precise_to_general3. apply repl_intro_sngl.
  - destruct_all. inversion H.
Qed.

(** If a well-typed path [p] looks up to a path [q] in a finite number
    of steps then [q] is also well-typed.*)
Lemma lookup_pres G p T q γ :
  inert G ->
  wf G ->
  γ ⫶ G ->
  G ⊢!!! p : T ->
  γ ⟦ defp p ⤳* defp q ⟧ ->
  exists U, G ⊢!!! q : U.
Proof.
  intros Hi Hwf Hwt Hp Hl. gen T. dependent induction Hl; introv Hp; eauto.
  destruct b.
  - pose proof (lookup_step_pres Hi Hwf Hwt Hp H) as [U Hq]. eauto.
  - apply lookup_val_inv in Hl as [=].
Qed.

(** If a well-typed path [p] looks up to a path [q] then [q] is also well-typed. *)
Lemma lookup_sngl G p T q γ :
  inert G ->
  wf G ->
  γ ⫶ G ->
  G ⊢!!! p : T ->
  γ ⟦ defp p ⤳* defp q ⟧ ->
  p = q \/ G ⊢ trm_path p: {{ q }}.
Proof.
  introv Hi Hwf Hwt Hp Hl. gen T. dependent induction Hl; introv Hp; auto.
  destruct b.
  + assert (Hqu: exists U, G ⊢!!! p0 : U). {
      apply* lookup_pres.
    }
    assert (Hpp0: G ⊢ trm_path p : {{ p0 }}). {
      apply* lookup_step_sngl.
    }
    destruct Hqu as [U Hpu].
    assert (Hqu: exists U, G ⊢!!! q : U). {
      apply* lookup_pres.
    }
    destruct Hqu as [U' Hqu].
    specialize (IHHl p0 q Hi Hwf Hwt eq_refl eq_refl _ Hpu).
    destruct IHHl.
    - subst. right. auto.
    - right. eapply ty_sub.
      * exact Hpp0.
      * eapply subtyp_sngl_pq. exact H0.
        apply* precise_to_general3. apply repl_intro_sngl.
  + apply lookup_val_inv in Hl. inversion Hl.
Qed.

(** If a stable term [t] has a function type and [t] can be looked
    up to [u] in a finite number of steps in the value environment,
    then [u] has the same function type. *)
Lemma lookup_preservation_forall : forall G γ t u T S,
    inert G ->
    wf G ->
    γ ⫶ G ->
    γ ⟦ t ⤳* u ⟧ ->
    G ⊢ deftrm t : ∀(S) T ->
    G ⊢ deftrm u: ∀(S) T.
Proof.
  introv Hi Hwf Hwt Hl Hp. dependent induction Hl; auto.
  assert (exists q, a = defp q) as [q ->] by (inversions H; eauto).
  proof_recipe.
  pose proof (lookup_step_preservation_prec3_fun Hi Hwf Hwt H Hpr) as Hb.
  apply IHHl.
  apply ty_sub with (T:=∀(Spr) Tpr); auto; fresh_constructor; apply* tight_to_general.
Qed.

(** If a stable term [t] has a function type and [t] can be looked
    up to [u] in a finite number of steps in the value environment,
    then [u] has the same function type. *)
Lemma lookup_preservation_tag : forall G γ t u r,
    inert G ->
    wf G ->
    γ ⫶ G ->
    γ ⟦ t ⤳* u ⟧ ->
    G ⊢ deftrm t : typ_tag r ->
    G ⊢ deftrm u : typ_tag r.
Proof.
  introv Hi Hwf Hwt Hl Hp. dependent induction Hl; auto.
  assert (exists q, a = defp q) as [q ->] by (inversions H; eauto).
  proof_recipe.
  eapply repl_to_invertible_tag_repl_comp in Hp; eauto 1.
  destruct Hp as [q' [Hrq' Hqi]].
  eapply inv_to_precise_tag_repl_comp in Hqi; eauto 5.
  destruct Hqi as [r' [Hqp Hrq'']].
  pose proof (lookup_step_preservation_prec3_tag Hi Hwf Hwt H Hqp) as Hb.
  apply IHHl; eauto 1.
  eapply ty_sub. apply Hb.
  apply subtyp_trans with (T:=typ_tag q').
  + apply* subtyp_tag_equiv_path_qp.
  + apply* subtyp_tag_equiv_path_pq.
Qed.

(** ** Looking up well-typed paths *)
(** If a path has a precise type then it can be looked up in the value environment *)
Lemma typ_to_lookup1 G γ p T U :
  inert G ->
  wf G ->
  γ ⫶ G ->
  G ⊢! p : T ⪼ U ->
  exists t, γ ⟦ p ⤳ t ⟧.
Proof.
  intros Hi Hwf Hwt Hp. gen p T U. induction Hwt; introv Hp.
  (* induction on ⟦~⟧ **)
  - false. dependent induction Hp; eauto. apply* binds_empty_inv.
  - pose proof (typed_paths_named (precise_to_general Hp)) as [y [bs ->]].
    (* later when we figure out how to make env closed *)
    destruct (classicT (x = y)) as [-> | Hn].
    * SCase "x = y"%string.
      (* induction on ⟦⊢!⟧ **)
      dependent induction Hp; try simpl_dot.
      + eexists. apply* lookup_var.
      + specialize (IHHp _ _ H0 _ _ Hwf Hi Hwt H H1 IHHwt JMeq_refl eq_refl) as [t Hs].
        pose proof (pf_bnd_T2 Hi Hp) as [V ->].
        destruct (lookup_step_preservation_prec1 Hi Hwf (well_typed_push Hwt H H0 H1) Hs Hp eq_refl)
          as [[S [u [-> Ht]]] |
              [[S [ds' [W [T'' [G1 [G2 [pT [-> [[= ->] [Heq [Hds Hrc]]]]]]]]]]] |
               [[? [? [? [? [? [? [? [[=] [? ?]]]]]]]]]|]]].
        ++ proof_recipe. inversion Ht.
        ++ assert (exists u, defs_has ds' {a := u}) as [u Hu]. {
             apply pf_record_has_U in Hp; auto.
             eapply repl_comp_trans_open in Hrc.
             eapply repl_comp_trans_record_has in Hrc as [V [X [Hr _]]]; try apply Hp.
             eapply record_has_ty_defs in Hds as [d [Hdh Hds]]; eauto.
             eapply defs_invert_trm in Hds as [t ->]. unfold defs_has in *.
             simpl in *. apply* defs_has_open'. rewrite  Heq in Hi, Hwf.
             repeat apply* inert_prefix.
           }
           eexists. rewrite proj_rewrite. eauto.
        ++ destruct_all. inversion H3.
      + eauto.
      + eauto.
      + eauto.
    * SCase "x <> y"%string.
      apply pf_strengthen in Hp; auto. specialize (IHHwt (inert_prefix Hi) (wf_prefix Hwf) _ _ _ Hp) as [t Hs].
      eexists. apply* lookup_step_weaken_one.
Qed.

(** If a path has a II-level precise type then it can be looked up in the value environment *)
Lemma typ_to_lookup2 G γ p T :
  inert G ->
  wf G ->
  γ ⫶ G ->
  G ⊢!! p : T ->
  exists t, γ ⟦ p ⤳ t ⟧.
Proof.
  intros Hi Hwf Hwt Hp. induction Hp.
  - apply* typ_to_lookup1.
  - specialize (IHHp1 Hi Hwf Hwt) as [u1 Hs1]. specialize (IHHp2 Hi Hwf Hwt) as [u2 Hs2].
    pose proof (typed_paths_named (precise_to_general2 Hp1)) as [px [pbs ->]].
    destruct (lookup_step_preservation_prec2 Hi Hwf Hwt Hs1 Hp1 eq_refl)
                                as [[S' [U' [u [[= ->] [Hv Hp']]]]] |
                                    [[S' [ds [W [U' [G1 [G2 [pT [-> [Hp' [Heq [Hds [Hrc1 Hrc2]]]]]]]]]]]] |
                                     [[? [? [? [? [? [? [-> [[= ->] ?]]]]]]]]|]]].
    + pose proof (pf_sngl_T Hi Hp') as ->. proof_recipe. inversions Hv. inversions H. inversions H0.
    + pose proof (pf_sngl_T Hi Hp') as [=].
    + eauto.
    + destruct_all. inversion H0.
Qed.

(** If a path has a III-level precise type then it can be looked up
    in the value environment *)
Lemma typ_to_lookup3 G γ p T :
  inert G ->
  wf G ->
  γ ⫶ G ->
  G ⊢!!!p : T ->
  exists t, γ ⟦ p ⤳ t ⟧.
Proof.
  intros Hi Hwf Hwt Hp. induction Hp; apply* typ_to_lookup2.
Qed.

(** If a path [p]'s environment type is a singleton type [q.type]
    then [p] can be looked up to a path [r] in the value environment,
    and either [q=r], or there exists a path [r'] such that
    both [r'] is the III-level precise type of both [q] and [r].
    In other words, [q] and [r] are aliases of the same path [r']. *)
Lemma sngl_path_lookup G γ p q U :
  inert G ->
  wf G ->
  γ ⫶ G ->
  G ⊢! p : {{ q }} ⪼ U ->
           exists r r', γ ⟦ p ⤳ defp r ⟧ /\
                   (r = r' \/ G ⊢!!! r : {{ r' }}) /\
                   (q = r' \/ G ⊢!!! q : {{ r' }}).
Proof.
  intros Hi Hwf Hwt Hp. destruct (typ_to_lookup1 Hi Hwf Hwt Hp) as [t Hs].
  pose proof (typed_paths_named (precise_to_general Hp)) as [px [pbs ->]].
  destruct (lookup_step_preservation_prec1 Hi Hwf Hwt Hs Hp eq_refl)
           as [[S [u [-> Ht]]] |
              [[S [ds' [W [T'' [G1 [G2 [pT [-> [[= ->] ?]]]]]]]]] |
               [[? [? [? [G1 [G2 [pT [-> [[= -> ] [-> [Hrc1 Hrc2]]]]]]]]]]|]]].
  - proof_recipe. inversions Ht. inversions H. inversion H0.
  - pose proof (inert_ok Hi) as Hok%ok_concat_inv_l.
    destruct Hrc1 as [-> | Hx0]; destruct Hrc2 as [-> | Hrx1]; do 2 eexists; eauto.
    + split*. split. right.
      repeat apply* pt3_weaken. eauto.
    + split*. split. left*. right. repeat apply* pt3_weaken.
    + split*. split; right; repeat apply* pt3_weaken.
  - destruct_all. inversion H0.
Qed.

(** If [p] looks up to [t] in a value environment and [p]'s III-level precise type
    is [q.type], where [q]'s environment type is a function type, then
    [t] is a path [r], and [q] and [r] are aliases. *)
Lemma lookup_step_preservation_sngl_prec3: forall G γ p q t Q1 Q2 Q3,
    inert G ->
    wf G ->
    γ ⫶ G ->
    γ ⟦ p ⤳ t ⟧ ->
    G ⊢!!! p : {{ q }} ->
    G ⊢! q : ∀(Q1) Q2 ⪼ Q3 ->
    exists r r', t = defp r /\
            (q = r' \/ G ⊢!!! q : {{ r' }}) /\
            (r = r' \/ G ⊢!!! r : {{ r' }}).
Proof.
  introv Hi Hwf Hwt Hs Hp. gen t.
  pose proof (typed_paths_named (precise_to_general3 Hp)) as [px [pbs Heq]].
  dependent induction Hp; introv Hs Hq;
    destruct (lookup_step_preservation_prec2 Hi Hwf Hwt Hs H Heq)
    as [[S' [U' [u [[= ->] [Hv Hp']]]]] |
        [[S' [ds [W [U [G1 [G2 [pT [-> [Hp' [Heq' [Hds [Hrc1 Hrc2]]]]]]]]]]]] |
         [[q' [r [r' [G1 [G2 [pT [-> [[= ->] [-> [Hrc1 Hrc2]]]]]]]]]]|]]].
  - pose proof (pf_sngl_T Hi Hp') as ->. pose proof (sngl_path_lookup Hi Hwf Hwt Hp') as [? [? [Hl ?]]].
    pose proof (lookup_step_func Hl Hs) as [=].
  - pose proof (pf_sngl_T Hi Hp') as [=].
  - destruct Hrc1 as [-> | Hrc1]; destruct Hrc2 as [-> | Hrc2]; do 2 eexists; eauto; split*; split;
      [ left* | right | right | left* | right | right ]; repeat apply* pt3_weaken.
    all: apply* inert_ok; apply* inert_prefix.
  - destruct_all. subst. inversion H1.
  - pose proof (pf_sngl_T Hi Hp') as ->. pose proof (sngl_path_lookup Hi Hwf Hwt Hp') as [? [? [Hl ?]]].
    pose proof (lookup_step_func Hl Hs) as [=].
  - pose proof (pf_sngl_T Hi Hp') as [=].
  - pose proof (typ_to_lookup3 Hi Hwf Hwt Hp) as [t Hl].
    pose proof (typed_paths_named (precise_to_general3 Hp)) as [rx [rbs Heqr]].
    specialize (IHHp _ Hi Hwf Hwt eq_refl _ _ Heqr _ Hl Hq) as [r1 [r2 [-> [[-> | Hq'] [-> | Hq'']]]]].
      * destruct Hrc1 as [-> | Hp']; destruct Hrc2 as [-> | Hp'']; do 2 eexists; split*.
        ** split. left*. right. apply* pt3_sngl_trans3. repeat apply* pt3_weaken.
           apply inert_ok. apply* inert_prefix.
        ** split. left*. do 2 eapply pt3_weaken in Hp'. pose proof (pt3_invert Hi Hp Hp')
             as [? | [r1 [[= ->] [-> | ?]]]]; eauto.
           false* pf_inert_pt3_sngl_false. all: apply* inert_ok; apply* inert_prefix.
        ** split. left*. do 2 eapply pt3_weaken in Hp'; try solve [apply* inert_ok; apply* inert_prefix].
           pose proof (pt3_invert Hi Hp Hp')
             as [? | [r1 [[= ->] [-> | ?]]]].
           *** right. apply* pt3_sngl_trans3. repeat apply* pt3_weaken. eapply inert_ok, inert_prefix; eauto.
           *** right. repeat apply* pt3_weaken. eapply inert_ok, inert_prefix; eauto.
           *** false* pf_inert_pt3_sngl_false.
      * destruct Hrc1 as [-> | Hp']; destruct Hrc2 as [-> | Hp'']; do 2 eexists; split*.
        ** split. left*. right. eapply pt3_sngl_trans3. repeat apply* pt3_weaken.
           apply* inert_ok. apply* inert_prefix. auto.
        ** split. left*. do 2 eapply pt3_weaken in Hp'; try solve [apply* inert_ok; apply* inert_prefix].
           pose proof (pt3_invert Hi Hp Hp')
             as [? | [r1' [[= ->] [-> | ?]]]]; eauto. false* pf_inert_pt3_sngl_false.
        ** split. left*.
           do 2 eapply pt3_weaken in Hp'; try solve [apply* inert_ok; apply* inert_prefix].
           pose proof (pt3_invert Hi Hp Hp') as [? | [r1' [[= ->] [-> | HHH]]]].
           *** right. apply* pt3_sngl_trans3. repeat apply* pt3_weaken. apply* inert_ok. apply* inert_prefix.
           *** right. repeat apply* pt3_weaken. apply* inert_ok. apply* inert_prefix.
           *** false* pf_inert_pt3_sngl_false.
      * destruct Hrc1 as [-> | Hp']; destruct Hrc2 as [-> | Hp'']; do 2 eexists; split*.
        ** split. left*. right. apply* pt3_sngl_trans3. repeat apply* pt3_weaken.
           apply* inert_ok. apply* inert_prefix.
        ** split. left*.
           do 2 eapply pt3_weaken in Hp'; try solve [apply* inert_ok; apply* inert_prefix].
           pose proof (pt3_invert Hi Hp Hp')
             as [? | [r1 [[= ->] [-> | ?]]]]; eauto.
           false* pf_inert_pt3_sngl_false.
        ** split. left*.
            do 2 eapply pt3_weaken in Hp'; try solve [apply* inert_ok; apply* inert_prefix].
           pose proof (pt3_invert Hi Hp Hp')
             as [? | [r1 [[= ->] [-> | ?]]]].
           *** right. apply* pt3_sngl_trans3. repeat apply* pt3_weaken. apply* inert_ok; apply* inert_prefix.
           *** right. repeat apply* pt3_weaken. apply* inert_ok; apply* inert_prefix.
           *** false* pf_inert_pt3_sngl_false.
      * destruct Hrc1 as [-> | Hp']; destruct Hrc2 as [-> | Hp'']; do 2 eexists; split*.
        ** split. left*. right. eapply pt3_sngl_trans3. repeat apply* pt3_weaken.
           apply inert_ok; apply* inert_prefix. auto.
        ** split. left*.
            do 2 eapply pt3_weaken in Hp'; try solve [apply* inert_ok; apply* inert_prefix].
           pose proof (pt3_invert Hi Hp Hp')
             as [? | [r1' [[= ->] [-> | ?]]]]; eauto. false* pf_inert_pt3_sngl_false.
        ** split. left*.
           do 2 eapply pt3_weaken in Hp'; try solve [apply* inert_ok; apply* inert_prefix].
           pose proof (pt3_invert Hi Hp Hp') as [? | [r1' [[= ->] [-> | HHH]]]].
           *** right. apply* pt3_sngl_trans3. repeat apply* pt3_weaken. apply* inert_ok. apply* inert_prefix.
           *** right. repeat apply* pt3_weaken. apply* inert_ok. apply* inert_prefix.
           *** false* pf_inert_pt3_sngl_false.
   - destruct_all. inversion H1.
Qed.

(** If [p] looks up to [t] in a value environment and [p]'s III-level precise type
    is [q.type], where [q]'s environment type is a tag type, then
    [t] is a path [r], and [q] and [r] are aliases. *)
Lemma lookup_step_preservation_sngl_prec3_tag: forall G γ p q t r0 Q,
    inert G ->
    wf G ->
    γ ⫶ G ->
    γ ⟦ p ⤳ t ⟧ ->
    G ⊢!!! p : {{ q }} ->
    G ⊢! q : typ_tag r0 ⪼ Q ->
    exists r r', t = defp r /\
            (q = r' \/ G ⊢!!! q : {{ r' }}) /\
            (r = r' \/ G ⊢!!! r : {{ r' }}).
Proof.
  introv Hi Hwf Hwt Hs Hp. gen t.
  pose proof (typed_paths_named (precise_to_general3 Hp)) as [px [pbs Heq]].
  dependent induction Hp; introv Hs Hq;
    destruct (lookup_step_preservation_prec2 Hi Hwf Hwt Hs H Heq)
    as [[S' [U' [u [[= ->] [Hv Hp']]]]] |
        [[S' [ds [W [U [G1 [G2 [pT [-> [Hp' [Heq' [Hds [Hrc1 Hrc2]]]]]]]]]]]] |
         [[q' [r [r' [G1 [G2 [pT [-> [[= ->] [-> [Hrc1 Hrc2]]]]]]]]]]|]]].
  - pose proof (pf_sngl_T Hi Hp') as ->. pose proof (sngl_path_lookup Hi Hwf Hwt Hp') as [? [? [Hl ?]]].
    pose proof (lookup_step_func Hl Hs) as [=].
  - pose proof (pf_sngl_T Hi Hp') as [=].
  - destruct Hrc1 as [-> | Hrc1]; destruct Hrc2 as [-> | Hrc2]; do 2 eexists; eauto; split*; split;
      [ left* | right | right | left* | right | right ]; repeat apply* pt3_weaken.
    all: apply* inert_ok; apply* inert_prefix.
  - destruct_all. subst. inversion H1.
  - pose proof (pf_sngl_T Hi Hp') as ->. pose proof (sngl_path_lookup Hi Hwf Hwt Hp') as [? [? [Hl ?]]].
    pose proof (lookup_step_func Hl Hs) as [=].
  - pose proof (pf_sngl_T Hi Hp') as [=].
  - pose proof (typ_to_lookup3 Hi Hwf Hwt Hp) as [t Hl].
    pose proof (typed_paths_named (precise_to_general3 Hp)) as [rx [rbs Heqr]].
    specialize (IHHp _ Hi Hwf Hwt eq_refl _ _ Heqr _ Hl Hq) as [r1 [r2 [-> [[-> | Hq'] [-> | Hq'']]]]].
      * destruct Hrc1 as [-> | Hp']; destruct Hrc2 as [-> | Hp'']; do 2 eexists; split*.
        ** split. left*. right. apply* pt3_sngl_trans3. repeat apply* pt3_weaken.
           apply inert_ok. apply* inert_prefix.
        ** split. left*. do 2 eapply pt3_weaken in Hp'. pose proof (pt3_invert Hi Hp Hp')
             as [? | [r1 [[= ->] [-> | ?]]]]; eauto.
           false* pf_inert_pt3_sngl_false. all: apply* inert_ok; apply* inert_prefix.
        ** split. left*. do 2 eapply pt3_weaken in Hp'; try solve [apply* inert_ok; apply* inert_prefix].
           pose proof (pt3_invert Hi Hp Hp')
             as [? | [r1 [[= ->] [-> | ?]]]].
           *** right. apply* pt3_sngl_trans3. repeat apply* pt3_weaken. eapply inert_ok, inert_prefix; eauto.
           *** right. repeat apply* pt3_weaken. eapply inert_ok, inert_prefix; eauto.
           *** false* pf_inert_pt3_sngl_false.
      * destruct Hrc1 as [-> | Hp']; destruct Hrc2 as [-> | Hp'']; do 2 eexists; split*.
        ** split. left*. right. eapply pt3_sngl_trans3. repeat apply* pt3_weaken.
           apply* inert_ok. apply* inert_prefix. auto.
        ** split. left*. do 2 eapply pt3_weaken in Hp'; try solve [apply* inert_ok; apply* inert_prefix].
           pose proof (pt3_invert Hi Hp Hp')
             as [? | [r1' [[= ->] [-> | ?]]]]; eauto. false* pf_inert_pt3_sngl_false.
        ** split. left*.
           do 2 eapply pt3_weaken in Hp'; try solve [apply* inert_ok; apply* inert_prefix].
           pose proof (pt3_invert Hi Hp Hp') as [? | [r1' [[= ->] [-> | HHH]]]].
           *** right. apply* pt3_sngl_trans3. repeat apply* pt3_weaken. apply* inert_ok. apply* inert_prefix.
           *** right. repeat apply* pt3_weaken. apply* inert_ok. apply* inert_prefix.
           *** false* pf_inert_pt3_sngl_false.
      * destruct Hrc1 as [-> | Hp']; destruct Hrc2 as [-> | Hp'']; do 2 eexists; split*.
        ** split. left*. right. apply* pt3_sngl_trans3. repeat apply* pt3_weaken.
           apply* inert_ok. apply* inert_prefix.
        ** split. left*.
           do 2 eapply pt3_weaken in Hp'; try solve [apply* inert_ok; apply* inert_prefix].
           pose proof (pt3_invert Hi Hp Hp')
             as [? | [r1 [[= ->] [-> | ?]]]]; eauto.
           false* pf_inert_pt3_sngl_false.
        ** split. left*.
            do 2 eapply pt3_weaken in Hp'; try solve [apply* inert_ok; apply* inert_prefix].
           pose proof (pt3_invert Hi Hp Hp')
             as [? | [r1 [[= ->] [-> | ?]]]].
           *** right. apply* pt3_sngl_trans3. repeat apply* pt3_weaken. apply* inert_ok; apply* inert_prefix.
           *** right. repeat apply* pt3_weaken. apply* inert_ok; apply* inert_prefix.
           *** false* pf_inert_pt3_sngl_false.
      * destruct Hrc1 as [-> | Hp']; destruct Hrc2 as [-> | Hp'']; do 2 eexists; split*.
        ** split. left*. right. eapply pt3_sngl_trans3. repeat apply* pt3_weaken.
           apply inert_ok; apply* inert_prefix. auto.
        ** split. left*.
            do 2 eapply pt3_weaken in Hp'; try solve [apply* inert_ok; apply* inert_prefix].
           pose proof (pt3_invert Hi Hp Hp')
             as [? | [r1' [[= ->] [-> | ?]]]]; eauto. false* pf_inert_pt3_sngl_false.
        ** split. left*.
           do 2 eapply pt3_weaken in Hp'; try solve [apply* inert_ok; apply* inert_prefix].
           pose proof (pt3_invert Hi Hp Hp') as [? | [r1' [[= ->] [-> | HHH]]]].
           *** right. apply* pt3_sngl_trans3. repeat apply* pt3_weaken. apply* inert_ok. apply* inert_prefix.
           *** right. repeat apply* pt3_weaken. apply* inert_ok. apply* inert_prefix.
           *** false* pf_inert_pt3_sngl_false.
   - destruct_all. inversion H1.
Qed.

(** If a [x.bs] looks up to a path [x.cs] in the value environment,
    and [x.bs]'s environment type is [T] then [T = x.cs.type]. *)
Lemma lookup_same_var_same_type G γ x bs cs T:
  inert G ->
  wf G ->
  γ ⫶ G ->
  γ ⟦ p_sel (avar_f x) bs ⤳ defp (p_sel (avar_f x) cs) ⟧ ->
  G ⊢!! p_sel (avar_f x) bs : T ->
  T = {{ p_sel (avar_f x) cs }}.
Proof.
  intros Hi Hwf Hwt. gen x bs cs T. induction Hwt; introv Hs Ht.
  - Case "s is empty"%string.
    false* lookup_empty.
  - Case "G is not empty"%string.
    destruct (classicT (x = x0)) as [<- | Hn].
    + SCase "x = x0"%string.
      pose proof (lookup_step_preservation_prec2 Hi Hwf (well_typed_push Hwt H H0 H1) Hs Ht eq_refl)
        as [[S' [U' [u [[= ->] [Hv Hp']]]]] |
            [[S' [ds [W [U' [G1 [G2 [pT [[=] [Hp' [Heq [Hds [Hrc1 Hrc2]]]]]]]]]]]] |
             [[q [r [r' [G1 [G2 [pT [[= <-] [-> [Heq [Hrc1 Hrc2]]]]]]]]]]|]]].
      rewrite <- concat_empty_r in Heq at 1.
      apply eq_sym in Heq. apply env_ok_inv in Heq as [<- [<- ->]]; try rewrite concat_empty_r in *; auto.
      pose proof (sngl_typed2 Hi Hwf Ht) as [T [rx [rbs ->]]%precise_to_general2%typed_paths_named].
      destruct Hrc1 as [-> | Hrc1];
        destruct Hrc2 as [-> | [U Hu]%precise_to_general3%typing_implies_bound];
        eauto.
      * false binds_fresh_inv; eauto.
      * apply sngl_typed3 in Hrc1 as
            [? [S Hb]%precise_to_general3%typing_implies_bound].
        false binds_fresh_inv; eauto. apply* inert_prefix. apply* wf_prefix.
      * false binds_fresh_inv; eauto.
      * destruct_all. inversion H2.
    + SCase "x <> x0"%string.
      apply pt2_strengthen_one in Ht; auto.
      apply lookup_strengthen_one in Hs; eauto. apply* IHHwt. apply* inert_prefix. apply* wf_prefix.
Qed.

(** If the path [y.bs] has II-level precise type [y.cs.type] then
    [y.bs] looks up to [y.cs] in the value environment. *)
Lemma typed_path_lookup_same_var2 G γ y bs cs :
  inert G ->
  wf G ->
  γ ⫶ G ->
  G ⊢!! p_sel (avar_f y) bs : {{ p_sel (avar_f y) cs }} ->
  γ ⟦ p_sel (avar_f y) bs ⤳ defp (p_sel (avar_f y) cs) ⟧.
Proof.
  intros Hi Hwf Hwt Hp. pose proof (typ_to_lookup2 Hi Hwf Hwt Hp) as [t Hs].
  pose proof (lookup_step_preservation_prec2 Hi Hwf Hwt Hs Hp eq_refl)
        as [[? [? [? [[= ->] [Hv ->%pf_sngl_T]]]]] |
            [[? [? [? [? [? [? [? [[= ->] [[=]%pf_sngl_T ?]]]]]]]]] |
             [[q' [r [r' [G1 [G2 [pT [-> [[= <-] [-> [Hrc1 Hrc2]]]]]]]]]]|]]]; auto.
  - proof_recipe. inversions Hv. inversions H. inversion H0.
  - apply (pt2_strengthen eq_refl Hi Hwf) in Hp.
    pose proof (wt_prefix Hwt) as [v [s1 [s2 [-> Hwt']]]].
    pose proof (wt_to_ok_γ Hwt) as Hoks.
    apply (lookup_strengthen Hoks eq_refl) in Hs.
    pose proof (inert_ok Hi) as Hok%ok_middle_inv_l.
    destruct Hrc1 as [<- | Hrc1]; destruct Hrc2 as [-> | Hrc2]; eauto.
    + apply* lookup_step_weaken.
    + apply (sngl_typed3 (inert_prefix (inert_prefix Hi))) in Hrc2
        as [T [U Hb]%precise_to_general3%typing_implies_bound].
      false binds_fresh_inv; eauto. repeat apply* wf_prefix.
    + pose proof (typing_implies_bound (precise_to_general3 Hrc1)) as [S Hb].
      false binds_fresh_inv; eauto.
    + pose proof (typing_implies_bound (precise_to_general3 Hrc1)) as [S Hb].
      false binds_fresh_inv; eauto.
  - destruct_all. inversion H0.
Qed.

(** If the path [y.bs] has III-level precise type [y.cs.type] then
    [y.bs] looks up to [y.cs] in the value environment in a finite number of steps. *)
Lemma typed_path_lookup_same_var3 G γ y bs cs :
  inert G ->
  wf G ->
  γ ⫶ G ->
  G ⊢!!! p_sel (avar_f y) bs : {{ p_sel (avar_f y) cs }} ->
  γ ⟦ defp (p_sel (avar_f y) bs) ⤳* defp (p_sel (avar_f y) cs) ⟧.
Proof.
  intros Hi Hwf Hwt Hp. dependent induction Hp.
  - apply star_one. apply* typed_path_lookup_same_var2.
  - pose proof (typed_paths_named (precise_to_general3 Hp)) as [qx [qbs ->]].
    destruct (classicT (qx = y)) as [-> | Hn].
    + specialize (IHHp _ _ _ Hi Hwf Hwt eq_refl eq_refl).
      pose proof (typed_path_lookup_same_var2 Hi Hwf Hwt H) as Hs.
      eapply star_trans. apply* star_one. auto.
    + clear IHHp.
      pose proof (typing_implies_bound (precise_to_general2 H)) as [S [G1 [G2 ->]]%binds_destruct].
      pose proof (inert_ok Hi) as Hok%ok_middle_inv_l.
      eapply pt2_strengthen in H; eauto.
      pose proof (sngl_typed2 (inert_prefix Hi) (wf_prefix Hwf) H)
        as [T [U [[-> ->] |
                  [Hn' [G1' [G2' ->]]%binds_destruct]]%binds_push_inv]%precise_to_general2%typing_implies_bound].
      * false*.
      * do 2 rewrite <- concat_assoc in Hp, Hi, Hwf. apply (pt3_strengthen eq_refl Hi Hwf) in Hp.
        apply (sngl_typed3 (inert_prefix Hi) (wf_prefix Hwf)) in Hp
          as [V [W Hb]%precise_to_general3%typing_implies_bound].
        simpl_dom. apply notin_union in Hok as [Hnu _]. false binds_fresh_inv; eauto.
Qed.

(** If [px.pbs] has III-level precise type [qx.qbs.type], and [px ≠ qx]
    then there exists a type [q'] that is [px.pbs]'s II-level precise type,
    [qx.qbs.type] is [q']'s III-level precise type, and [q']'s receiver is
    not equal to [px]. *)
Lemma prev_var_exists G p q px pbs qx qbs:
  inert G ->
  wf G ->
  p = p_sel (avar_f px) pbs ->
  q = p_sel (avar_f qx) qbs ->
  G ⊢!!! p : {{ q }} ->
  px <> qx ->
  exists p' cs q' ds rx,
    rx <> px /\
    p' = p_sel (avar_f px) cs /\
    q' = p_sel (avar_f rx) ds /\
    (p = p' \/ G ⊢!!! p : {{ p' }}) /\
    G ⊢!! p' : {{ q' }} /\
    (q' = q \/ G ⊢!!! q' : {{ q }}).
Proof.
  intros Hi Hwf -> -> Hp Hn. dependent induction Hp.
  - repeat eexists; eauto.
  - pose proof (sngl_typed2 Hi Hwf H) as [? [rx [rbs ->]]%precise_to_general2%typed_paths_named].
    destruct (classicT (rx = qx)) as [-> | Hn'].
    + do 5 eexists. split. eauto. split*.
    + specialize (IHHp _ _ _ _ Hi Hwf eq_refl eq_refl Hn')
        as [p' [cs [q' [ds [sx [Hn'' [-> [-> [Hp' [Hpq Hq]]]]]]]]]].
      destruct (classicT (px = rx)) as [-> | Hnpr].
      * eexists. exists cs. eexists. exists ds sx. repeat split*. right.
        destruct Hp' as [<- | Hnr]; eauto.
      * eexists. exists pbs. eexists. exists rbs rx. split*.
Qed.

(** If [p]'s III-level precise type is [r.type] and [r]'s environment type is
    a function type then [p] can be looked up to [r] in the value environment
    in a finite number of steps. *)
Lemma typed_path_lookup_helper G γ p r S T V :
  inert G ->
  wf G ->
  γ ⫶ G ->
  G ⊢!!! p : {{ r }} ->
  G ⊢! r : ∀(S) T ⪼ V->
  γ ⟦ defp p ⤳* defp r ⟧.
Proof.
  intros Hi Hwf Hwt. gen p r S T V. induction Hwt; introv Hp Hr.
  - Case "G is empty"%string.
    apply precise_to_general in Hr. false* typing_empty_false.
  - Case "G is not empty"%string.
    destruct p as [x' bs].
    pose proof (typed_paths_named (precise_to_general3 Hp)) as [px [pbs [= -> ->]]].
    destruct (classicT (x = px)) as [-> | Hn].
    + SCase "x = px"%string.
      lets Hwt': (well_typed_push Hwt H H0 H1).
      pose proof (typ_to_lookup3 Hi Hwf Hwt' Hp) as [t Hlt].
      pose proof (lookup_step_preservation_sngl_prec3 Hi Hwf Hwt' Hlt Hp Hr)
        as [r1 [r2 [-> [Hrc Hrc']]]].
      pose proof (sngl_typed3 Hi Hwf Hp) as [? [rx [rbs ->]]%precise_to_general3%typed_paths_named].
      destruct (classicT (px = rx)) as [-> | Hn].
      { apply* typed_path_lookup_same_var3. }
      pose proof (prev_var_exists Hi Hwf eq_refl eq_refl Hp Hn) as
          [p' [cs' [q' [ds [sx [Hn' [-> [-> [Hpp' [Hp'q' Hq'q]]]]]]]]]].
      pose proof (typ_to_lookup2 Hi Hwf Hwt' Hp'q') as [t Hst].
      pose proof (lookup_step_preservation_prec2 Hi Hwf Hwt' Hst Hp'q' eq_refl)
        as [[S' [U' [u [[= ->] [Hv ->%pf_sngl_T]]]]] |
            [[S' [ds' [W [U' [G1 [G2 [pT [-> [[=]%pf_sngl_T [Heq [Hds [Hrc1 Hrc2]]]]]]]]]]]] |
             [[q' [r [r' [G1 [G2 [pT [[= ->] [[= <-] [Heq' [Hrc1 Hrc2]]]]]]]]]]|]]]; auto.
      { simpl in *. proof_recipe. inversions Hv. inversions H2. inversion H3. }
      pose proof (inert_prefix Hi) as Hi'.
      rewrite <- concat_empty_r in Heq' at 1. apply env_ok_inv'  in Heq' as [-> [-> <-]];
                                               try rewrite concat_empty_r in *; auto.
      assert (exists q'x q'bs, q' = p_sel (avar_f q'x) q'bs) as [q'x [q'bs ->]]. {
        destruct Hrc2 as [-> | Hq'%precise_to_general3].
        - destruct Hrc1 as [<- | Hq']; eauto.
          pose proof (sngl_typed3 (inert_prefix Hi) (wf_prefix Hwf) Hq') as [? Hq''%precise_to_general3].
          apply* typed_paths_named.
        - apply* typed_paths_named.
      }
      apply star_trans with (b:=defp (p_sel (avar_f px) cs')). {
        destruct Hpp' as [[= ->] | Hpp'].
        - apply* star_refl.
        - eapply (typed_path_lookup_same_var3 Hi); auto.
      }
      clear Hpp'.
      assert (p_sel (avar_f rx) rbs = r2) as <-. {
        destruct Hrc as [<- | Ht]; auto. false (pf_inert_pt3_sngl_false Hi Hr Ht); auto.
      }
      clear Hrc.
      apply star_trans with (b:=defp (p_sel (avar_f q'x) q'bs)).
      { apply* star_one. }
      apply* lookup_weaken.
      { apply* wt_to_ok_γ. }
      pose proof (wf_prefix Hwf) as Hwf'.
      apply pf_strengthen in Hr; auto. clear Hrc' Hst Hp'q' Hp.
      destruct Hq'q as [[= -> ->] | Hq'q%pt3_strengthen_one]; destruct Hrc1 as [<- | Hrc1]; destruct Hrc2 as [[= ->] | Hrc2]; subst; auto;
        try solve [apply* IHHwt; try solve [false (pf_inert_pt3_sngl_false Hi' Hr Hrc1); auto]].
        * apply* IHHwt. apply* pt3_sngl_trans3.
        * pose proof (pt3_invert Hi' Hrc1 Hq'q) as [Contra | [q' [[= ->] [[= <-] | Hqt]]]].
          ** false (pf_inert_pt3_sngl_false Hi' Hr Contra); auto.
          ** subst. apply* star_refl.
          ** apply* IHHwt.
        * pose proof (pt3_invert Hi' Hrc1 Hq'q) as [Contra | [q' [[= ->] [[= <-] | Hqt]]]].
          ** false (pf_inert_pt3_sngl_false Hi' Hr Contra); auto.
          ** apply* IHHwt.
          ** apply (pt3_sngl_trans3 Hrc2) in Hqt. apply* IHHwt.
       * destruct_all; try inversion H3.
    + SCase "x <> px"%string.
      apply pt3_strengthen_one in Hp; auto. apply lookup_weaken.
      { apply* ok_push. apply* wt_to_ok_γ. }
      pose proof (inert_prefix Hi) as Hi'. pose proof (wf_prefix Hwf) as Hwf'.
      apply* IHHwt.
      apply (sngl_typed3 Hi' Hwf') in Hp as [U Ht]. apply* pf_strengthen_from_pt3.
Qed.

(** If [p]'s III-level precise type is [r.type] and [r]'s environment type is
    a tag type then [p] can be looked up to [r] in the value environment
    in a finite number of steps. *)
Lemma typed_path_lookup_helper_tag G γ p r r0 V :
  inert G ->
  wf G ->
  γ ⫶ G ->
  G ⊢!!! p : {{ r }} ->
  G ⊢! r : typ_tag r0 ⪼ V ->
  γ ⟦ defp p ⤳* defp r ⟧.
Proof.
  intros Hi Hwf Hwt. gen p r r0 V. induction Hwt; introv Hp Hr.
  - Case "G is empty"%string.
    apply precise_to_general in Hr. false* typing_empty_false.
  - Case "G is not empty"%string.
    destruct p as [x' bs].
    pose proof (typed_paths_named (precise_to_general3 Hp)) as [px [pbs [= -> ->]]].
    destruct (classicT (x = px)) as [-> | Hn].
    + SCase "x = px"%string.
      lets Hwt': (well_typed_push Hwt H H0 H1).
      pose proof (typ_to_lookup3 Hi Hwf Hwt' Hp) as [t Hlt].
      pose proof (lookup_step_preservation_sngl_prec3_tag Hi Hwf Hwt' Hlt Hp Hr)
        as [r1 [r2 [-> [Hrc Hrc']]]].
      pose proof (sngl_typed3 Hi Hwf Hp) as [? [rx [rbs ->]]%precise_to_general3%typed_paths_named].
      destruct (classicT (px = rx)) as [-> | Hn].
      { apply* typed_path_lookup_same_var3. }
      pose proof (prev_var_exists Hi Hwf eq_refl eq_refl Hp Hn) as
          [p' [cs' [q' [ds [sx [Hn' [-> [-> [Hpp' [Hp'q' Hq'q]]]]]]]]]].
      pose proof (typ_to_lookup2 Hi Hwf Hwt' Hp'q') as [t Hst].
      pose proof (lookup_step_preservation_prec2 Hi Hwf Hwt' Hst Hp'q' eq_refl)
        as [[S' [U' [u [[= ->] [Hv ->%pf_sngl_T]]]]] |
            [[S' [ds' [W [U' [G1 [G2 [pT [-> [[=]%pf_sngl_T [Heq [Hds [Hrc1 Hrc2]]]]]]]]]]]] |
             [[q' [r [r' [G1 [G2 [pT [[= ->] [[= <-] [Heq' [Hrc1 Hrc2]]]]]]]]]]|]]]; auto.
      { simpl in *. proof_recipe. inversions Hv. inversions H2. inversion H3. }
      pose proof (inert_prefix Hi) as Hi'.
      rewrite <- concat_empty_r in Heq' at 1. apply env_ok_inv'  in Heq' as [-> [-> <-]];
                                               try rewrite concat_empty_r in *; auto.
      assert (exists q'x q'bs, q' = p_sel (avar_f q'x) q'bs) as [q'x [q'bs ->]]. {
        destruct Hrc2 as [-> | Hq'%precise_to_general3].
        - destruct Hrc1 as [<- | Hq']; eauto.
          pose proof (sngl_typed3 (inert_prefix Hi) (wf_prefix Hwf) Hq') as [? Hq''%precise_to_general3].
          apply* typed_paths_named.
        - apply* typed_paths_named.
      }
      apply star_trans with (b:=defp (p_sel (avar_f px) cs')). {
        destruct Hpp' as [[= ->] | Hpp'].
        - apply* star_refl.
        - eapply (typed_path_lookup_same_var3 Hi); auto.
      }
      clear Hpp'.
      assert (p_sel (avar_f rx) rbs = r2) as <-. {
        destruct Hrc as [<- | Ht]; auto. false (pf_inert_pt3_sngl_false Hi Hr Ht); auto.
      }
      clear Hrc.
      apply star_trans with (b:=defp (p_sel (avar_f q'x) q'bs)).
      { apply* star_one. }
      apply* lookup_weaken.
      { apply* wt_to_ok_γ. }
      pose proof (wf_prefix Hwf) as Hwf'.
      apply pf_strengthen in Hr; auto. clear Hrc' Hst Hp'q' Hp.
      destruct Hq'q as [[= -> ->] | Hq'q%pt3_strengthen_one]; destruct Hrc1 as [<- | Hrc1]; destruct Hrc2 as [[= ->] | Hrc2]; subst; auto;
        try solve [apply* IHHwt; try solve [false (pf_inert_pt3_sngl_false Hi' Hr Hrc1); auto]].
        * apply* IHHwt. apply* pt3_sngl_trans3.
        * pose proof (pt3_invert Hi' Hrc1 Hq'q) as [Contra | [q' [[= ->] [[= <-] | Hqt]]]].
          ** false (pf_inert_pt3_sngl_false Hi' Hr Contra); auto.
          ** subst. apply* star_refl.
          ** apply* IHHwt.
        * pose proof (pt3_invert Hi' Hrc1 Hq'q) as [Contra | [q' [[= ->] [[= <-] | Hqt]]]].
          ** false (pf_inert_pt3_sngl_false Hi' Hr Contra); auto.
          ** apply* IHHwt.
          ** apply (pt3_sngl_trans3 Hrc2) in Hqt. apply* IHHwt.
       * destruct_all; try inversion H3.
    + SCase "x <> px"%string.
      apply pt3_strengthen_one in Hp; auto. apply lookup_weaken.
      { apply* ok_push. apply* wt_to_ok_γ. }
      pose proof (inert_prefix Hi) as Hi'. pose proof (wf_prefix Hwf) as Hwf'.
      apply* IHHwt.
      apply (sngl_typed3 Hi' Hwf') in Hp as [U Ht]. apply* pf_strengthen_from_pt3.
Qed.

(** If [p]'s III-level precise type is a function type then [p] can be looked
    up to a value in the value environment. *)
Lemma typed_path_lookup3 G γ p T U :
  inert G ->
  wf G ->
  γ ⫶ G ->
  G ⊢!!! p: ∀(T) U ->
  exists v, γ ⟦ defp p ⤳* defv v ⟧.
Proof.
  intros Hi Hwf Hwt Hp.
  pose proof (typed_paths_named (precise_to_general3 Hp)) as [px [pbs ->]].
  apply (last_path Hi) in Hp as [Hp | [q [Hpq Hq]]].
  - inversions Hp. pose proof (typ_to_lookup1 Hi Hwf Hwt H) as [t Hs].
    destruct (lookup_step_preservation_prec1 Hi Hwf Hwt Hs H eq_refl)
          as [[S [u [-> Ht]]] |
              [[S [ds' [W [T'' [G1 [G2 [pT [-> [[= ->] [? ?]]]]]]]]]] |
               [[? [? [? [? [? [? [? [[= ->] [-> ?]]]]]]]]]|]]]; eauto.
    apply pf_sngl_U in H as [=].
    destruct_all. subst. apply pf_tag_U in H as [=].
  - inversions Hq. pose proof (pf_forall_T Hi H) as ->.
    pose proof (typed_path_lookup_helper Hi Hwf Hwt Hpq H) as Hs.
    pose proof (typ_to_lookup1 Hi Hwf Hwt H) as [t Hs'].
    pose proof (typed_paths_named (precise_to_general H)) as [qx [qbs ->]].
    destruct (lookup_step_preservation_prec1 Hi Hwf Hwt Hs' H eq_refl)
          as [[S [u [-> Ht]]] |
              [[S [ds' [W [T'' [G1 [G2 [pT [-> [[= ->] [? ?]]]]]]]]]] |
               [[? [? [? [? [? [? [? [[= ->] [-> ?]]]]]]]]]|]]].
    eexists. eapply star_trans. apply Hs. apply* star_one.
    destruct_all. inversion H1.
Qed.

(** If [p]'s III-level precise type is a function type then [p] can be looked
    up to a value in the value environment. *)
Lemma typed_path_lookup3_tag G γ p q :
  inert G ->
  wf G ->
  γ ⫶ G ->
  G ⊢!!! p: typ_tag q ->
  exists v, γ ⟦ defp p ⤳* defv v ⟧.
Proof.
  intros Hi Hwf Hwt Hp.
  pose proof (typed_paths_named (precise_to_general3 Hp)) as [px [pbs ->]].
  apply (last_path_tag Hi) in Hp as [Hp | [q' [Hpq Hq]]].
  - inversions Hp. pose proof (typ_to_lookup1 Hi Hwf Hwt H) as [t Hs].
    destruct (lookup_step_preservation_prec1 Hi Hwf Hwt Hs H eq_refl)
          as [[S [u [-> Ht]]] |
              [[S [ds' [W [T'' [G1 [G2 [pT [-> [[= ->] [? ?]]]]]]]]]] |
               [[? [? [? [? [? [? [? [[= ->] [-> ?]]]]]]]]]|]]]; eauto.
    apply pf_sngl_U in H as [=].
    destruct_all; eauto; subst. repeat eexists; eauto.
  - inversions Hq. pose proof (pf_tag_T Hi H) as ->.
    pose proof (typed_path_lookup_helper_tag Hi Hwf Hwt Hpq H) as Hs.
    pose proof (typ_to_lookup1 Hi Hwf Hwt H) as [t Hs'].
    pose proof (typed_paths_named (precise_to_general H)) as [qx [qbs ->]].
    destruct (lookup_step_preservation_prec1 Hi Hwf Hwt Hs' H eq_refl)
          as [[S [u [-> Ht]]] |
              [[S [ds' [W [T'' [G1 [G2 [pT [-> [[= ->] [? ?]]]]]]]]]] |
               [[? [? [? [? [? [? [? [[= ->] [-> ?]]]]]]]]]|]]].
    eexists. eapply star_trans. apply Hs. apply* star_one.
    destruct_all; subst. inversions H1.
    eexists. eapply star_trans. apply Hs. apply* star_one.
Qed.


(** If a path has a III-level function type then the path can be
    looked up in the value environment in a finite number of steps
    to a value of the same type. *)
Lemma corresponding_types_fun: forall G γ p S T,
    inert G ->
    wf G ->
    γ ⫶ G ->
    G ⊢!!! p: ∀(S) T ->
    (exists v, γ ⟦ defp p ⤳* defv v ⟧ /\
            G ⊢ trm_val v : ∀(S) T).
Proof.
  introv Hi Hwf Hwt Hp.
  destruct (typed_path_lookup3 Hi Hwf Hwt Hp) as [v Hs].
  lets Ht: (lookup_preservation_forall Hi Hwf Hwt Hs (precise_to_general3 Hp)). eauto.
Qed.

(** If a path has a III-level tag type then the path can be
    looked up in the value environment in a finite number of steps
    to a value of the same type. *)
Lemma corresponding_types_tag: forall G γ p q,
    inert G ->
    wf G ->
    γ ⫶ G ->
    G ⊢!!! p: typ_tag q ->
    (exists v, γ ⟦ defp p ⤳* defv v ⟧ /\
            G ⊢ trm_val v : typ_tag q).
Proof.
  introv Hi Hwf Hwt Hp.
  destruct (typed_path_lookup3_tag Hi Hwf Hwt Hp) as [v Hs].
  lets Ht: (lookup_preservation_tag Hi Hwf Hwt Hs (precise_to_general3 Hp)). eauto.
Qed.

(** ** Canonical Forms for Functions (Lemma 5.5) *)
(** If a path has a function type then it can be looked up in the value environment
    in a finite number of steps to a function that has the same function type. *)
Lemma canonical_forms_fun: forall G γ p T U,
    inert G ->
    wf G ->
    γ ⫶ G ->
    G ⊢ trm_path p : ∀(T) U ->
                   (exists L T' t, γ ⟦ defp p ⤳* defv (λ(T') t) ⟧ /\
                    G ⊢ T <: T' /\
                    (forall y, y \notin L -> G & y ~ T ⊢ open_trm y t : open_typ y U)).
Proof.
  introv Hin Hwf Hwt Hty.
  destruct (path_typ_all_to_precise Hin Hty) as [L [S [T' [Hp [Hs1 Hs2]]]]].
  destruct (corresponding_types_fun Hin Hwf Hwt Hp) as [v [P Hv]].
  destruct (val_typ_all_to_lambda Hin Hv) as [L' [S' [t [Heq [Hs1' Hs2']]]]].
  subst.
  exists (L \u L' \u (dom G)) S' t. repeat split~.
  - eapply subtyp_trans; eauto.
  - intros.
    assert (HL: y \notin L) by auto.
    assert (HL': y \notin L') by auto.
    specialize (Hs2 y HL).
    specialize (Hs2' y HL').
    apply narrow_typing with (G':=G & y ~ T) in Hs2'; auto.
    eapply ty_sub; eauto.
Qed.

Lemma canonical_forms_tag: forall G γ p r1,
    inert G ->
    wf G ->
    γ ⫶ G ->
    G ⊢ trm_path p : typ_tag r1 ->
    (exists q A r2 r3, γ ⟦ defp p ⤳* defv (val_tag q A r2 r3) ⟧ /\
               G ⊢ trm_path r2 : q↓A /\
               G ⊢ trm_path r3 : {{ r2 }} /\
               (exists U, G ⊢ trm_path r1: U) /\
               (r1 = r2 \/ G ⊢ trm_path r1 : {{ r2 }} \/ G ⊢ trm_path r2 : {{ r1 }})).
Proof.
  introv Hin Hwf Hwt Hty.
  destruct (path_typ_tag_to_precise Hin Hwf Hty) as [q [Hpq [q' Hrqq]]].
  destruct (corresponding_types_tag Hin Hwf Hwt Hpq) as [v [P Hv]].
  destruct (val_typ_tag_to_tag Hin Hv) as [p0 [A [r' [r'' [r''' [Heq [He1 [He2 He3]]]]]]]].
  subst.
  apply (pt3_exists Hin) in He1 as He1'. destruct He1' as [U1 He1'].
  lets Hes: equiv_path_to_sngl_typed_double Hin Hwf Hrqq He3 He1'.
  destruct Hes as [Hes1 [U0 Hes2]].
  repeat eexists; eauto 2. apply* precise_to_general3.
Qed.

Lemma canonical_forms_path_sel: forall G p q A,
    inert G ->
    G ⊢ trm_path p: q ↓ A ->
    exists T, G ⊢!!! q: typ_rcd {A >: T <: T}.
Proof.
  introv Hin Hsel. proof_recipe.
  lets Hr: path_sel_repl_inv' Hin Hsel.
  destruct_all. eexists; eauto.
Qed.

Lemma canonical_forms_dealias: forall γ G p q T1 T2 v r,
  inert G ->
  wf G ->
  γ ⫶ G ->
  G ⊢!!! p : T1 ->
  G ⊢!!! q : T2 ->
  γ ⟦ p ⤳!* (v, r) ⟧ ->
  γ ⟦ q ⤳!* (v, r) ⟧ ->
  p = q \/ G ⊢ trm_path p: {{q}} \/ G ⊢ trm_path q: {{p}}.
Proof.
  introv Hin Hwf Hwt Hp Hq Hdp Hdq.
  apply dealias_to_lookup_p in Hdp, Hdq.
  Check lookup_pres.
  lets Hr: lookup_pres Hin Hwf Hwt Hp Hdp. destruct Hr as [U Hr].
  lets Hpr: lookup_sngl Hin Hwf Hwt Hp Hdp.
  lets Hqr: lookup_sngl Hin Hwf Hwt Hq Hdq.
  destruct Hpr as [Heq1 | Hs1]; destruct Hqr as [Heq2 | Hs2]; subst; eauto.
  - right. left.
    eapply ty_sub. apply Hs1.
    eapply subtyp_sngl_qp. exact Hs2.
    apply* precise_to_general3. apply repl_intro_sngl.
Qed.

Lemma repl_intro_sel: forall p q A,
    repl_typ p q (p↓A) (q↓A).
Proof.
  introv.
  replace (p↓A) with (p •• nil ↓ A).
  replace (q↓A) with (q •• nil ↓ A).
  - auto.
  - destruct* q.
  - destruct* p.
Qed.
