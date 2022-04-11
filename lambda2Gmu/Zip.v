Set Implicit Arguments.
Require Import List.
Require Import TLC.LibTactics.
Require Import Psatz.
Open Scope list_scope.

Section Zip.
  Variables A B:Type.
  Variable R : A -> B -> Prop.

  Fixpoint zip la lb : list (A * B) :=
  match la,lb with
  | a::lla, b::llb => (a,b) :: zip lla llb
  | _, _ => nil
  end.

  Fixpoint zipWith {C} (f : A -> B -> C) la lb : list C :=
    match la,lb with
    | a::lla, b::llb => (f a b) :: zipWith f lla llb
    | _, _ => nil
    end.

  Lemma zipWithIsMappedZip : forall C (f : A -> B -> C) la lb,
      zipWith f la lb = map (fun p: A*B => let (a,b) := p in f a b) (zip la lb).
    induction la; intros; cbn; auto.
    destruct lb; auto.
    cbn. f_equal. auto.
  Qed.

  Lemma F2_iff_In_zip : forall la lb,
    Forall2 R la lb <-> (length la = length lb /\ forall a b, In (a,b) (zip la lb) -> R a b).
  Proof.
    intros la lb.
    constructor.
    - generalize la lb.
      induction 1; simpl; intuition; congruence.
    - generalize la lb.
      induction la0; intros lb0 [Hlen HzipR].
      + destruct lb0.
        * econstructor.
        * cbn in Hlen. congruence.
      + destruct lb0.
        * cbn in Hlen. congruence.
        * econstructor.
          -- apply HzipR. econstructor. eauto.
          -- apply IHla0.
             split.
             ++ cbn in Hlen. congruence.
             ++ intros.
                apply HzipR.
                cbn. eauto.
  Qed.

  Lemma F2_from_zip : forall la lb,
      length la = length lb ->
      (forall a b, In (a,b) (zip la lb) -> R a b) ->
      Forall2 R la lb.
    intros.
    apply F2_iff_In_zip.
    eauto.
  Qed.

End Zip.

Ltac listin :=
  match goal with
  | |- List.In ?e (?h :: ?t) =>
    cbn; solve [right* | left*]
  end.

#[export] Hint Extern 4 (List.In _ (_ :: _)) => (cbn; solve [left* | right*]) : listin.

Lemma forall2_from_snd : forall T1 T2 (P : T1 -> T2 -> Prop) (As : list T1) (Bs : list T2) (B : T2),
    List.Forall2 P As Bs ->
    List.In B Bs ->
    exists A, (List.In A As /\ List.In (A,B) (zip As Bs) /\ P A B).
  induction 1.
  - intros. contradiction.
  - introv Bin.
    inversions Bin.
    + exists x. splits*.
      * eauto with listin.
      * constructor*.
    + lets [A [InA PA]]: IHForall2 H1.
      exists A. splits*.
      * eauto with listin.
      * cbn. right*.
Qed.

Lemma forall2_from_snd_zip : forall T1 T2 (P : T1 -> T2 -> Prop) (As : list T1) (Bs : list T2) (B : T2),
    length As = length Bs ->
    (forall a b, In (a,b) (zip As Bs) -> P a b) ->
    List.In B Bs ->
    exists A, (List.In A As /\ List.In (A,B) (zip As Bs) /\ P A B).
  intros.
  eapply forall2_from_snd; eauto.
  apply F2_iff_In_zip. eauto.
Qed.

Lemma nth_error_implies_zip : forall AT BT (As : list AT) (Bs : list BT) i A,
    List.nth_error As i = Some A ->
    List.length As = List.length Bs ->
    exists B, List.nth_error Bs i = Some B /\ List.In (A, B) (zip As Bs).
  induction As as [| Ah Ats]; introv ntherror lengtheq.
  - lets: List.nth_error_In ntherror.
    contradiction.
  - destruct Bs as [| Bh Bts]; cbn in lengtheq; try lia.
    destruct i.
    + cbn in ntherror.
      assert (Ah = A); try congruence; subst.
      exists Bh.
      split*.
      cbn. left*.
    + cbn in ntherror.
      assert (Hlen: length Ats = length Bts); eauto.
      lets* IH: IHAts ntherror Hlen.
      destruct IH as [B [Bnth Binzip]].
      exists B.
      split*.
      cbn. right*.
Qed.

Lemma zip_swap : forall AT BT As Bs (A : AT) (B : BT),
    List.In (A,B) (zip As Bs) ->
    List.In (B,A) (zip Bs As).
  induction As; intros; destruct Bs; cbn in *; try congruence.
  destruct H.
  - inversions H. left*.
  - right*.
Qed.

Lemma nth_error_implies_zip_swap : forall AT BT (As : list AT) (Bs : list BT) i B,
    List.nth_error Bs i = Some B ->
    List.length As = List.length Bs ->
    exists A, List.nth_error As i = Some A /\ List.In (A, B) (zip As Bs).
  intros.
  lets [A ?]: nth_error_implies_zip As H.
  - symmetry. trivial.
  - exists A. split*. apply* zip_swap.
Qed.

Lemma nth_error_zip_split : forall i AT BT (As : list AT) (Bs : list BT) A B,
    List.nth_error (zip As Bs) i = Some (A, B) ->
    List.nth_error As i = Some A /\ List.nth_error Bs i = Some B.
  induction i; destruct As; destruct Bs; intros; try (cbn in *; congruence).
  - cbn in *. inversions H; eauto.
  - cbn in *.
    lets* IH: IHi H.
Qed.

Lemma nth_error_zip_merge : forall i AT BT (As : list AT) (Bs : list BT) A B,
    List.nth_error As i = Some A /\ List.nth_error Bs i = Some B ->
    List.nth_error (zip As Bs) i = Some (A, B).
  induction i; destruct As; destruct Bs; introv [Ha Hb]; try (inversions Ha; inversions Hb; cbn in *; congruence).
  cbn in *.
  apply* IHi.
Qed.

Lemma Inzip_to_nth_error : forall AT BT (As : list AT) (Bs : list BT) A B,
    List.In (A, B) (zip As Bs) ->
    exists i, List.nth_error As i = Some A /\ List.nth_error Bs i = Some B.
  introv inzip.
  lets* [i Hin]: List.In_nth_error inzip.
  lets*: nth_error_zip_split Hin.
Qed.

Lemma Inzip_from_nth_error : forall AT BT (As : list AT) (Bs : list BT) A B i,
    List.nth_error As i = Some A ->
    List.nth_error Bs i = Some B ->
    List.In (A, B) (zip As Bs).
  introv HA HB.
  apply List.nth_error_In with i.
  apply* nth_error_zip_merge.
Qed.

Lemma nth_error_map : forall i A B (F : A -> B) (ls : list A) (b : B),
    List.nth_error (List.map F ls) i = Some b ->
    exists a, (List.nth_error ls i = Some a /\ F a = b).
  induction i; destruct ls; introv Hnth_map; try (cbn in *; congruence).
  - cbn in *.
    inversions Hnth_map. exists a. eauto.
  - cbn in *.
    eauto.
Qed.

Lemma fst_from_zip : forall AT BT (A : AT) (B : BT) As Bs,
    In (A,B) (zip As Bs) ->
    In A As.
  induction As as [| Ah Ats]; destruct Bs as [| Bh Bts]; introv Inz; try contradiction.
  cbn in *.
  destruct Inz as [Heq | Hin]; try inversion Heq; eauto.
Qed.

Lemma snd_from_zip : forall AT BT (A : AT) (B : BT) As Bs,
    In (A,B) (zip As Bs) ->
    In B Bs.
  induction As as [| Ah Ats]; destruct Bs as [| Bh Bts]; introv Inz; try contradiction.
  cbn in *.
  destruct Inz as [Heq | Hin]; try inversion Heq; eauto.
Qed.
