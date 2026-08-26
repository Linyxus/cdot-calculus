import CDot.Weakening

/-!
# Precise flow

The value-precise and first-level path-precise judgments from
`cdot/PreciseFlow.v`.
-/

namespace CDot

variable [Signature]

inductive PreciseVal : Ctx → Val → Typ → Prop where
  | allIntro (L : Vars) :
      (∀ x, x ∉ L → Typed (G.push x T) (t.open x) (U.open x)) →
      PreciseVal G (.lambda T t) (.all T U)
  | newIntro (L : Vars) :
      (∀ x, x ∉ L →
        TypedDefs x [] (G.push x (T.open x)) (ds.open x) (T.open x)) →
      (∀ x, x ∉ L →
        Typed (G.push x (T.open x)) (.path (.var x)) ((.path p A : Typ).open x)) →
      PreciseVal G (.new p A T ds) (.bnd T)

inductive PreciseFlow : Ctx → Path → Typ → Typ → Prop where
  | bind : Env.Ok G → Env.Binds x T G → PreciseFlow G (.var x) T T
  | fld : PreciseFlow G p T (.rcd (.trm a U)) →
      PreciseFlow G (p.selectField a) U U
  | open : PreciseFlow G p T (.bnd U) → PreciseFlow G p T (U.openPath p)
  | andLeft : PreciseFlow G p T (.and U₁ U₂) → PreciseFlow G p T U₁
  | andRight : PreciseFlow G p T (.and U₁ U₂) → PreciseFlow G p T U₂

theorem PreciseFlow.toGeneralBoth {G : Ctx} {p : Path} {T U : Typ}
    (h : PreciseFlow G p T U) : Typed G (.path p) T ∧ Typed G (.path p) U := by
  induction h with
  | bind _ hb =>
    have ht : Typed _ (.path _) _ := .var hb
    exact ⟨ht, ht⟩
  | fld _ ih =>
    have ht := Typed.newElim ih.2
    exact ⟨ht, ht⟩
  | «open» _ ih => exact ⟨ih.1, Typed.recElim ih.2⟩
  | andLeft _ ih => exact ⟨ih.1, (Typed.sub ih.2 Subtyp.andLeft)⟩
  | andRight _ ih => exact ⟨ih.1, (Typed.sub ih.2 Subtyp.andRight)⟩

theorem PreciseFlow.toGeneral {G : Ctx} {p : Path} {T U : Typ}
    (h : PreciseFlow G p T U) : Typed G (.path p) U := h.toGeneralBoth.2

theorem PreciseVal.toGeneral {G : Ctx} {v : Val} {T : Typ}
    (h : PreciseVal G v T) : Typed G (.val v) T := by
  cases h with
  | allIntro L hbody => exact .allIntro L hbody
  | newIntro L hdefs hself => exact .newIntro L hdefs hself

theorem PreciseVal.inertTyp {G : Ctx} {v : Val} {T : Typ}
    (h : PreciseVal G v T) : InertTyp T := by
  cases h with
  | allIntro => exact .all
  | @newIntro p A G T ds L hdefs hself =>
      obtain ⟨x, hx⟩ := Finset.exists_nat_subset_range (L ∪ T.fv)
      have hxfresh : x ∉ L ∪ T.fv := by
        intro hmem
        exact (Nat.lt_irrefl x) (Finset.mem_range.mp (hx hmem))
      have hxL : x ∉ L := by aesop
      have hxT : x ∉ T.fv := by aesop
      obtain ⟨labels, hrecord⟩ := (hdefs x hxL).recordType
      exact .bnd (hrecord.closeOpenRec x 0 hxT rfl)

theorem Inert.bindsTyp {G : Ctx} {x : Var} {T : Typ}
    (hi : Inert G) (hb : Env.Binds x T G) : InertTyp T := by
  induction hi with
  | empty => exact False.elim hb.empty_false
  | @push G y U hi hU hf ih =>
      cases hb with
      | here => exact hU
      | there hne hb => exact ih hb

theorem PreciseFlow.inertSngl {G : Ctx} {p : Path} {T U : Typ}
    (hi : Inert G) (h : PreciseFlow G p T U) :
    InertSngl T ∧ (InertSngl U ∨ RecordType U) := by
  induction h with
  | bind hok hb =>
      have hT : InertSngl _ := Or.inl (hi.bindsTyp hb)
      exact ⟨hT, Or.inl hT⟩
  | fld h ih =>
      obtain ⟨hT, hprecise⟩ := ih
      rcases hprecise with hbad | hrecord
      · exact False.elim hbad.rcd_false
      · exact ⟨hrecord.singleTrm, Or.inl hrecord.singleTrm⟩
  | «open» h ih =>
      obtain ⟨hT, hprecise⟩ := ih
      rcases hprecise with hbnd | hbad
      · exact ⟨hT, Or.inr (hbnd.bnd_record.openPath _)⟩
      · exact False.elim hbad.bnd_false
  | andLeft h ih =>
      obtain ⟨hT, hprecise⟩ := ih
      rcases hprecise with hbad | hrecord
      · exact False.elim hbad.and_false
      · exact ⟨hT, Or.inr hrecord.andLeft⟩
  | andRight h ih =>
      obtain ⟨hT, hprecise⟩ := ih
      rcases hprecise with hbad | hrecord
      · exact False.elim hbad.and_false
      · exact ⟨hT, Or.inr hrecord.andRight⟩

theorem PreciseFlow.bot_false {G : Ctx} {p : Path} {T : Typ}
    (hi : Inert G) (h : PreciseFlow G p T .bot) : False := by
  rcases (h.inertSngl hi).2 with hbot | hbot
  · rcases hbot with hbot | ⟨q, hbot⟩ <;> cases hbot
  · obtain ⟨labels, hbot⟩ := hbot
    cases hbot

theorem PreciseFlow.path_false {G : Ctx} {p q : Path}
    {A : Signature.TypLabel} {T : Typ}
    (hi : Inert G) (h : PreciseFlow G p T (.path q A)) : False := by
  rcases (h.inertSngl hi).2 with hpath | hpath
  · rcases hpath with hpath | ⟨r, hpath⟩ <;> cases hpath
  · obtain ⟨labels, hpath⟩ := hpath
    cases hpath

theorem PreciseFlow.sourceNamed {G : Ctx} {p : Path} {T U : Typ}
    (h : PreciseFlow G p T U) : p.Named :=
  h.toGeneral.pathNamed

theorem PreciseFlow.reset {G : Ctx} {p : Path} {T U : Typ}
    (h : PreciseFlow G p T U) : PreciseFlow G p T T := by
  induction h with
  | bind hok hb => exact .bind hok hb
  | fld h ih => exact .fld h
  | «open» h ih => exact ih
  | andLeft h ih => exact ih
  | andRight h ih => exact ih

theorem PreciseFlow.mono {G G' : Ctx} {p : Path} {T U : Typ}
    (h : PreciseFlow G p T U) (he : Env.Extends G G') (hok : Env.Ok G') :
    PreciseFlow G' p T U := by
  induction h with
  | bind _ hb => exact .bind hok (he hb)
  | fld _ ih => exact .fld ih
  | «open» _ ih => exact .open ih
  | andLeft _ ih => exact .andLeft ih
  | andRight _ ih => exact .andRight ih

theorem PreciseFlow.strengthenPush {G : Ctx} {y x : Var} {V T U : Typ}
    {fields : Fields}
    (h : PreciseFlow (G.push y V) (.select (.free x) fields) T U)
    (hxy : x ≠ y) : PreciseFlow G (.select (.free x) fields) T U := by
  generalize heq : Path.select (.free x) fields = p at h
  induction h generalizing x fields with
  | bind hok hb =>
      simp only [Path.var] at heq
      injection heq with havar hfields
      cases havar
      cases hfields
      have hokG : Env.Ok G := by
        change List.Nodup (y :: G.map Prod.fst) at hok
        exact hok.tail
      exact .bind hokG (hb.push_ne_inv hxy)
  | fld h ih =>
      rename_i p T a U
      cases p with
      | select av rest =>
          simp only [Path.selectField] at heq
          injection heq with havar hfields
          cases havar
          cases fields with
          | nil => cases hfields
          | cons b fields =>
              injection hfields with hab hrest
              cases hab
              exact .fld (ih hxy rfl)
  | «open» h ih => exact .open (ih hxy heq)
  | andLeft h ih => exact .andLeft (ih hxy heq)
  | andRight h ih => exact .andRight (ih hxy heq)

theorem PreciseFlow.envAll_eq {G : Ctx} {p : Path} {S T U : Typ}
    (h : PreciseFlow G p (.all S T) U) : U = .all S T := by
  generalize heq : Typ.all S T = E at h
  induction h with
  | bind _ _ => rfl
  | fld _ _ => rfl
  | «open» _ ih =>
      have := ih heq
      rw [← heq] at this
      contradiction
  | andLeft _ ih =>
      have := ih heq
      rw [← heq] at this
      contradiction
  | andRight _ ih =>
      have := ih heq
      rw [← heq] at this
      contradiction

theorem PreciseFlow.envSngl_eq {G : Ctx} {p q : Path} {U : Typ}
    (h : PreciseFlow G p (.sngl q) U) : U = .sngl q := by
  generalize heq : Typ.sngl q = E at h
  induction h with
  | bind _ _ => rfl
  | fld _ _ => rfl
  | «open» _ ih =>
      have := ih heq
      rw [← heq] at this
      contradiction
  | andLeft _ ih =>
      have := ih heq
      rw [← heq] at this
      contradiction
  | andRight _ ih =>
      have := ih heq
      rw [← heq] at this
      contradiction

theorem PreciseFlow.backtrackRecord {G : Ctx} {p : Path}
    {a : Signature.TrmLabel} {T U : Typ}
    (h : PreciseFlow G (p.selectField a) T U) :
    ∃ S, PreciseFlow G p S (.rcd (.trm a T)) := by
  generalize heq : p.selectField a = r at h
  induction h with
  | bind hok hb =>
      cases p with
      | select x fields =>
          simp only [Path.selectField, Path.var] at heq
          cases heq
  | fld h ih =>
      rename_i p' S b V
      obtain ⟨rfl, rfl⟩ := Path.selectField_injective heq
      exact ⟨S, h⟩
  | «open» h ih => exact ih heq
  | andLeft h ih => exact ih heq
  | andRight h ih => exact ih heq

theorem PreciseFlow.bndTarget {G : Ctx} {p : Path} {T U : Typ}
    (hi : Inert G) (h : PreciseFlow G p (.bnd T) U) :
    U = .bnd T ∨ RecordType U := by
  generalize heq : Typ.bnd T = S at h
  induction h generalizing T with
  | bind hok hb =>
      cases heq
      exact Or.inl rfl
  | fld h ih =>
      cases heq
      exact Or.inl rfl
  | «open» h ih =>
      rename_i p S V
      rcases ih heq with hsame | hbad
      · have hbnd : V.bnd = T.bnd := hsame.trans heq.symm
        have hVT : V = T := Typ.bnd.inj hbnd
        subst V
        have hinert := (h.inertSngl hi).1
        rw [← heq] at hinert
        have hrecord := hinert.bnd_record
        exact Or.inr (hrecord.openPath p)
      · exact False.elim hbad.bnd_false
  | andLeft h ih =>
      rcases ih heq with hbad | hrecord
      · have himpossible : _ = Typ.bnd T := hbad.trans heq.symm
        cases himpossible
      · exact Or.inr hrecord.andLeft
  | andRight h ih =>
      rcases ih heq with hbad | hrecord
      · have himpossible : _ = Typ.bnd T := hbad.trans heq.symm
        cases himpossible
      · exact Or.inr hrecord.andRight

theorem PreciseFlow.allSource_eq {G : Ctx} {p : Path} {S T U : Typ}
    (hi : Inert G) (h : PreciseFlow G p U (.all S T)) :
    U = .all S T := by
  rcases (h.inertSngl hi).1 with hinert | ⟨q, rfl⟩
  · cases hinert with
    | all => exact h.envAll_eq.symm
    | @bnd V labels hrecord =>
        rcases h.bndTarget hi with hbad | hbad
        · cases hbad
        · obtain ⟨labels, hbad⟩ := hbad
          cases hbad
  · have hbad := h.envSngl_eq
    cases hbad

theorem PreciseFlow.recordHas_of_bnd {G : Ctx} {p : Path} {T U : Typ}
    {D : Dec} (hi : Inert G) (h : PreciseFlow G p (.bnd T) U)
    (hhas : RecordHas U D) : RecordHas (T.openPath p) D := by
  generalize heq : Typ.bnd T = S at h
  induction h generalizing T D with
  | bind hok hb =>
      cases heq
      cases hhas
  | fld h ih =>
      cases heq
      cases hhas
  | «open» h ih =>
      rename_i p S V
      have hbnd := h
      rw [← heq] at hbnd
      rcases hbnd.bndTarget hi with hsame | hbad
      · have hVT : V = T := Typ.bnd.inj hsame
        subst V
        exact hhas
      · exact False.elim hbad.bnd_false
  | andLeft h ih =>
      exact ih (.andLeft hhas) heq
  | andRight h ih =>
      exact ih (.andRight hhas) heq

theorem PreciseFlow.decTyp_unique {G : Ctx} {p : Path} {T : Typ}
    {A : Signature.TypLabel} {S₁ S₂ : Typ} (hi : Inert G)
    (h₁ : PreciseFlow G p (.bnd T) (.rcd (.typ A S₁ S₁)))
    (h₂ : PreciseFlow G p (.bnd T) (.rcd (.typ A S₂ S₂))) : S₁ = S₂ := by
  have hrecord := ((h₁.inertSngl hi).1).bnd_record.openPath p
  obtain ⟨labels, hrecord⟩ := hrecord
  exact hrecord.typ_member_unique
    (h₁.recordHas_of_bnd hi .one) (h₂.recordHas_of_bnd hi .one)

theorem PreciseFlow.recordSource_bnd {G : Ctx} {p : Path} {T : Typ}
    {D : Dec} (hi : Inert G) (h : PreciseFlow G p T (.rcd D)) :
    ∃ U, T = .bnd U := by
  rcases (h.inertSngl hi).1 with hinert | ⟨q, rfl⟩
  · cases hinert with
    | all =>
        have hbad := h.envAll_eq
        cases hbad
    | bnd hrecord => exact ⟨_, rfl⟩
  · have hbad := h.envSngl_eq
    cases hbad

theorem PreciseFlow.binds_of_var {G : Ctx} {x : Var} {T U : Typ}
    (h : PreciseFlow G (.var x) T U) : Env.Binds x T G := by
  generalize heq : Path.var x = p at h
  induction h with
  | bind hok hb =>
      cases heq
      exact hb
  | fld h ih =>
      cases ‹Path› with
      | select av fields =>
          simp only [Path.selectField, Path.var] at heq
          cases heq
  | «open» h ih => exact ih heq
  | andLeft h ih => exact ih heq
  | andRight h ih => exact ih heq

theorem PreciseFlow.receiverBinds {G : Ctx} {x : Var} {fields : Fields}
    {T U : Typ} (h : PreciseFlow G (.select (.free x) fields) T U) :
    ∃ S, Env.Binds x S G := by
  induction fields generalizing T U with
  | nil => exact ⟨T, h.binds_of_var⟩
  | cons a fields ih =>
      change PreciseFlow G
        ((Path.select (.free x) fields).selectField a) T U at h
      obtain ⟨R, hprefix⟩ := h.backtrackRecord
      exact ih hprefix

theorem PreciseFlow.source_unique {G : Ctx} {p : Path}
    {T₁ T₂ U₁ U₂ : Typ} (hi : Inert G)
    (h₁ : PreciseFlow G p T₁ U₁) (h₂ : PreciseFlow G p T₂ U₂) : T₁ = T₂ := by
  cases p with
  | select av fields =>
      induction fields generalizing av T₁ T₂ U₁ U₂ with
      | nil =>
          have hn := h₁.sourceNamed
          simp only [Path.Named] at hn
          obtain ⟨x, hx⟩ := hn
          subst av
          exact (h₁.binds_of_var).functional h₂.binds_of_var
      | cons a fields ih =>
          change PreciseFlow G ((Path.select av fields).selectField a) T₁ U₁ at h₁
          change PreciseFlow G ((Path.select av fields).selectField a) T₂ U₂ at h₂
          obtain ⟨R₁, hb₁⟩ := h₁.backtrackRecord
          obtain ⟨R₂, hb₂⟩ := h₂.backtrackRecord
          have hR : R₁ = R₂ := ih av hb₁ hb₂
          subst R₂
          obtain ⟨B, hB⟩ := hb₁.recordSource_bnd hi
          subst R₁
          have hrecord := ((hb₁.inertSngl hi).1).bnd_record.openPath
            (Path.select av fields)
          obtain ⟨labels, hrecord⟩ := hrecord
          have hdec := hrecord.has_unique
            (hb₁.recordHas_of_bnd hi .one) (hb₂.recordHas_of_bnd hi .one) rfl
          exact Dec.trm.inj hdec |>.2

theorem PreciseFlow.decTypTarget_unique {G : Ctx} {p : Path}
    {T₁ T₂ S₁ S₂ : Typ} {A : Signature.TypLabel} (hi : Inert G)
    (h₁ : PreciseFlow G p T₁ (.rcd (.typ A S₁ S₁)))
    (h₂ : PreciseFlow G p T₂ (.rcd (.typ A S₂ S₂))) : S₁ = S₂ := by
  have hsource : T₁ = T₂ := h₁.source_unique hi h₂
  subst T₂
  obtain ⟨B, hB⟩ := h₁.recordSource_bnd hi
  subst T₁
  exact h₁.decTyp_unique hi h₂

theorem PreciseFlow.snglSource_eq {G : Ctx} {p q : Path} {T : Typ}
    (hi : Inert G) (h : PreciseFlow G p T (.sngl q)) : T = .sngl q := by
  rcases (h.inertSngl hi).1 with hinert | ⟨r, rfl⟩
  · cases hinert with
    | all =>
        have hbad := h.envAll_eq
        cases hbad
    | bnd hrecord =>
        rcases h.bndTarget hi with hbad | hbad
        · cases hbad
        · rcases hbad with ⟨labels, hbad⟩
          cases hbad
  · have heq := h.envSngl_eq
    exact congrArg Typ.sngl (Typ.sngl.inj heq.symm)

theorem PreciseFlow.snglFieldsElim {G : Ctx} {p q : Path}
    {T U : Typ} {fields : Fields} (hi : Inert G)
    (hs : PreciseFlow G p (.sngl q) (.sngl q))
    (hf : PreciseFlow G (p.selectFields fields) T U) : fields = [] := by
  induction fields generalizing T U with
  | nil => rfl
  | cons a fields ih =>
      rw [Path.selectFields_cons] at hf
      obtain ⟨R, hrest⟩ := hf.backtrackRecord
      have hnil := ih hrest
      subst fields
      simp only [Path.selectFields_nil] at hrest
      have hsource := hs.source_unique hi hrest
      obtain ⟨B, hB⟩ := hrest.recordSource_bnd hi
      rw [hB, hs.snglSource_eq hi] at hsource
      cases hsource

theorem PreciseFlow.snglSelect_unique {G : Ctx}
    {p q q₀ r₀ : Path} {fields fields₀ : Fields} (hi : Inert G)
    (hq : PreciseFlow G q (.sngl p) (.sngl p))
    (hq₀ : PreciseFlow G q₀ (.sngl r₀) (.sngl r₀))
    (heq : q₀.selectFields fields₀ = q.selectFields fields) :
    p.selectFields fields = r₀.selectFields fields₀ := by
  obtain ⟨rest, hleft | hright⟩ := Path.selectFields_comparable heq
  · rw [hleft] at hq₀
    have hnil := hq.snglFieldsElim hi hq₀
    rw [hnil] at hleft
    simp only [Path.selectFields_nil] at hleft
    rw [hnil, Path.selectFields_nil] at hq₀
    subst q₀
    have htarget := hq.source_unique hi hq₀
    have hp : p = r₀ := Typ.sngl.inj htarget
    subst p
    have hfields := q.selectFields_right_injective heq
    subst fields₀
    rfl
  · rw [hright] at hq
    have hnil := hq₀.snglFieldsElim hi hq
    rw [hnil] at hright
    simp only [Path.selectFields_nil] at hright
    rw [hnil, Path.selectFields_nil] at hq
    subst q
    have htarget := hq.source_unique hi hq₀
    have hp : p = r₀ := Typ.sngl.inj htarget
    subst r₀
    have hfields := q₀.selectFields_right_injective heq
    subst fields₀
    rfl

theorem PreciseFlow.recordTypeSource_bnd {G : Ctx} {p : Path} {T U : Typ}
    (hi : Inert G) (h : PreciseFlow G p T U) (hr : RecordType U) :
    ∃ V, T = .bnd V := by
  rcases (h.inertSngl hi).1 with hinert | ⟨q, rfl⟩
  · cases hinert with
    | all =>
        have heq := h.envAll_eq
        rw [heq] at hr
        obtain ⟨labels, hr⟩ := hr
        cases hr
    | bnd hrecord => exact ⟨_, rfl⟩
  · have heq := h.envSngl_eq
    rw [heq] at hr
    obtain ⟨labels, hr⟩ := hr
    cases hr

theorem PreciseVal.new_type_eq {G : Ctx} {r : Path} {A : Signature.TypLabel}
    {T U : Typ} {ds : Defs} (h : PreciseVal G (.new r A T ds) U) : U = .bnd T := by
  cases h
  rfl

end CDot
