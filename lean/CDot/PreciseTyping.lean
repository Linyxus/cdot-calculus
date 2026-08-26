import CDot.PreciseFlow
import CDot.Sequences

/-! # Second- and third-level precise typing -/

namespace CDot

variable [Signature]

inductive PreciseTyping2 : Ctx → Path → Typ → Prop where
  | flow : PreciseFlow G p T U → PreciseTyping2 G p U
  | snglTrans : PreciseTyping2 G p (.sngl q) →
      PreciseTyping2 G (q.selectField a) U →
      PreciseTyping2 G (p.selectField a) (.sngl (q.selectField a))

inductive PreciseTyping3 : Ctx → Path → Typ → Prop where
  | precise : PreciseTyping2 G p T → PreciseTyping3 G p T
  | snglTrans : PreciseTyping2 G p (.sngl q) →
      PreciseTyping3 G q T → PreciseTyping3 G p T

theorem PreciseTyping2.toGeneral {G : Ctx} {p : Path} {T : Typ}
    (h : PreciseTyping2 G p T) : Typed G (.path p) T := by
  induction h with
  | flow h => exact h.toGeneral
  | snglTrans _ _ ihp ihq => exact Typed.pathElim ihp ihq

theorem PreciseTyping3.toGeneral {G : Ctx} {p : Path} {T : Typ}
    (h : PreciseTyping3 G p T) : Typed G (.path p) T := by
  induction h with
  | precise h => exact h.toGeneral
  | snglTrans hp hq ihq => exact Typed.sngl hp.toGeneral ihq

theorem PreciseTyping2.andLeft {G : Ctx} {p : Path} {T U : Typ}
    (h : PreciseTyping2 G p (.and T U)) : PreciseTyping2 G p T := by
  cases h with
  | flow h => exact .flow (.andLeft h)

theorem PreciseTyping2.andRight {G : Ctx} {p : Path} {T U : Typ}
    (h : PreciseTyping2 G p (.and T U)) : PreciseTyping2 G p U := by
  cases h with
  | flow h => exact .flow (.andRight h)

theorem PreciseTyping3.andLeft {G : Ctx} {p : Path} {T U : Typ}
    (h : PreciseTyping3 G p (.and T U)) : PreciseTyping3 G p T := by
  generalize heq : Typ.and T U = V at h
  induction h with
  | precise h =>
      cases heq
      exact .precise h.andLeft
  | snglTrans hp hq ih => exact .snglTrans hp (ih heq)

theorem PreciseTyping3.andRight {G : Ctx} {p : Path} {T U : Typ}
    (h : PreciseTyping3 G p (.and T U)) : PreciseTyping3 G p U := by
  generalize heq : Typ.and T U = V at h
  induction h with
  | precise h =>
      cases heq
      exact .precise h.andRight
  | snglTrans hp hq ih => exact .snglTrans hp (ih heq)

theorem PreciseTyping2.bot_false {G : Ctx} {p : Path}
    (hi : Inert G) (h : PreciseTyping2 G p .bot) : False := by
  cases h with
  | flow h => exact h.bot_false hi

theorem PreciseTyping3.bot_false {G : Ctx} {p : Path}
    (hi : Inert G) (h : PreciseTyping3 G p .bot) : False := by
  generalize heq : Typ.bot = T at h
  induction h with
  | precise h =>
      cases heq
      exact h.bot_false hi
  | snglTrans _ _ ih => exact ih heq

theorem PreciseTyping2.bndElim {G : Ctx} {p : Path} {T : Typ}
    (h : PreciseTyping2 G p (.bnd T)) :
    PreciseTyping2 G p (T.openPath p) := by
  cases h with
  | flow h => exact .flow (.open h)

theorem PreciseTyping3.bndCases {G : Ctx} {p : Path} {T : Typ}
    (h : PreciseTyping3 G p (.bnd T)) :
    PreciseTyping3 G p (T.openPath p) ∨
      ∃ q U, PreciseTyping3 G p (.sngl q) ∧
        PreciseTyping2 G q U ∧ PreciseTyping3 G p (T.openPath q) := by
  generalize heq : Typ.bnd T = V at h
  induction h generalizing T with
  | precise h =>
      cases heq
      exact Or.inl (.precise h.bndElim)
  | snglTrans hs h ih =>
      rename_i p₀ q₀ W
      rcases ih heq with hopen | ⟨q, U, hpq, hq, hopen⟩
      · have hexists : ∃ U, PreciseTyping2 G q₀ U := by
          cases h with
          | precise h => exact ⟨_, h⟩
          | snglTrans hs _ => exact ⟨_, hs⟩
        obtain ⟨U, hq⟩ := hexists
        exact Or.inr ⟨_, U, .precise hs, hq, .snglTrans hs hopen⟩
      · exact Or.inr ⟨q, U, .snglTrans hs hpq, hq,
          .snglTrans hs hopen⟩

theorem PreciseTyping2.backtrack {G : Ctx} {p : Path}
    {a : Signature.TrmLabel} {T : Typ}
    (h : PreciseTyping2 G (p.selectField a) T) :
    ∃ U, PreciseTyping2 G p U := by
  generalize heq : p.selectField a = r at h
  induction h with
  | flow h =>
      rw [← heq] at h
      obtain ⟨S, hS⟩ := h.backtrackRecord
      exact ⟨_, .flow hS⟩
  | snglTrans hp hq ihp ihq =>
      rename_i p' q b U
      obtain ⟨rfl, rfl⟩ := Path.selectField_injective heq
      exact ⟨_, hp⟩

theorem PreciseTyping3.backtrack {G : Ctx} {p : Path}
    {a : Signature.TrmLabel} {T : Typ}
    (h : PreciseTyping3 G (p.selectField a) T) :
    ∃ U, PreciseTyping3 G p U := by
  cases h with
  | precise h =>
      obtain ⟨U, hU⟩ := h.backtrack
      exact ⟨U, .precise hU⟩
  | snglTrans hp hq =>
      obtain ⟨U, hU⟩ := hp.backtrack
      exact ⟨U, .precise hU⟩

theorem PreciseTyping3.snglTrans3 {G : Ctx} {p q : Path} {T : Typ}
    (hp : PreciseTyping3 G p (.sngl q)) (hq : PreciseTyping3 G q T) :
    PreciseTyping3 G p T := by
  generalize heq : Typ.sngl q = U at hp
  induction hp with
  | precise hp =>
      cases heq
      exact .snglTrans hp hq
  | snglTrans hp hrest ih => exact .snglTrans hp (ih heq)

theorem PreciseTyping2.mono {G G' : Ctx} {p : Path} {T : Typ}
    (h : PreciseTyping2 G p T) (he : Env.Extends G G') (hok : Env.Ok G') :
    PreciseTyping2 G' p T := by
  induction h with
  | flow h => exact .flow (h.mono he hok)
  | snglTrans hp hq ihp ihq => exact .snglTrans ihp ihq

theorem PreciseTyping3.mono {G G' : Ctx} {p : Path} {T : Typ}
    (h : PreciseTyping3 G p T) (he : Env.Extends G G') (hok : Env.Ok G') :
    PreciseTyping3 G' p T := by
  induction h with
  | precise h => exact .precise (h.mono he hok)
  | snglTrans hp hq ih => exact .snglTrans (hp.mono he hok) ih

theorem PreciseTyping2.fieldTrans {G : Ctx} {p q : Path} {fields : Fields}
    {T : Typ} (hp : PreciseTyping2 G p (.sngl q))
    (hq : PreciseTyping2 G (q.selectFields fields) T) :
    PreciseTyping2 G (p.selectFields fields) (.sngl (q.selectFields fields)) := by
  induction fields generalizing T with
  | nil => simpa only [Path.selectFields_nil] using hp
  | cons a fields ih =>
      rw [Path.selectFields_cons] at hq ⊢
      obtain ⟨U, hbase⟩ := hq.backtrack
      exact .snglTrans (ih hbase) hq

theorem PreciseTyping2.inertSngl {G : Ctx} {p : Path} {T : Typ}
    (hi : Inert G) (h : PreciseTyping2 G p T) :
    InertSngl T ∨ RecordType T := by
  cases h with
  | flow h => exact (h.inertSngl hi).2
  | snglTrans => exact Or.inl (Or.inr ⟨_, rfl⟩)

theorem PreciseTyping3.inertSngl {G : Ctx} {p : Path} {T : Typ}
    (hi : Inert G) (h : PreciseTyping3 G p T) :
    InertSngl T ∨ RecordType T := by
  induction h with
  | precise h => exact h.inertSngl hi
  | snglTrans hp hq ih => exact ih

theorem PreciseTyping2.path_false {G : Ctx} {p q : Path}
    {A : Signature.TypLabel} (hi : Inert G)
    (h : PreciseTyping2 G p (.path q A)) : False := by
  cases h with
  | flow h => exact h.path_false hi

theorem PreciseTyping3.path_false {G : Ctx} {p q : Path}
    {A : Signature.TypLabel} (hi : Inert G)
    (h : PreciseTyping3 G p (.path q A)) : False := by
  generalize heq : Typ.path q A = U at h
  induction h with
  | precise h =>
      cases heq
      exact h.path_false hi
  | snglTrans hp hq ih => exact ih heq

theorem PreciseTyping3.precise2Exists {G : Ctx} {p : Path} {T : Typ}
    (h : PreciseTyping3 G p T) : ∃ U, PreciseTyping2 G p U := by
  induction h with
  | precise h => exact ⟨_, h⟩
  | snglTrans hp hq ih => exact ⟨_, hp⟩

theorem PreciseTyping3.last {G : Ctx} {p : Path} {T : Typ}
    (h : PreciseTyping3 G p T) :
    PreciseTyping2 G p T ∨
      ∃ q, PreciseTyping3 G p (.sngl q) ∧ PreciseTyping2 G q T := by
  induction h with
  | precise h => exact Or.inl h
  | snglTrans hp hq ih =>
      rename_i p' q T'
      rcases ih with hlast | ⟨r, hpr, hlast⟩
      · exact Or.inr ⟨q, .precise hp, hlast⟩
      · exact Or.inr ⟨r, .snglTrans hp hpr, hlast⟩

theorem PreciseTyping2.decTyp_eq {G : Ctx} {p : Path}
    {A : Signature.TypLabel} {S T : Typ} (hi : Inert G)
    (h : PreciseTyping2 G p (.rcd (.typ A S T))) : S = T := by
  rcases h.inertSngl hi with hbad | hrecord
  · exact False.elim hbad.rcd_false
  · exact hrecord.singleTyp_eq

theorem PreciseTyping3.decTyp_eq {G : Ctx} {p : Path}
    {A : Signature.TypLabel} {S T : Typ} (hi : Inert G)
    (h : PreciseTyping3 G p (.rcd (.typ A S T))) : S = T := by
  rcases h.inertSngl hi with hbad | hrecord
  · exact False.elim hbad.rcd_false
  · exact hrecord.singleTyp_eq

theorem PreciseTyping2.record_sngl_false {G : Ctx} {p q : Path}
    {R : Typ} {D : Dec} (hi : Inert G)
    (hr : PreciseFlow G p R (.rcd D))
    (hs : PreciseTyping2 G p (.sngl q)) : False := by
  generalize heq : Typ.sngl q = V at hs
  induction hs generalizing q R D with
  | flow hs =>
      cases heq
      have hsource : R = .sngl q := hr.source_unique hi hs |>.trans
        (hs.snglSource_eq hi)
      obtain ⟨T, hR⟩ := hr.recordSource_bnd hi
      rw [hR] at hsource
      cases hsource
  | snglTrans hp hq ihp ihq =>
      cases heq
      obtain ⟨R', hr'⟩ := hr.backtrackRecord
      exact ihp hr' rfl

theorem PreciseTyping2.decTypTarget_unique {G : Ctx} {p : Path}
    {A : Signature.TypLabel} {S₁ S₂ : Typ} (hi : Inert G)
    (h₁ : PreciseTyping2 G p (.rcd (.typ A S₁ S₁)))
    (h₂ : PreciseTyping2 G p (.rcd (.typ A S₂ S₂))) : S₁ = S₂ := by
  cases h₁ with
  | flow h₁ =>
      cases h₂ with
      | flow h₂ => exact h₁.decTypTarget_unique hi h₂

theorem PreciseTyping2.snglField_cases {G : Ctx} {p q : Path}
    {a : Signature.TrmLabel} (h : PreciseTyping2 G (p.selectField a) (.sngl q)) :
    (∃ R, PreciseFlow G (p.selectField a) R (.sngl q)) ∨
      ∃ r, q = r.selectField a ∧ PreciseTyping2 G p (.sngl r) := by
  generalize heq : p.selectField a = s at h
  cases h with
  | flow h => exact Or.inl ⟨_, h⟩
  | snglTrans hp hq =>
      rename_i p' r b U
      obtain ⟨rfl, rfl⟩ := Path.selectField_injective heq
      exact Or.inr ⟨r, rfl, hp⟩

theorem PreciseTyping2.snglTarget_unique {G : Ctx} {p q₁ q₂ : Path}
    (hi : Inert G) (h₁ : PreciseTyping2 G p (.sngl q₁))
    (h₂ : PreciseTyping2 G p (.sngl q₂)) : q₁ = q₂ := by
  generalize heq : Typ.sngl q₁ = V at h₁
  induction h₁ generalizing q₁ q₂ with
  | flow h₁ =>
      cases heq
      cases h₂ with
      | flow h₂ =>
          have hs : _ = _ := h₁.source_unique hi h₂
          rw [h₁.snglSource_eq hi, h₂.snglSource_eq hi] at hs
          exact Typ.sngl.inj hs
      | snglTrans hp hq =>
          obtain ⟨R, hr⟩ := h₁.backtrackRecord
          exact False.elim (hp.record_sngl_false hi hr)
  | snglTrans hp hq ihp ihq =>
      cases heq
      rcases h₂.snglField_cases with ⟨R, h₂⟩ | ⟨r, rfl, hp₂⟩
      · obtain ⟨R, hr⟩ := h₂.backtrackRecord
        exact False.elim (hp.record_sngl_false hi hr)
      · have hbase := ihp hp₂ rfl
        subst r
        rfl

theorem PreciseTyping2.snglTypeExists {G : Ctx} {p q : Path} {T : Typ}
    (hi : Inert G) (hs : PreciseTyping2 G p (.sngl q))
    (hT : PreciseTyping2 G p T) : ∃ r, T = .sngl r := by
  induction hT generalizing q with
  | flow hT =>
      cases hs with
      | flow hs =>
          have hsource := hs.source_unique hi hT
          rw [hs.snglSource_eq hi] at hsource
          rw [← hsource] at hT
          exact ⟨q, hT.envSngl_eq⟩
      | snglTrans hp hq =>
          obtain ⟨R, hr⟩ := hT.backtrackRecord
          exact False.elim (hp.record_sngl_false hi hr)
  | snglTrans hp hq ihp ihq => exact ⟨_, rfl⟩

theorem PreciseTyping2.snglType_eq {G : Ctx} {p q : Path} {T : Typ}
    (hi : Inert G) (hs : PreciseTyping2 G p (.sngl q))
    (hT : PreciseTyping2 G p T) : T = .sngl q := by
  obtain ⟨r, rfl⟩ := hs.snglTypeExists hi hT
  exact congrArg Typ.sngl (hT.snglTarget_unique hi hs)

theorem PreciseTyping2.invertSngl3 {G : Ctx} {p q : Path} {T : Typ}
    (hi : Inert G) (hT : PreciseTyping2 G p T)
    (hs : PreciseTyping3 G p (.sngl q)) :
    ∃ r, Typ.sngl r = T ∧
      (q = r ∨ PreciseTyping3 G r (.sngl q)) := by
  generalize heq : Typ.sngl q = U at hs
  induction hs generalizing q T with
  | precise hs =>
      cases heq
      exact ⟨q, (hs.snglType_eq hi hT).symm, Or.inl rfl⟩
  | snglTrans hpr hr ih =>
      cases heq
      exact ⟨_, (hpr.snglType_eq hi hT).symm, Or.inr hr⟩

theorem PreciseTyping3.invertSngl {G : Ctx} {p q : Path} {T : Typ}
    (hi : Inert G) (hT : PreciseTyping3 G p T)
    (hs : PreciseTyping3 G p (.sngl q)) :
    PreciseTyping3 G q T ∨
      ∃ r, Typ.sngl r = T ∧
        (q = r ∨ PreciseTyping3 G r (.sngl q)) := by
  induction hT with
  | precise hT => exact Or.inr (hT.invertSngl3 hi hs)
  | snglTrans hpr hr ih =>
      obtain ⟨r, heq, hrel⟩ := hpr.invertSngl3 hi hs
      have hrq : r = _ := Typ.sngl.inj heq
      subst r
      rcases hrel with rfl | hrs
      · exact Or.inl hr
      · exact ih hrs

theorem PreciseTyping3.decTypTarget_unique {G : Ctx} {p : Path}
    {A : Signature.TypLabel} {S₁ S₂ : Typ} (hi : Inert G)
    (h₁ : PreciseTyping3 G p (.rcd (.typ A S₁ S₁)))
    (h₂ : PreciseTyping3 G p (.rcd (.typ A S₂ S₂))) : S₁ = S₂ := by
  generalize heq : Typ.rcd (Dec.typ A S₁ S₁) = V at h₁
  induction h₁ generalizing S₁ S₂ with
  | precise h₁ =>
      cases heq
      cases h₂ with
      | precise h₂ => exact h₁.decTypTarget_unique hi h₂
      | snglTrans hs h₂ =>
          cases h₁ with
          | flow hr => exact False.elim (hs.record_sngl_false hi hr)
  | snglTrans hs h₁ ih =>
      cases h₂ with
      | precise h₂ =>
          cases h₂ with
          | flow hr => exact False.elim (hs.record_sngl_false hi hr)
      | snglTrans hs₂ h₂ =>
          have hq := hs.snglTarget_unique hi hs₂
          subst hq
          exact ih h₂ heq

theorem PreciseTyping2.recordType_sngl_false {G : Ctx} {p q : Path}
    {T : Typ} (hi : Inert G) (hrecord : RecordType T)
    (hT : PreciseTyping2 G p T) (hs : PreciseTyping2 G p (.sngl q)) : False := by
  cases hT with
  | flow hT =>
      cases hs with
      | flow hs =>
          obtain ⟨V, hV⟩ := hT.recordTypeSource_bnd hi hrecord
          have hsource := hT.source_unique hi hs
          rw [hV, hs.snglSource_eq hi] at hsource
          cases hsource
      | snglTrans hp hq =>
          obtain ⟨R, hr⟩ := hT.backtrackRecord
          exact hp.record_sngl_false hi hr
  | snglTrans hp hq =>
      obtain ⟨labels, hrecord⟩ := hrecord
      cases hrecord

theorem PreciseTyping3.invertSngl2_record {G : Ctx} {p q : Path}
    {T : Typ} (hi : Inert G) (hrecord : RecordType T)
    (hT : PreciseTyping3 G p T) (hs : PreciseTyping2 G p (.sngl q)) :
    PreciseTyping3 G q T := by
  induction hT with
  | precise hT => exact False.elim (hT.recordType_sngl_false hi hrecord hs)
  | snglTrans hs' hT ih =>
      have hq := hs'.snglTarget_unique hi hs
      subst hq
      exact hT

theorem PreciseTyping3.invertSngl_record {G : Ctx} {p q : Path}
    {T : Typ} (hi : Inert G) (hrecord : RecordType T)
    (hT : PreciseTyping3 G p T) (hs : PreciseTyping3 G p (.sngl q)) :
    PreciseTyping3 G q T := by
  generalize heq : Typ.sngl q = U at hs
  induction hs generalizing q T with
  | precise hs =>
      cases heq
      exact hT.invertSngl2_record hi hrecord hs
  | snglTrans hs hrest ih =>
      have hT' := hT.invertSngl2_record hi hrecord hs
      exact ih hrecord hT' heq

theorem PreciseTyping3.fieldSngl {G : Ctx} {p q : Path}
    {a : Signature.TrmLabel} {T : Typ}
    (hs : PreciseTyping3 G p (.sngl q))
    (hq : PreciseTyping3 G (q.selectField a) T) :
    PreciseTyping3 G (p.selectField a) (.sngl (q.selectField a)) := by
  generalize heq : Typ.sngl q = U at hs
  induction hs generalizing q T a with
  | precise hs =>
      cases heq
      obtain ⟨U, hq₂⟩ := hq.precise2Exists
      exact .precise (.snglTrans hs hq₂)
  | snglTrans hs hrest ih =>
      have htail := ih hq heq
      obtain ⟨U, hbase⟩ := htail.precise2Exists
      exact .snglTrans (.snglTrans hs hbase) htail

theorem PreciseTyping3.fieldElim {G : Ctx} {p : Path}
    {a : Signature.TrmLabel} {T : Typ}
    (h : PreciseTyping3 G p (.rcd (.trm a T))) :
    PreciseTyping3 G (p.selectField a) T := by
  generalize heq : Typ.rcd (Dec.trm a T) = U at h
  induction h generalizing a T with
  | precise h =>
      cases heq
      cases h with
      | flow h => exact .precise (.flow (.fld h))
  | snglTrans hs h ih =>
      have hfield := ih heq
      exact ((PreciseTyping3.precise hs).fieldSngl hfield).snglTrans3 hfield

theorem PreciseTyping2.fieldOtherExists {G : Ctx} {p q : Path}
    {a : Signature.TrmLabel} {T : Typ} (hi : Inert G)
    (hs : PreciseTyping2 G p (.sngl q))
    (hpa : PreciseTyping2 G (p.selectField a) T) :
    ∃ U, PreciseTyping2 G (q.selectField a) U := by
  generalize heq : p.selectField a = r at hpa
  induction hpa generalizing p q a with
  | flow hpa =>
      rw [← heq] at hpa
      obtain ⟨R, hb⟩ := hpa.backtrackRecord
      have hrecord := ((hpa.inertSngl hi).1).trmRecordType a
      have hqrec := (PreciseTyping3.precise (.flow hb)).invertSngl2_record
        hi hrecord hs
      exact hqrec.fieldElim.precise2Exists
  | snglTrans hs' hq ihs ihq =>
      rename_i p' q' b U
      obtain ⟨rfl, rfl⟩ := Path.selectField_injective heq
      have hqeq := hs.snglTarget_unique hi hs'
      subst hqeq
      exact ⟨U, hq⟩

theorem PreciseTyping2.fieldsOtherExists {G : Ctx} {p q : Path}
    {fields : Fields} {T U : Typ} (hi : Inert G)
    (hs : PreciseFlow G p (.sngl q) (.sngl q))
    (hq : PreciseTyping2 G q T)
    (hpfields : PreciseTyping2 G (p.selectFields fields) U) :
    ∃ V, PreciseTyping2 G (q.selectFields fields) V := by
  induction fields generalizing U with
  | nil =>
      simpa only [Path.selectFields_nil] using Exists.intro T hq
  | cons a fields ih =>
      rw [Path.selectFields_cons] at hpfields ⊢
      obtain ⟨W, hpbase⟩ := hpfields.backtrack
      obtain ⟨V, hqbase⟩ := ih hpbase
      have hsfields := (PreciseTyping2.flow hs).fieldTrans hqbase
      exact hsfields.fieldOtherExists hi hpfields

theorem PreciseTyping3.fieldOtherExists {G : Ctx} {p q : Path}
    {a : Signature.TrmLabel} {T : Typ} (hi : Inert G)
    (hs : PreciseTyping3 G p (.sngl q))
    (hpa : PreciseTyping3 G (p.selectField a) T) :
    ∃ U, PreciseTyping3 G (q.selectField a) U := by
  generalize heq : Typ.sngl q = V at hs
  induction hs generalizing q a T with
  | precise hs =>
      cases heq
      obtain ⟨R, hpa₂⟩ := hpa.precise2Exists
      obtain ⟨U, hqa₂⟩ := hs.fieldOtherExists hi hpa₂
      exact ⟨U, .precise hqa₂⟩
  | snglTrans hs hrest ih =>
      obtain ⟨R, hpa₂⟩ := hpa.precise2Exists
      obtain ⟨U, hra₂⟩ := hs.fieldOtherExists hi hpa₂
      exact ih (.precise hra₂) heq

theorem PreciseTyping3.fieldSnglFromLeft {G : Ctx} {p q : Path}
    {a : Signature.TrmLabel} {T : Typ} (hi : Inert G)
    (hs : PreciseTyping3 G p (.sngl q))
    (hpa : PreciseTyping3 G (p.selectField a) T) :
    PreciseTyping3 G (p.selectField a) (.sngl (q.selectField a)) := by
  obtain ⟨U, hqa⟩ := hs.fieldOtherExists hi hpa
  exact hs.fieldSngl hqa

theorem PreciseTyping3.fieldTransSngl {G : Ctx} {p q : Path}
    {fields : Fields} {T : Typ} (hs : PreciseTyping3 G p (.sngl q))
    (hq : PreciseTyping3 G (q.selectFields fields) T) :
    PreciseTyping3 G (p.selectFields fields) (.sngl (q.selectFields fields)) := by
  induction fields generalizing T with
  | nil => simpa only [Path.selectFields_nil] using hs
  | cons a fields ih =>
      rw [Path.selectFields_cons] at hq ⊢
      obtain ⟨U, hbase⟩ := hq.backtrack
      exact (ih hbase).fieldSngl hq

theorem PreciseTyping3.fieldTransSnglFromLeft {G : Ctx} {p q : Path}
    {fields : Fields} {T : Typ} (hi : Inert G)
    (hs : PreciseTyping3 G p (.sngl q))
    (hp : PreciseTyping3 G (p.selectFields fields) T) :
    PreciseTyping3 G (p.selectFields fields) (.sngl (q.selectFields fields)) := by
  induction fields generalizing T with
  | nil => simpa only [Path.selectFields_nil] using hs
  | cons a fields ih =>
      rw [Path.selectFields_cons] at hp ⊢
      obtain ⟨U, hbase⟩ := hp.backtrack
      exact (ih hbase).fieldSnglFromLeft hi hp

inductive Wf : Ctx → Prop where
  | empty : Wf Env.empty
  | push : Wf G → Env.Fresh x G →
      (∀ fields q,
        PreciseFlow (G.push x T) (.select (.free x) fields)
          (.sngl q) (.sngl q) → ∃ U, PreciseTyping2 (G.push x T) q U) →
      Wf (G.push x T)

theorem Wf.prefix {G : Ctx} {x : Var} {T : Typ}
    (h : Wf (G.push x T)) : Wf G := by
  cases h with
  | push h _ _ => exact h

theorem PreciseFlow.singletonTargetStrengthen {G : Ctx} {x y : Var}
    {T : Typ} {fields : Fields} {q : Path}
    (hi : Inert (G.push x T)) (hwf : Wf G)
    (h : PreciseFlow (G.push x T) (.select (.free y) fields)
      (.sngl q) (.sngl q)) (hyx : y ≠ x) :
    ∃ U, PreciseTyping2 G q U := by
  induction hwf generalizing x T y fields q with
  | empty =>
      have h0 := h.strengthenPush hyx
      obtain ⟨S, hb⟩ := h0.receiverBinds
      exact False.elim hb.empty_false
  | @push G z Z hwf hz htargets ih =>
      have hiG : Inert (G.push z Z) := hi.prefix
      have hG := h.strengthenPush hyx
      by_cases hyz : y = z
      · subst y
        exact htargets fields q hG
      · obtain ⟨U, hq⟩ := ih hiG hG hyz
        exact ⟨U, hq.mono (.pushRight hz Z) hiG.ok⟩

theorem PreciseFlow.singletonTargetTyped {G : Ctx} {p q : Path}
    {T : Typ} (hi : Inert G) (hwf : Wf G)
    (h : PreciseFlow G p T (.sngl q)) :
    ∃ U, PreciseTyping2 G q U := by
  have hsource := h.snglSource_eq hi
  subst T
  cases hwf with
  | empty =>
      obtain ⟨x, hx⟩ := h.sourceNamed
      cases p with
      | select av fields =>
          simp only [Path.Named] at hx
          obtain ⟨y, rfl⟩ := hx
          obtain ⟨S, hb⟩ := h.receiverBinds
          exact False.elim hb.empty_false
  | @push G x T hwf hx htargets =>
      cases p with
      | select av fields =>
          have hn := h.sourceNamed
          simp only [Path.Named] at hn
          obtain ⟨y, rfl⟩ := hn
          by_cases hyx : y = x
          · subst y
            exact htargets fields q h
          · obtain ⟨U, hq⟩ := h.singletonTargetStrengthen hi hwf hyx
            exact ⟨U, hq.mono (.pushRight hx T) hi.ok⟩

theorem PreciseTyping2.singletonTargetTyped {G : Ctx} {p q : Path}
    (hi : Inert G) (hwf : Wf G)
    (h : PreciseTyping2 G p (.sngl q)) :
    ∃ U, PreciseTyping2 G q U := by
  cases h with
  | flow h => exact h.singletonTargetTyped hi hwf
  | snglTrans hp hq => exact ⟨_, hq⟩

theorem PreciseTyping3.singletonTargetTyped {G : Ctx} {p q : Path}
    (hi : Inert G) (hwf : Wf G)
    (h : PreciseTyping3 G p (.sngl q)) :
    ∃ U, PreciseTyping3 G q U := by
  generalize heq : Typ.sngl q = T at h
  induction h generalizing q with
  | precise h =>
      cases heq
      obtain ⟨U, hq⟩ := h.singletonTargetTyped hi hwf
      exact ⟨U, .precise hq⟩
  | snglTrans hp hq ih => exact ih heq

theorem PreciseTyping2.receiverBinds {G : Ctx} {x : Var}
    {fields : Fields} {T : Typ}
    (h : PreciseTyping2 G (.select (.free x) fields) T) :
    ∃ S, Env.Binds x S G := by
  generalize heq : Path.select (.free x) fields = p at h
  induction h generalizing x fields with
  | flow h =>
      rw [← heq] at h
      exact h.receiverBinds
  | snglTrans hp hq ihp ihq =>
      rename_i p q a U
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
              exact ihp rfl

theorem PreciseTyping2.strengthenPush {G : Ctx} {x y : Var}
    {T U : Typ} {fields : Fields}
    (hi : Inert (G.push x T)) (hwf : Wf G)
    (h : PreciseTyping2 (G.push x T)
      (.select (.free y) fields) U) (hyx : y ≠ x) :
    PreciseTyping2 G (.select (.free y) fields) U := by
  generalize heq : Path.select (.free y) fields = p at h
  induction h generalizing y fields with
  | flow h =>
      cases heq
      exact .flow (h.strengthenPush hyx)
  | snglTrans hp hq ihp ihq =>
      rename_i p q a V
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
              have hpG := ihp hyx rfl
              obtain ⟨W, hqG⟩ := hpG.singletonTargetTyped hi.prefix hwf
              have hn := hq.toGeneral.pathNamed
              cases q with
              | select qav qfields =>
                  simp only [Path.Named] at hn
                  obtain ⟨z, rfl⟩ := hn
                  obtain ⟨S, hb⟩ := hqG.receiverBinds
                  have hx : Env.Fresh x G := by
                    cases hi with
                    | push _ _ hx => exact hx
                  have hzx : z ≠ x := hb.ne_of_fresh hx
                  exact .snglTrans hpG (ihq hzx rfl)

theorem PreciseTyping3.strengthenPush {G : Ctx} {x y : Var}
    {T U : Typ} {fields : Fields}
    (hi : Inert (G.push x T)) (hwf : Wf G)
    (h : PreciseTyping3 (G.push x T)
      (.select (.free y) fields) U) (hyx : y ≠ x) :
    PreciseTyping3 G (.select (.free y) fields) U := by
  generalize heq : Path.select (.free y) fields = p at h
  induction h generalizing y fields with
  | precise h =>
      cases heq
      exact .precise (h.strengthenPush hi hwf hyx)
  | snglTrans hp hq ih =>
      rename_i p q V
      cases heq
      have hpG := hp.strengthenPush hi hwf hyx
      obtain ⟨W, hqG⟩ := hpG.singletonTargetTyped hi.prefix hwf
      have hn := hq.toGeneral.pathNamed
      cases q with
      | select qav qfields =>
          simp only [Path.Named] at hn
          obtain ⟨z, rfl⟩ := hn
          obtain ⟨S, hb⟩ := hqG.receiverBinds
          have hx : Env.Fresh x G := by
            cases hi with
            | push _ _ hx => exact hx
          have hzx : z ≠ x := hb.ne_of_fresh hx
          exact .snglTrans hpG (ih hzx rfl)

/-! ## Typed replacement composition -/

def TypedReplStep (G : Ctx) (T U : Typ) : Prop :=
  ∃ p q V, PreciseFlow G p (.sngl q) (.sngl q) ∧
    PreciseTyping2 G q V ∧ ReplTyp q p T U

def ReplComposition (G : Ctx) : Typ → Typ → Prop := Star (TypedReplStep G)

inductive TypedPathReplStep (G : Ctx) : Path → Path → Prop where
  | step : PreciseFlow G p (.sngl q) (.sngl q) → PreciseTyping2 G q U →
      TypedPathReplStep G (q.selectFields fields) (p.selectFields fields)

def PathReplComposition (G : Ctx) : Path → Path → Prop :=
  Star (TypedPathReplStep G)

theorem ReplComposition.bndInner {G : Ctx} {T U : Typ}
    (h : ReplComposition G (.bnd T) (.bnd U)) :
    ReplComposition G T U := by
  generalize hleft : Typ.bnd T = S at h
  generalize hright : Typ.bnd U = V at h
  induction h generalizing T U with
  | refl =>
      have heq := Typ.bnd.inj (hleft.trans hright.symm)
      subst U
      exact .refl T
  | step hstep hrest ih =>
      rw [← hleft] at hstep
      obtain ⟨p, q, W, hp, hq, hr⟩ := hstep
      cases hr with
      | bnd hr =>
          have htail := ih rfl hright
          exact (Star.one ⟨p, q, W, hp, hq, hr⟩).trans htail

theorem ReplComposition.bndMap {G : Ctx} {T U : Typ}
    (h : ReplComposition G T U) :
    ReplComposition G (.bnd T) (.bnd U) := by
  induction h with
  | refl => exact .refl _
  | step hstep hrest ih =>
      obtain ⟨p, q, W, hp, hq, hr⟩ := hstep
      exact (Star.one ⟨p, q, W, hp, hq, .bnd hr⟩).trans ih

theorem ReplComposition.sourceBnd {G : Ctx} {T U : Typ}
    (h : ReplComposition G (.bnd T) U) :
    ∃ U', U = .bnd U' ∧ ReplComposition G T U' := by
  generalize hsource : Typ.bnd T = S at h
  induction h generalizing T with
  | refl =>
      exact ⟨T, hsource.symm, .refl T⟩
  | step hstep hrest ih =>
      rw [← hsource] at hstep
      obtain ⟨p, q, W, hp, hq, hr⟩ := hstep
      cases hr with
      | bnd hr =>
          obtain ⟨U', heq, htail⟩ := ih rfl
          exact ⟨U', heq,
            (Star.one ⟨p, q, W, hp, hq, hr⟩).trans htail⟩

theorem ReplComposition.targetBnd {G : Ctx} {T U : Typ}
    (h : ReplComposition G T (.bnd U)) :
    ∃ T', T = .bnd T' ∧ ReplComposition G T' U := by
  generalize htarget : Typ.bnd U = V at h
  induction h generalizing U with
  | refl => exact ⟨U, htarget.symm, .refl U⟩
  | step hstep hrest ih =>
      obtain ⟨V', heq, htail⟩ := ih htarget
      subst_vars
      obtain ⟨p, q, W, hp, hq, hr⟩ := hstep
      cases hr with
      | bnd hr =>
          exact ⟨_, rfl,
            (Star.one ⟨p, q, W, hp, hq, hr⟩).trans htail⟩

theorem ReplComposition.sourceSngl {G : Ctx} {p : Path} {U : Typ}
    (h : ReplComposition G (.sngl p) U) : ∃ q, U = .sngl q := by
  generalize hsource : Typ.sngl p = S at h
  induction h generalizing p with
  | refl => exact ⟨p, hsource.symm⟩
  | step hstep hrest ih =>
      rw [← hsource] at hstep
      obtain ⟨r, q, W, hr, hq, hrepl⟩ := hstep
      cases hrepl with
      | sngl => exact ih rfl

theorem ReplComposition.targetSngl {G : Ctx} {T : Typ} {q : Path}
    (h : ReplComposition G T (.sngl q)) : ∃ p, T = .sngl p := by
  generalize htarget : Typ.sngl q = U at h
  induction h generalizing q with
  | refl => exact ⟨q, htarget.symm⟩
  | step hstep hrest ih =>
      obtain ⟨r, heq⟩ := ih htarget
      subst_vars
      obtain ⟨p, q, W, hp, hq, hrepl⟩ := hstep
      cases hrepl with
      | sngl => exact ⟨_, rfl⟩

theorem ReplComposition.sourceAll {G : Ctx} {S T U : Typ}
    (h : ReplComposition G (.all S T) U) :
    ∃ S' T', U = .all S' T' := by
  generalize hsource : Typ.all S T = V at h
  induction h generalizing S T with
  | refl => exact ⟨S, T, hsource.symm⟩
  | step hstep hrest ih =>
      rw [← hsource] at hstep
      obtain ⟨p, q, W, hp, hq, hrepl⟩ := hstep
      cases hrepl with
      | allDom => exact ih rfl
      | allCod => exact ih rfl

theorem ReplComposition.targetAll {G : Ctx} {U S T : Typ}
    (h : ReplComposition G U (.all S T)) :
    ∃ S' T', U = .all S' T' := by
  generalize htarget : Typ.all S T = V at h
  induction h generalizing S T with
  | refl => exact ⟨S, T, htarget.symm⟩
  | step hstep hrest ih =>
      obtain ⟨S', T', heq⟩ := ih htarget
      subst_vars
      obtain ⟨p, q, W, hp, hq, hrepl⟩ := hstep
      cases hrepl with
      | allDom => exact ⟨_, _, rfl⟩
      | allCod => exact ⟨_, _, rfl⟩

end CDot
