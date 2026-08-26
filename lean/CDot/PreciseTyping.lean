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

end CDot
