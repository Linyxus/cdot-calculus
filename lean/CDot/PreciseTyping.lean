import CDot.PreciseFlow

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

end CDot
