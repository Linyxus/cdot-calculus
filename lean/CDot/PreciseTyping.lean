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
