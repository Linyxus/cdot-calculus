import CDot.TightTyping

/-!
# Invertible typing

The introduction-`pq` typing relations for paths and values, ported from
`cdot/InvertibleTyping.v`.
-/

namespace CDot

variable [Signature]

inductive InvertiblePath : Ctx → Path → Typ → Prop where
  | precise : PreciseTyping3 G p T → InvertiblePath G p T
  | recPQ : PreciseFlow G p (.sngl q) (.sngl q) →
      PreciseTyping2 G q U → InvertiblePath G r (.bnd T) →
      ReplTyp p q T T' → InvertiblePath G r (.bnd T')
  | selPQ : PreciseFlow G p (.sngl q) (.sngl q) →
      PreciseTyping2 G q U → InvertiblePath G r (.path (p.selectFields fields) A) →
      InvertiblePath G r (.path (q.selectFields fields) A)
  | snglPQ : PreciseFlow G p (.sngl q) (.sngl q) →
      PreciseTyping2 G q U → InvertiblePath G r (.sngl (p.selectFields fields)) →
      InvertiblePath G r (.sngl (q.selectFields fields))
  | self : PreciseTyping2 G p T → InvertiblePath G p (.sngl p)

inductive InvertibleVal : Ctx → Val → Typ → Prop where
  | precise : PreciseVal G v T → InvertibleVal G v T
  | recPQ : PreciseFlow G p (.sngl q) (.sngl q) →
      PreciseTyping2 G q U → InvertibleVal G v (.bnd T) →
      ReplTyp p q T T' → InvertibleVal G v (.bnd T')

theorem InvertiblePath.preciseExists {G : Ctx} {p : Path} {T : Typ}
    (h : InvertiblePath G p T) : ∃ U, PreciseTyping3 G p U := by
  induction h with
  | precise h => exact ⟨_, h⟩
  | recPQ _ _ _ _ ih => exact ih
  | selPQ _ _ _ ih => exact ih
  | snglPQ _ _ _ ih => exact ih
  | self h => exact ⟨_, .precise h⟩

theorem InvertiblePath.andParts {G : Ctx} {p : Path} {T U : Typ}
    (h : InvertiblePath G p (.and T U)) :
    InvertiblePath G p T ∧ InvertiblePath G p U := by
  cases h with
  | precise h => exact ⟨.precise h.andLeft, .precise h.andRight⟩

end CDot
