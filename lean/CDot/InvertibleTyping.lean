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

theorem InvertiblePath.allToPrecise {G : Ctx} {p : Path} {S T : Typ}
    (h : InvertiblePath G p (.all S T)) :
    ∃ S' T', ∃ L : Vars, PreciseTyping3 G p (.all S' T') ∧
      TightSubtyp G S S' ∧
      (∀ y, y ∉ L → TightSubtyp (G.push y S) (T'.open y) (T.open y)) := by
  cases h with
  | precise h => exact ⟨S, T, ∅, h, .refl, fun _ _ => .refl⟩

theorem InvertiblePath.rcdToPrecise {G : Ctx} {p : Path}
    {A : Signature.TypLabel} {S U : Typ} (hi : Inert G)
    (h : InvertiblePath G p (.rcd (.typ A S U))) :
    ∃ T, PreciseTyping3 G p (.rcd (.typ A T T)) ∧
      TightSubtyp G T U ∧ TightSubtyp G S T := by
  cases h with
  | precise h =>
      have heq := h.decTyp_eq hi
      subst U
      exact ⟨S, h, .refl, .refl⟩

theorem InvertibleVal.allToPrecise {G : Ctx} {v : Val} {S T : Typ}
    (h : InvertibleVal G v (.all S T)) :
    ∃ S' T', PreciseVal G v (.all S' T') ∧
      Subtyp G S S' ∧
      (∀ y, Subtyp (G.push y S) (T'.open y) (T.open y)) := by
  cases h with
  | precise h => exact ⟨S, T, h, .refl, fun _ => .refl⟩

end CDot
