import CDot.InvertibleTyping

/-!
# Replacement typing

The introduction-`qp` closure used by the canonical-forms argument, ported
from `cdot/ReplacementTyping.v`.
-/

namespace CDot

variable [Signature]

inductive ReplacementPath : Ctx → Path → Typ → Prop where
  | invertible : InvertiblePath G p T → ReplacementPath G p T
  | and : ReplacementPath G p T → ReplacementPath G p U →
      ReplacementPath G p (.and T U)
  | bnd : ReplacementPath G p (T.openPath p) → ReplacementPath G p (.bnd T)
  | sel : ReplacementPath G p T →
      PreciseFlow G q S (.rcd (.typ A T T)) → ReplacementPath G p (.path q A)
  | rcdIntro : ReplacementPath G (p.selectField a) T →
      ReplacementPath G p (.rcd (.trm a T))
  | recQP : PreciseFlow G p (.sngl q) (.sngl q) →
      PreciseTyping2 G q U → ReplacementPath G r (.bnd T) →
      ReplTyp q p T T' → ReplacementPath G r (.bnd T')
  | selQP : PreciseFlow G p (.sngl q) (.sngl q) →
      PreciseTyping2 G q U → ReplacementPath G r (.path (q.selectFields fields) A) →
      ReplacementPath G r (.path (p.selectFields fields) A)
  | snglQP : PreciseFlow G p (.sngl q) (.sngl q) →
      PreciseTyping2 G q U → ReplacementPath G r (.sngl (q.selectFields fields)) →
      ReplacementPath G r (.sngl (p.selectFields fields))
  | top : ReplacementPath G p T → ReplacementPath G p .top
  | trm : ReplacementPath G p (.rcd (.trm a T)) → TightSubtyp G T U →
      ReplacementPath G p (.rcd (.trm a U))
  | typ : ReplacementPath G p (.rcd (.typ A T₁ S₁)) →
      TightSubtyp G T₂ T₁ → TightSubtyp G S₁ S₂ →
      ReplacementPath G p (.rcd (.typ A T₂ S₂))
  | all (L : Vars) : ReplacementPath G p (.all S₁ T₁) →
      TightSubtyp G S₂ S₁ →
      (∀ y, y ∉ L → Subtyp (G.push y S₂) (T₁.open y) (T₂.open y)) →
      ReplacementPath G p (.all S₂ T₂)

inductive ReplacementVal : Ctx → Val → Typ → Prop where
  | invertible : InvertibleVal G v T → ReplacementVal G v T
  | and : ReplacementVal G v T → ReplacementVal G v U →
      ReplacementVal G v (.and T U)
  | bnd : ReplacementVal G v (T.openPath p) → ReplacementVal G v (.bnd T)
  | sel : ReplacementVal G v T →
      PreciseFlow G q S (.rcd (.typ A T T)) → ReplacementVal G v (.path q A)
  | recQP : PreciseFlow G p (.sngl q) (.sngl q) →
      PreciseTyping2 G q U → ReplacementVal G v (.bnd T) →
      ReplTyp q p T T' → ReplacementVal G v (.bnd T')
  | top : ReplacementVal G v T → ReplacementVal G v .top
  | trm : ReplacementVal G v (.rcd (.trm a T)) → TightSubtyp G T U →
      ReplacementVal G v (.rcd (.trm a U))
  | typ : ReplacementVal G v (.rcd (.typ A T₁ S₁)) →
      TightSubtyp G T₂ T₁ → TightSubtyp G S₁ S₂ →
      ReplacementVal G v (.rcd (.typ A T₂ S₂))
  | all (L : Vars) : ReplacementVal G v (.all S₁ T₁) →
      TightSubtyp G S₂ S₁ →
      (∀ y, y ∉ L → Subtyp (G.push y S₂) (T₁.open y) (T₂.open y)) →
      ReplacementVal G v (.all S₂ T₂)

theorem ReplacementPath.andParts {G : Ctx} {p : Path} {T U : Typ}
    (h : ReplacementPath G p (.and T U)) :
    ReplacementPath G p T ∧ ReplacementPath G p U := by
  cases h with
  | invertible h =>
      exact ⟨.invertible h.andParts.1, .invertible h.andParts.2⟩
  | and hT hU => exact ⟨hT, hU⟩

end CDot
