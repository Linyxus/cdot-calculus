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

end CDot
