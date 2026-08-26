import CDot.ReplacementTyping
import CDot.GADTRules

/-!
# General typing to tight typing

In an inert context, general typing and subtyping derivations can be converted
to their tight counterparts.  This ports `cdot/GeneralToTight.v`.
-/

namespace CDot

variable [Signature]

theorem ReplTyp.aliasSubtypes {G : Ctx} {p q : Path} {T U V : Typ}
    (hpq : PreciseTyping3 G p (.sngl q)) (hq : PreciseTyping3 G q V)
    (hr : ReplTyp p q T U) :
    TightSubtyp G T U ∧ TightSubtyp G U T :=
  ⟨.snglPQ hpq hq hr, .snglQP hpq hq hr.swap⟩

theorem TightTyped.selectSubtypes {G : Ctx} {p : Path}
    {A : Signature.TypLabel} {S U : Typ} (hi : Inert G)
    (h : TightTyped G (.path p) (.rcd (.typ A S U))) :
    TightSubtyp G (.path p A) U ∧ TightSubtyp G S (.path p A) := by
  obtain ⟨T, hp, hTU, hST⟩ := (h.pathReplacement hi).rcdToPrecise hi
  exact ⟨.trans (.selHi hp) hTU, .trans hST (.selLo hp)⟩

theorem TightTyped.precise2Exists {G : Ctx} {p : Path} {T : Typ}
    (hi : Inert G) (h : TightTyped G (.path p) T) :
    ∃ U, PreciseTyping2 G p U := by
  obtain ⟨U, hp⟩ := (h.pathReplacement hi).preciseExists
  exact hp.precise2Exists

theorem TightTyped.snglSubtypes {G : Ctx} {p q : Path}
    {T U S : Typ} (hi : Inert G)
    (hp : TightTyped G (.path p) (.sngl q))
    (hq : TightTyped G (.path q) S) (hr : ReplTyp p q T U) :
    TightSubtyp G T U ∧ TightSubtyp G U T := by
  obtain ⟨V, hq₂⟩ := hq.precise2Exists hi
  let hq₃ : PreciseTyping3 G q V := .precise hq₂
  have hp' := hp.pathReplacement hi
  obtain ⟨r, W, hpr, hr₃, hqr⟩ := hp'.snglToInvertible hi hq₃
  rcases hpr.snglPreciseCases hi hr₃ with
    ⟨r', hpr', hr'r⟩ | rfl
  · have hprr : PreciseTyping3 G p (.sngl r) := by
      rcases hr'r with rfl | hr'r
      · exact hpr'
      · exact hpr'.snglTrans3 hr'r
    rcases hqr with rfl | hqr
    · exact hr.aliasSubtypes hprr hr₃
    · obtain ⟨X, hprX, hXq⟩ := hr.insert r
      have hpPair := hprX.aliasSubtypes hprr hr₃
      have hqPair := hXq.swap.aliasSubtypes hqr hr₃
      exact ⟨.trans hpPair.1 hqPair.2, .trans hqPair.1 hpPair.2⟩
  · rcases hqr with rfl | hqr
    · have heq := hr.eq_of_paths_eq rfl
      cases heq
      exact ⟨.refl, .refl⟩
    · have hpair := hr.swap.aliasSubtypes hqr hr₃
      exact ⟨hpair.2, hpair.1⟩

end CDot
