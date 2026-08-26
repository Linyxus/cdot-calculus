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

theorem ReplTyp.subtypPQ {G : Ctx} {p q : Path} {T U V : Typ}
    (hr : ReplTyp p q T U) (hp : PreciseTyping3 G p (.sngl q))
    (hq : PreciseTyping3 G q V) : TightSubtyp G T U :=
  .snglPQ hp hq hr

theorem ReplTyp.subtypQP {G : Ctx} {p q : Path} {T U V : Typ}
    (hr : ReplTyp p q T U) (hp : PreciseTyping3 G p (.sngl q))
    (hq : PreciseTyping3 G q V) : TightSubtyp G U T :=
  .snglQP hp hq hr.swap

theorem ReplComposition.subtypes {G : Ctx} {T U : Typ}
    (h : ReplComposition G T U) :
    TightSubtyp G T U ∧ TightSubtyp G U T := by
  induction h with
  | refl => exact ⟨.refl, .refl⟩
  | @step T V U hTV _ ih =>
      obtain ⟨p, q, W, hp, hq, hr⟩ := hTV
      have hp' : PreciseTyping3 G p (.sngl q) := .precise (.flow hp)
      have hq' : PreciseTyping3 G q W := .precise hq
      have hTV₁ : TightSubtyp G T V := .snglQP hp' hq' hr
      have hVT₁ : TightSubtyp G V T := .snglPQ hp' hq' hr.swap
      exact ⟨.trans hTV₁ ih.1, .trans ih.2 hVT₁⟩

theorem InvertiblePath.preciseExists {G : Ctx} {p : Path} {T : Typ}
    (h : InvertiblePath G p T) : ∃ U, PreciseTyping3 G p U := by
  induction h with
  | precise h => exact ⟨_, h⟩
  | recPQ _ _ _ _ ih => exact ih
  | selPQ _ _ _ ih => exact ih
  | snglPQ _ _ _ ih => exact ih
  | self h => exact ⟨_, .precise h⟩

theorem InvertiblePath.bot_false {G : Ctx} {p : Path}
    (hi : Inert G) (h : InvertiblePath G p .bot) : False := by
  cases h with
  | precise h => exact h.bot_false hi

theorem InvertiblePath.backtrack {G : Ctx} {p : Path}
    {a : Signature.TrmLabel} {T : Typ}
    (h : InvertiblePath G (p.selectField a) T) :
    ∃ U, InvertiblePath G p U := by
  generalize heq : p.selectField a = q at h
  induction h generalizing p a with
  | precise h =>
      cases heq
      obtain ⟨U, hp⟩ := h.backtrack
      exact ⟨U, .precise hp⟩
  | recPQ _ _ _ _ ih => exact ih heq
  | selPQ _ _ _ ih => exact ih heq
  | snglPQ _ _ _ ih => exact ih heq
  | self h =>
      cases heq
      obtain ⟨U, hp⟩ := h.backtrack
      exact ⟨U, .precise (.precise hp)⟩

theorem InvertiblePath.andParts {G : Ctx} {p : Path} {T U : Typ}
    (h : InvertiblePath G p (.and T U)) :
    InvertiblePath G p T ∧ InvertiblePath G p U := by
  cases h with
  | precise h => exact ⟨.precise h.andLeft, .precise h.andRight⟩

theorem InvertiblePath.pathSel {G : Ctx} {p q : Path}
    {A : Signature.TypLabel} {T : Typ} (hi : Inert G)
    (hp : PreciseTyping3 G p (.rcd (.typ A T T)))
    (h : InvertiblePath G q (.path p A)) : InvertiblePath G q T := by
  generalize heq : Typ.path p A = V at h
  induction h generalizing p A T with
  | precise h =>
      cases heq
      exact False.elim (h.path_false hi)
  | recPQ hpq hq h hr ih => cases heq
  | selPQ hpq hq h ih =>
      cases heq
      have hs : PreciseTyping3 G _ (.sngl _) :=
        (PreciseTyping3.precise (.flow hpq)).fieldTransSngl hp
      have hp' := hs.snglTrans3 hp
      exact ih hp' rfl
  | snglPQ hpq hq h ih => cases heq
  | self h => cases heq

theorem InvertiblePath.pathSelExists {G : Ctx} {p q : Path}
    {A : Signature.TypLabel} (hi : Inert G)
    (h : InvertiblePath G q (.path p A)) :
    ∃ T, PreciseTyping3 G p (.rcd (.typ A T T)) ∧
      InvertiblePath G q T := by
  generalize heq : Typ.path p A = V at h
  induction h generalizing p A with
  | precise h =>
      cases heq
      exact False.elim (h.path_false hi)
  | recPQ hpq hq h hr ih => cases heq
  | selPQ hpq hq h ih =>
      cases heq
      obtain ⟨T, hp, hT⟩ := ih rfl
      have hs := (PreciseTyping3.precise (.flow hpq)).fieldTransSnglFromLeft hi hp
      have hp' := hp.invertSngl_record hi
        (by exact ⟨_, .one .typ rfl⟩) hs
      exact ⟨T, hp', hT⟩
  | snglPQ hpq hq h ih => cases heq
  | self h => cases heq

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

theorem InvertibleVal.and_false {G : Ctx} {v : Val} {T U : Typ}
    (h : InvertibleVal G v (.and T U)) : False := by
  cases h with
  | precise h => cases h

theorem InvertibleVal.newToPrecise {G : Ctx} {r : Path}
    {A : Signature.TypLabel} {T : Typ} {ds : Defs} {U : Typ}
    (h : InvertibleVal G (.new r A T ds) U) :
    ∃ T', U = .bnd T' ∧ PreciseVal G (.new r A T ds) (.bnd T) ∧
      ReplComposition G T' T := by
  generalize heq : Val.new r A T ds = v at h
  induction h generalizing r A T ds with
  | precise h =>
      cases h with
      | allIntro L hbody => cases heq
      | newIntro L hdefs hself =>
          cases heq
          exact ⟨T, rfl, .newIntro L hdefs hself, .refl T⟩
  | recPQ hp hq h hr ih =>
      rename_i p q W v T₁ T₂
      obtain ⟨T', heqT, hv, hcomp⟩ := ih heq
      have hT : T₁ = T' := Typ.bnd.inj heqT
      subst T'
      exact ⟨T₂, rfl, hv,
        (Star.one ⟨p, q, W, hp, hq, hr.swap⟩).trans hcomp⟩

end CDot
