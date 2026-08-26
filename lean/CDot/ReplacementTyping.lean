import CDot.InvertibleTyping
import CDot.Narrowing

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
  | sel : ReplacementVal G v T →
      PreciseFlow G q S (.rcd (.typ A T T)) → ReplacementVal G v (.path q A)
  | recQP : PreciseFlow G p (.sngl q) (.sngl q) →
      PreciseTyping2 G q U → ReplacementVal G v (.bnd T) →
      ReplTyp q p T T' → ReplacementVal G v (.bnd T')
  | selQP : PreciseFlow G p (.sngl q) (.sngl q) →
      PreciseTyping2 G q U → ReplacementVal G v (.path r' A) →
      ReplTyp q p (.path r' A) (.path r'' A) →
      ReplacementVal G v (.path r'' A)
  | top : ReplacementVal G v T → ReplacementVal G v .top
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

theorem ReplacementPath.rcdToPrecise {G : Ctx} {p : Path}
    {A : Signature.TypLabel} {S U : Typ} (hi : Inert G)
    (h : ReplacementPath G p (.rcd (.typ A S U))) :
    ∃ T, PreciseTyping3 G p (.rcd (.typ A T T)) ∧
      TightSubtyp G T U ∧ TightSubtyp G S T := by
  generalize heq : Typ.rcd (Dec.typ A S U) = V at h
  induction h generalizing A S U with
  | invertible h =>
      cases heq
      exact h.rcdToPrecise hi
  | and hT hU ihT ihU => cases heq
  | bnd h ih => cases heq
  | sel h hf ih => cases heq
  | rcdIntro h ih => cases heq
  | recQP hp hq h hr ih => cases heq
  | selQP hp hq h ih => cases heq
  | snglQP hp hq h ih => cases heq
  | top h ih => cases heq
  | trm h hs ih => cases heq
  | typ h hLo hHi ih =>
      cases heq
      obtain ⟨V, hp, hVS₁, hT₁V⟩ := ih rfl
      exact ⟨V, hp, .trans hVS₁ hHi, .trans hLo hT₁V⟩
  | all L h hdom hbody ih => cases heq

theorem ReplacementPath.allToPrecise {G : Ctx} {p : Path} {S T : Typ}
    (hi : Inert G) (h : ReplacementPath G p (.all S T)) :
    ∃ S' T', ∃ L : Vars, PreciseTyping3 G p (.all S' T') ∧
      TightSubtyp G S S' ∧
      (∀ y, y ∉ L → Subtyp (G.push y S) (T'.open y) (T.open y)) := by
  generalize heq : Typ.all S T = V at h
  induction h generalizing S T with
  | invertible h =>
      cases heq
      obtain ⟨S', T', L, hp, hdom, hbody⟩ := h.allToPrecise
      exact ⟨S', T', L, hp, hdom, fun y hy => (hbody y hy).toGeneral⟩
  | and hT hU ihT ihU => cases heq
  | bnd h ih => cases heq
  | sel h hf ih => cases heq
  | rcdIntro h ih => cases heq
  | recQP hp hq h hr ih => cases heq
  | selQP hp hq h ih => cases heq
  | snglQP hp hq h ih => cases heq
  | top h ih => cases heq
  | trm h hs ih => cases heq
  | typ h hLo hHi ih => cases heq
  | all L h hdom hbody ih =>
      rename_i p' S₁ T₁ S₂ T₂
      cases heq
      obtain ⟨S', T', L', hp, hS₁S', hT'T₁⟩ := ih rfl
      let L'' := (L ∪ L') ∪ G.dom
      refine ⟨S', T', L'', hp, .trans hdom hS₁S', ?_⟩
      intro y hy
      simp only [L'', Finset.mem_union, not_or] at hy
      have hok₂ : Env.Ok (G.push y S₂) := Env.okPush hi.ok hy.2
      have hok₁ : Env.Ok (G.push y S₁) := Env.okPush hi.ok hy.2
      have hnarrow := (hT'T₁ y hy.1.2).narrow
        (Subenv.last hdom.toGeneral hok₂ hok₁)
      exact .trans hnarrow (hbody y hy.1.1)

theorem ReplacementVal.andParts {G : Ctx} {v : Val} {T U : Typ}
    (h : ReplacementVal G v (.and T U)) :
    ReplacementVal G v T ∧ ReplacementVal G v U := by
  cases h with
  | invertible h => exact False.elim h.and_false
  | and hT hU => exact ⟨hT, hU⟩

theorem ReplacementVal.allToPrecise {G : Ctx} {v : Val} {S T : Typ}
    (hi : Inert G) (h : ReplacementVal G v (.all S T)) :
    ∃ L : Vars, ∃ S' T', PreciseVal G v (.all S' T') ∧
      Subtyp G S S' ∧
      (∀ y, y ∉ L → Subtyp (G.push y S) (T'.open y) (T.open y)) := by
  generalize heq : Typ.all S T = V at h
  induction h generalizing S T with
  | invertible h =>
      cases heq
      obtain ⟨S', T', hp, hdom, hbody⟩ := h.allToPrecise
      exact ⟨∅, S', T', hp, hdom, fun y _ => hbody y⟩
  | and hT hU ihT ihU => cases heq
  | sel h hf ih => cases heq
  | recQP hp hq h hr ih => cases heq
  | selQP hp hq h hr ih => cases heq
  | top h ih => cases heq
  | all L h hdom hbody ih =>
      rename_i S₁ T₁ S₂ T₂
      cases heq
      obtain ⟨L', S', T', hp, hS₁S', hT'T₁⟩ := ih rfl
      let L'' := (L ∪ L') ∪ G.dom
      refine ⟨L'', S', T', hp, .trans hdom.toGeneral hS₁S', ?_⟩
      intro y hy
      simp only [L'', Finset.mem_union, not_or] at hy
      have hok₂ : Env.Ok (G.push y S₂) := Env.okPush hi.ok hy.2
      have hok₁ : Env.Ok (G.push y S₁) := Env.okPush hi.ok hy.2
      have hnarrow := (hT'T₁ y hy.1.2).narrow
        (Subenv.last hdom.toGeneral hok₂ hok₁)
      exact .trans hnarrow (hbody y hy.1.1)

theorem ReplacementVal.lambdaExists {G : Ctx} {v : Val} {S T : Typ}
    (hi : Inert G) (h : ReplacementVal G v (.all S T)) :
    ∃ L : Vars, ∃ S' t, v = .lambda S' t ∧ Subtyp G S S' ∧
      (∀ y, y ∉ L → Typed (G.push y S) (t.open y) (T.open y)) := by
  obtain ⟨L, S', T', hp, hdom, hbody⟩ := h.allToPrecise hi
  cases hp with
  | allIntro L' htyped =>
      let L'' := (L ∪ L') ∪ G.dom
      refine ⟨L'', S', _, rfl, hdom, ?_⟩
      intro y hy
      simp only [L'', Finset.mem_union, not_or] at hy
      have hokS : Env.Ok (G.push y S) := Env.okPush hi.ok hy.2
      have hokS' : Env.Ok (G.push y S') := Env.okPush hi.ok hy.2
      have hnarrow := (htyped y hy.1.2).narrow
        (Subenv.last hdom hokS hokS')
      exact .sub hnarrow (hbody y hy.1.1)

theorem ReplacementVal.bndToInvertible {G : Ctx} {v : Val} {T : Typ}
    (h : ReplacementVal G v (.bnd T)) :
    ∃ U, InvertibleVal G v (.bnd U) ∧ ReplComposition G U T := by
  generalize heq : Typ.bnd T = V at h
  induction h generalizing T with
  | invertible h =>
      cases heq
      exact ⟨T, h, .refl T⟩
  | and hT hU ihT ihU => cases heq
  | sel h hf ih => cases heq
  | recQP hp hq h hr ih =>
      rename_i p q W v T₁ T₂
      cases heq
      obtain ⟨T', hinv, hcomp⟩ := ih rfl
      exact ⟨T', hinv, hcomp.trans (.one ⟨p, q, W, hp, hq, hr⟩)⟩
  | selQP hp hq h hr ih => cases heq
  | top h ih => cases heq
  | all L h hdom hbody ih => cases heq

theorem ReplacementVal.newPreciseExists {G : Ctx} {r : Path}
    {A : Signature.TypLabel} {T : Typ} {ds : Defs} {U : Typ}
    (h : ReplacementVal G (.new r A T ds) U) :
    ∃ T', PreciseVal G (.new r A T ds) (.bnd T') := by
  generalize heq : Val.new r A T ds = v at h
  induction h generalizing r A T ds with
  | invertible h =>
      rw [← heq] at h
      obtain ⟨T', _, hp, _⟩ := h.newToPrecise
      rw [← heq]
      exact ⟨T, hp⟩
  | and hT hU ihT ihU => exact ihT heq
  | sel h hf ih => exact ih heq
  | recQP hp hq h hr ih => exact ih heq
  | selQP hp hq h hr ih => exact ih heq
  | top h ih => exact ih heq
  | all L h hdom hbody ih => exact ih heq

end CDot
