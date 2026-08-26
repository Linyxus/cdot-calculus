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

mutual
  theorem RecordDec.replacementQP {D D' : Dec} (hD : RecordDec D)
      {G : Ctx} {subject aliasPath target : Path} {V : Typ}
      (hsubject : PreciseTyping3 G subject (.rcd D))
      (halias : PreciseFlow G aliasPath (.sngl target) (.sngl target))
      (htarget : PreciseTyping2 G target V) (hr : ReplDec target aliasPath D D') :
      ReplacementPath G subject (.rcd D') := by
    have ha3 : PreciseTyping3 G aliasPath (.sngl target) := .precise (.flow halias)
    have ht3 : PreciseTyping3 G target V := .precise htarget
    cases hD with
    | typ =>
        cases hr with
        | typLo hr =>
            exact .typ (.invertible (.precise hsubject))
              (.snglPQ ha3 ht3 hr.swap) .refl
        | typHi hr =>
            exact .typ (.invertible (.precise hsubject)) .refl
              (.snglQP ha3 ht3 hr)
    | trm hT =>
        cases hr with
        | trm hr =>
            exact .trm (.invertible (.precise hsubject))
              (.snglQP ha3 ht3 hr)
    | trmSngl =>
        cases hr with
        | trm hr =>
            exact .trm (.invertible (.precise hsubject))
              (.snglQP ha3 ht3 hr)

  theorem RecordTyp.replacementQP {T T' : Typ} {labels : Finset Label}
      (hT : RecordTyp T labels) {G : Ctx} {subject aliasPath target : Path}
      {V : Typ} (hsubject : PreciseTyping3 G subject T)
      (halias : PreciseFlow G aliasPath (.sngl target) (.sngl target))
      (htarget : PreciseTyping2 G target V) (hr : ReplTyp target aliasPath T T') :
      ReplacementPath G subject T' := by
    cases hT with
    | one hD heq =>
        cases hr with
        | rcd hr => exact hD.replacementQP hsubject halias htarget hr
    | cons hrest hD heq hfresh =>
        cases hr with
        | andLeft hr =>
            exact .and (hrest.replacementQP hsubject.andLeft halias htarget hr)
              (.invertible (.precise hsubject.andRight))
        | andRight hr =>
            cases hr with
            | rcd hr =>
                exact .and (.invertible (.precise hsubject.andLeft))
                  (hD.replacementQP hsubject.andRight halias htarget hr)

  theorem InertTyp.replacementQP {T T' : Typ} (hT : InertTyp T)
      {G : Ctx} {subject aliasPath target : Path} {V : Typ}
      (hi : Inert G) (hsubject : PreciseTyping3 G subject T)
      (halias : PreciseFlow G aliasPath (.sngl target) (.sngl target))
      (htarget : PreciseTyping2 G target V) (hr : ReplTyp target aliasPath T T') :
      ReplacementPath G subject T' := by
    have ha3 : PreciseTyping3 G aliasPath (.sngl target) := .precise (.flow halias)
    have ht3 : PreciseTyping3 G target V := .precise htarget
    cases hT with
    | all =>
        cases hr with
        | allDom hr =>
            exact .all ∅ (.invertible (.precise hsubject))
              (.snglPQ ha3 ht3 hr.swap) (fun _ _ => .refl)
        | allCod hr =>
            rename_i S T T'
            let L := G.dom
            apply ReplacementPath.all L (.invertible (.precise hsubject)) .refl
            intro y hy
            have hok : Env.Ok (G.push y S) := Env.okPush hi.ok hy
            have hext : Env.Extends G (G.push y S) := .pushRight hy S
            have ha3' := ha3.mono hext hok
            have ht3' := ht3.mono hext hok
            exact (TightSubtyp.snglQP ha3' ht3'
              (hr.openVar htarget.toGeneral.pathNamed halias.sourceNamed y)).toGeneral
    | bnd hrecord =>
        cases hr with
        | bnd hr =>
            exact .recQP halias htarget (.invertible (.precise hsubject)) hr
end

theorem PreciseTyping3.replacementQP {G : Ctx} {subject aliasPath target : Path}
    {T T' V : Typ} (hi : Inert G) (hsubject : PreciseTyping3 G subject T)
    (halias : PreciseFlow G aliasPath (.sngl target) (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp target aliasPath T T') :
    ReplacementPath G subject T' := by
  rcases hsubject.inertSngl hi with hinert | hrecord
  · rcases hinert with hinert | ⟨p, heq⟩
    · exact hinert.replacementQP hi hsubject halias htarget hr
    · subst T
      cases hr with
      | sngl => exact .snglQP halias htarget (.invertible (.precise hsubject))
  · obtain ⟨labels, hrecord⟩ := hrecord
    exact hrecord.replacementQP hsubject halias htarget hr

theorem InvertiblePath.replacementQP {G : Ctx}
    {subject aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (hsubject : InvertiblePath G subject T)
    (halias : PreciseFlow G aliasPath (.sngl target) (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp target aliasPath T T') :
    ReplacementPath G subject T' := by
  cases hsubject with
  | precise h => exact h.replacementQP hi halias htarget hr
  | recPQ hp hq h hr₀ =>
      cases hr with
      | bnd hr => exact .recQP halias htarget (.invertible (.recPQ hp hq h hr₀)) hr
  | selPQ hp hq h =>
      obtain ⟨fields, hsrc, rfl⟩ := hr.path_target
      have hcur := InvertiblePath.selPQ hp hq h
      rw [hsrc] at hcur
      exact .selQP halias htarget (.invertible hcur)
  | snglPQ hp hq h =>
      obtain ⟨fields, hsrc, rfl⟩ := hr.sngl_target
      have hcur := InvertiblePath.snglPQ hp hq h
      rw [hsrc] at hcur
      exact .snglQP halias htarget (.invertible hcur)
  | self h =>
      obtain ⟨fields, hsrc, rfl⟩ := hr.sngl_target
      have hself : InvertiblePath G subject (.sngl (target.selectFields fields)) := by
        rw [← hsrc]
        exact .self h
      exact .snglQP halias htarget (.invertible hself)

theorem ReplacementPath.replacementQP {G : Ctx}
    {subject aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (hsubject : ReplacementPath G subject T)
    (halias : PreciseFlow G aliasPath (.sngl target) (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp target aliasPath T T') :
    ReplacementPath G subject T' := by
  have ha3 : PreciseTyping3 G aliasPath (.sngl target) := .precise (.flow halias)
  have ht3 : PreciseTyping3 G target V := .precise htarget
  generalize heq : T = U at hsubject
  induction hsubject generalizing T T' with
  | invertible h =>
      cases heq
      exact h.replacementQP hi halias htarget hr
  | and h₁ h₂ ih₁ ih₂ =>
      cases heq
      cases hr with
      | andLeft hr => exact .and (ih₁ hr rfl) h₂
      | andRight hr => exact .and h₁ (ih₂ hr rfl)
  | bnd h ih =>
      cases heq
      cases hr with
      | bnd hr =>
          rename_i p T T'
          apply ReplacementPath.bnd
          exact ih (hr.openPath htarget.toGeneral.pathNamed halias.sourceNamed p) rfl
  | sel h hf ih =>
      cases heq
      obtain ⟨fields, hsrc, rfl⟩ := hr.path_target
      rw [hsrc] at hf
      exact .selQP halias htarget (.sel h hf)
  | rcdIntro h ih =>
      cases heq
      cases hr with
      | rcd hr =>
          cases hr with
          | trm hr => exact .rcdIntro (ih hr rfl)
  | recQP hp hq h hr₀ ih =>
      cases heq
      cases hr with
      | bnd hr => exact .recQP halias htarget (.recQP hp hq h hr₀) hr
  | selQP hp hq h ih =>
      cases heq
      obtain ⟨fields, hsrc, rfl⟩ := hr.path_target
      have hcur := ReplacementPath.selQP hp hq h
      rw [hsrc] at hcur
      exact .selQP halias htarget hcur
  | snglQP hp hq h ih =>
      cases heq
      obtain ⟨fields, hsrc, rfl⟩ := hr.sngl_target
      have hcur := ReplacementPath.snglQP hp hq h
      rw [hsrc] at hcur
      exact .snglQP halias htarget hcur
  | top h ih =>
      cases heq
      cases hr
  | trm h hs ih =>
      cases heq
      cases hr with
      | rcd hr =>
          cases hr with
          | trm hr => exact .trm h (.trans hs (.snglQP ha3 ht3 hr))
  | typ h hLo hHi ih =>
      cases heq
      cases hr with
      | rcd hr =>
          cases hr with
          | typLo hr =>
              exact .typ h (.trans (.snglPQ ha3 ht3 hr.swap) hLo) hHi
          | typHi hr =>
              exact .typ h hLo (.trans hHi (.snglQP ha3 ht3 hr))
  | all L h hdom hbody ih =>
      cases heq
      cases hr with
      | allDom hr =>
          let L' := L ∪ G.dom
          apply ReplacementPath.all L' h
            (.trans (.snglPQ ha3 ht3 hr.swap) hdom)
          intro y hy
          simp only [L', Finset.mem_union, not_or] at hy
          exact (hbody y hy.1).narrow
            (Subenv.last (TightSubtyp.snglPQ ha3 ht3 hr.swap).toGeneral
              (Env.okPush hi.ok hy.2) (Env.okPush hi.ok hy.2))
      | allCod hr =>
          let L' := L ∪ G.dom
          apply ReplacementPath.all L' h hdom
          intro y hy
          simp only [L', Finset.mem_union, not_or] at hy
          exact .trans (hbody y hy.1)
            (TightSubtyp.snglQP
              (ha3.mono (.pushRight hy.2 _) (Env.okPush hi.ok hy.2))
              (ht3.mono (.pushRight hy.2 _) (Env.okPush hi.ok hy.2))
              (hr.openVar htarget.toGeneral.pathNamed halias.sourceNamed y)).toGeneral

theorem ReplacementPath.replacementQP2 {G : Ctx}
    {subject aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (hsubject : ReplacementPath G subject T)
    (halias : PreciseTyping2 G aliasPath (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp target aliasPath T T') :
    ReplacementPath G subject T' := by
  generalize heq : Typ.sngl target = U at halias
  induction halias generalizing subject target T T' V with
  | flow halias =>
      cases heq
      have hsource := halias.snglSource_eq hi
      subst hsource
      exact hsubject.replacementQP hi halias htarget hr
  | snglTrans hp hfield ihp ihfield =>
      cases heq
      obtain ⟨V', htarget'⟩ := htarget.backtrack
      exact ihp hsubject htarget' hr.fieldElim rfl

theorem ReplacementPath.replacementQP3 {G : Ctx}
    {subject aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (hsubject : ReplacementPath G subject T)
    (halias : PreciseTyping3 G aliasPath (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp target aliasPath T T') :
    ReplacementPath G subject T' := by
  generalize heq : Typ.sngl target = U at halias
  induction halias generalizing subject target T T' V with
  | precise halias =>
      cases heq
      exact hsubject.replacementQP2 hi halias htarget hr
  | snglTrans hp hrest ih =>
      obtain ⟨W, hr₁, hr₂⟩ := hr.insert _
      obtain ⟨V', hmiddle⟩ := hrest.precise2Exists
      have hmid := ih hsubject htarget hr₁ heq
      exact hmid.replacementQP2 hi hp hmiddle hr₂

theorem ReplacementPath.replacementQPStar {G : Ctx}
    {subject aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (hsubject : ReplacementPath G subject T)
    (halias : PreciseTyping3 G aliasPath (.sngl target))
    (htarget : PreciseTyping2 G target V)
    (hr : Star (ReplTyp target aliasPath) T T') :
    ReplacementPath G subject T' := by
  induction hr generalizing subject with
  | refl => exact hsubject
  | step hr _ ih =>
      exact ih (hsubject.replacementQP3 hi halias htarget hr)

theorem ReplacementPath.andParts {G : Ctx} {p : Path} {T U : Typ}
    (h : ReplacementPath G p (.and T U)) :
    ReplacementPath G p T ∧ ReplacementPath G p U := by
  cases h with
  | invertible h =>
      exact ⟨.invertible h.andParts.1, .invertible h.andParts.2⟩
  | and hT hU => exact ⟨hT, hU⟩

theorem ReplacementPath.toInvertibleExists {G : Ctx} {p : Path} {T : Typ}
    (h : ReplacementPath G p T) : ∃ U, InvertiblePath G p U := by
  induction h with
  | invertible h => exact ⟨_, h⟩
  | and _ _ ihT _ => exact ihT
  | bnd _ ih => exact ih
  | sel _ _ ih => exact ih
  | rcdIntro _ ih =>
      obtain ⟨_, hfield⟩ := ih
      exact hfield.backtrack
  | recQP _ _ _ _ ih => exact ih
  | selQP _ _ _ ih => exact ih
  | snglQP _ _ _ ih => exact ih
  | top _ ih => exact ih
  | trm _ _ ih => exact ih
  | typ _ _ _ ih => exact ih
  | all _ _ _ _ ih => exact ih

theorem ReplacementPath.preciseExists {G : Ctx} {p : Path} {T : Typ}
    (h : ReplacementPath G p T) : ∃ U, PreciseTyping3 G p U := by
  obtain ⟨_, hinv⟩ := h.toInvertibleExists
  exact hinv.preciseExists

theorem ReplacementPath.pathSel {G : Ctx} {p q : Path}
    {A : Signature.TypLabel} {T : Typ} (hi : Inert G)
    (hp : PreciseTyping3 G p (.rcd (.typ A T T)))
    (h : ReplacementPath G q (.path p A)) : ReplacementPath G q T := by
  generalize heq : Typ.path p A = V at h
  induction h generalizing p A T with
  | invertible h =>
      cases heq
      exact .invertible (h.pathSel hi hp)
  | and hT hU ihT ihU => cases heq
  | bnd h ih => cases heq
  | sel h hf ih =>
      cases heq
      have heqT := hp.decTypTarget_unique hi (.precise (.flow hf))
      cases heqT
      exact h
  | rcdIntro h ih => cases heq
  | recQP hpq hq h hr ih => cases heq
  | selQP hpq hq h ih =>
      cases heq
      have hs := (PreciseTyping3.precise (.flow hpq)).fieldTransSnglFromLeft hi hp
      have hp' := hp.invertSngl_record hi
        (by exact ⟨_, .one .typ rfl⟩) hs
      exact ih hp' rfl
  | snglQP hpq hq h ih => cases heq
  | top h ih => cases heq
  | trm h hs ih => cases heq
  | typ h hLo hHi ih => cases heq
  | all L h hdom hbody ih => cases heq

theorem ReplacementPath.pathSelExists {G : Ctx} {p q : Path}
    {A : Signature.TypLabel} (hi : Inert G)
    (h : ReplacementPath G q (.path p A)) :
    ∃ T, PreciseTyping3 G p (.rcd (.typ A T T)) ∧
      ReplacementPath G q T := by
  generalize heq : Typ.path p A = V at h
  induction h generalizing p A with
  | invertible h =>
      cases heq
      obtain ⟨T, hp, hT⟩ := h.pathSelExists hi
      exact ⟨T, hp, .invertible hT⟩
  | and hT hU ihT ihU => cases heq
  | bnd h ih => cases heq
  | sel h hf ih =>
      cases heq
      exact ⟨_, .precise (.flow hf), h⟩
  | rcdIntro h ih => cases heq
  | recQP hpq hq h hr ih => cases heq
  | selQP hpq hq h ih =>
      cases heq
      obtain ⟨T, hp, hT⟩ := ih rfl
      have hs := (PreciseTyping3.precise (.flow hpq)).fieldTransSngl hp
      exact ⟨T, hs.snglTrans3 hp, hT⟩
  | snglQP hpq hq h ih => cases heq
  | top h ih => cases heq
  | trm h hs ih => cases heq
  | typ h hLo hHi ih => cases heq
  | all L h hdom hbody ih => cases heq

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
