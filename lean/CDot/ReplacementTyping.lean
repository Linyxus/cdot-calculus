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

mutual
  theorem RecordDec.replacementPQ {D D' : Dec} (hD : RecordDec D)
      {G : Ctx} {subject aliasPath target : Path} {V : Typ}
      (hsubject : PreciseTyping3 G subject (.rcd D))
      (halias : PreciseFlow G aliasPath (.sngl target) (.sngl target))
      (htarget : PreciseTyping2 G target V) (hr : ReplDec aliasPath target D D') :
      ReplacementPath G subject (.rcd D') := by
    have ha3 : PreciseTyping3 G aliasPath (.sngl target) := .precise (.flow halias)
    have ht3 : PreciseTyping3 G target V := .precise htarget
    cases hD with
    | typ =>
        cases hr with
        | typLo hr =>
            exact .typ (.invertible (.precise hsubject))
              (.snglQP ha3 ht3 hr.swap) .refl
        | typHi hr =>
            exact .typ (.invertible (.precise hsubject)) .refl
              (.snglPQ ha3 ht3 hr)
    | trm hT =>
        cases hr with
        | trm hr =>
            exact .trm (.invertible (.precise hsubject))
              (.snglPQ ha3 ht3 hr)
    | trmSngl =>
        cases hr with
        | trm hr =>
            exact .trm (.invertible (.precise hsubject))
              (.snglPQ ha3 ht3 hr)

  theorem RecordTyp.replacementPQ {T T' : Typ} {labels : Finset Label}
      (hT : RecordTyp T labels) {G : Ctx} {subject aliasPath target : Path}
      {V : Typ} (hsubject : PreciseTyping3 G subject T)
      (halias : PreciseFlow G aliasPath (.sngl target) (.sngl target))
      (htarget : PreciseTyping2 G target V) (hr : ReplTyp aliasPath target T T') :
      ReplacementPath G subject T' := by
    cases hT with
    | one hD heq =>
        cases hr with
        | rcd hr => exact hD.replacementPQ hsubject halias htarget hr
    | cons hrest hD heq hfresh =>
        cases hr with
        | andLeft hr =>
            exact .and (hrest.replacementPQ hsubject.andLeft halias htarget hr)
              (.invertible (.precise hsubject.andRight))
        | andRight hr =>
            cases hr with
            | rcd hr =>
                exact .and (.invertible (.precise hsubject.andLeft))
                  (hD.replacementPQ hsubject.andRight halias htarget hr)

  theorem InertTyp.replacementPQ {T T' : Typ} (hT : InertTyp T)
      {G : Ctx} {subject aliasPath target : Path} {V : Typ}
      (hi : Inert G) (hsubject : PreciseTyping3 G subject T)
      (halias : PreciseFlow G aliasPath (.sngl target) (.sngl target))
      (htarget : PreciseTyping2 G target V) (hr : ReplTyp aliasPath target T T') :
      ReplacementPath G subject T' := by
    have ha3 : PreciseTyping3 G aliasPath (.sngl target) := .precise (.flow halias)
    have ht3 : PreciseTyping3 G target V := .precise htarget
    cases hT with
    | all =>
        cases hr with
        | allDom hr =>
            exact .all ∅ (.invertible (.precise hsubject))
              (.snglQP ha3 ht3 hr.swap) (fun _ _ => .refl)
        | allCod hr =>
            rename_i S T T'
            let L := G.dom
            apply ReplacementPath.all L (.invertible (.precise hsubject)) .refl
            intro y hy
            have hok : Env.Ok (G.push y S) := Env.okPush hi.ok hy
            have hext : Env.Extends G (G.push y S) := .pushRight hy S
            exact (TightSubtyp.snglPQ (ha3.mono hext hok) (ht3.mono hext hok)
              (hr.openVar halias.sourceNamed htarget.toGeneral.pathNamed y)).toGeneral
    | bnd hrecord =>
        cases hr with
        | bnd hr =>
            exact .invertible (.recPQ halias htarget (.precise hsubject) hr)
end

theorem PreciseTyping3.replacementPQ {G : Ctx} {subject aliasPath target : Path}
    {T T' V : Typ} (hi : Inert G) (hsubject : PreciseTyping3 G subject T)
    (halias : PreciseFlow G aliasPath (.sngl target) (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp aliasPath target T T') :
    ReplacementPath G subject T' := by
  rcases hsubject.inertSngl hi with hinert | hrecord
  · rcases hinert with hinert | ⟨p, heq⟩
    · exact hinert.replacementPQ hi hsubject halias htarget hr
    · subst T
      cases hr with
      | sngl => exact .invertible (.snglPQ halias htarget (.precise hsubject))
  · obtain ⟨labels, hrecord⟩ := hrecord
    exact hrecord.replacementPQ hsubject halias htarget hr

theorem InvertiblePath.replacementPQ {G : Ctx}
    {subject aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (hsubject : InvertiblePath G subject T)
    (halias : PreciseFlow G aliasPath (.sngl target) (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp aliasPath target T T') :
    ReplacementPath G subject T' := by
  cases hsubject with
  | precise h => exact h.replacementPQ hi halias htarget hr
  | recPQ hp hq h hr₀ =>
      cases hr with
      | bnd hr => exact .invertible (.recPQ halias htarget (.recPQ hp hq h hr₀) hr)
  | selPQ hp hq h =>
      obtain ⟨fields, hsrc, rfl⟩ := hr.path_target
      have hcur := InvertiblePath.selPQ hp hq h
      rw [hsrc] at hcur
      exact .invertible (.selPQ halias htarget hcur)
  | snglPQ hp hq h =>
      obtain ⟨fields, hsrc, rfl⟩ := hr.sngl_target
      have hcur := InvertiblePath.snglPQ hp hq h
      rw [hsrc] at hcur
      exact .invertible (.snglPQ halias htarget hcur)
  | self h =>
      obtain ⟨fields, hsrc, rfl⟩ := hr.sngl_target
      have hself : InvertiblePath G subject (.sngl (aliasPath.selectFields fields)) := by
        rw [← hsrc]
        exact .self h
      exact .invertible (.snglPQ halias htarget hself)

mutual
  theorem ReplTyp.commuteTyped {q p : Path} {T T' : Typ}
      (h₁ : ReplTyp q p T T') {q₀ r₀ : Path} {T₂ : Typ} {G : Ctx}
      (h₂ : ReplTyp q₀ r₀ T' T₂) (hi : Inert G)
      (hp : PreciseFlow G p (.sngl q) (.sngl q))
      (hq₀ : PreciseFlow G q₀ (.sngl r₀) (.sngl r₀)) :
      T = T₂ ∨ ∃ T₃, ReplTyp q₀ r₀ T T₃ ∧ ReplTyp q p T₃ T₂ := by
    cases h₁ with
    | rcd h₁ =>
        cases h₂ with
        | rcd h₂ =>
            rcases h₁.commuteTyped h₂ hi hp hq₀ with heq | ⟨D₃, hl, hr⟩
            · exact Or.inl (congrArg Typ.rcd heq)
            · exact Or.inr ⟨.rcd D₃, .rcd hl, .rcd hr⟩
    | andLeft h₁ =>
        cases h₂ with
        | andLeft h₂ =>
            rcases h₁.commuteTyped h₂ hi hp hq₀ with heq | ⟨V, hl, hr⟩
            · exact Or.inl (congrArg (fun X => Typ.and X _) heq)
            · exact Or.inr ⟨.and V _, .andLeft hl, .andLeft hr⟩
        | andRight h₂ =>
            exact Or.inr ⟨.and _ _, .andRight h₂, .andLeft h₁⟩
    | andRight h₁ =>
        cases h₂ with
        | andLeft h₂ =>
            exact Or.inr ⟨.and _ _, .andLeft h₂, .andRight h₁⟩
        | andRight h₂ =>
            rcases h₁.commuteTyped h₂ hi hp hq₀ with heq | ⟨V, hl, hr⟩
            · exact Or.inl (congrArg (fun X => Typ.and _ X) heq)
            · exact Or.inr ⟨.and _ V, .andRight hl, .andRight hr⟩
    | path =>
        obtain ⟨fields₀, heq, hT₂⟩ := h₂.path_target
        subst T₂
        have hout := hp.snglSelect_unique hi hq₀ heq.symm
        exact Or.inl (congrArg (fun r => Typ.path r _) hout)
    | bnd h₁ =>
        cases h₂ with
        | bnd h₂ =>
            rcases h₁.commuteTyped h₂ hi hp hq₀ with heq | ⟨V, hl, hr⟩
            · exact Or.inl (congrArg Typ.bnd heq)
            · exact Or.inr ⟨.bnd V, .bnd hl, .bnd hr⟩
    | allDom h₁ =>
        cases h₂ with
        | allDom h₂ =>
            rcases h₁.commuteTyped h₂ hi hp hq₀ with heq | ⟨V, hl, hr⟩
            · exact Or.inl (congrArg (fun X => Typ.all X _) heq)
            · exact Or.inr ⟨.all V _, .allDom hl, .allDom hr⟩
        | allCod h₂ =>
            exact Or.inr ⟨.all _ _, .allCod h₂, .allDom h₁⟩
    | allCod h₁ =>
        cases h₂ with
        | allDom h₂ =>
            exact Or.inr ⟨.all _ _, .allDom h₂, .allCod h₁⟩
        | allCod h₂ =>
            rcases h₁.commuteTyped h₂ hi hp hq₀ with heq | ⟨V, hl, hr⟩
            · exact Or.inl (congrArg (fun X => Typ.all _ X) heq)
            · exact Or.inr ⟨.all _ V, .allCod hl, .allCod hr⟩
    | sngl =>
        obtain ⟨fields₀, heq, hT₂⟩ := h₂.sngl_target
        subst T₂
        have hout := hp.snglSelect_unique hi hq₀ heq.symm
        exact Or.inl (congrArg Typ.sngl hout)

  theorem ReplDec.commuteTyped {q p : Path} {D D' : Dec}
      (h₁ : ReplDec q p D D') {q₀ r₀ : Path} {D₂ : Dec} {G : Ctx}
      (h₂ : ReplDec q₀ r₀ D' D₂) (hi : Inert G)
      (hp : PreciseFlow G p (.sngl q) (.sngl q))
      (hq₀ : PreciseFlow G q₀ (.sngl r₀) (.sngl r₀)) :
      D = D₂ ∨ ∃ D₃, ReplDec q₀ r₀ D D₃ ∧ ReplDec q p D₃ D₂ := by
    cases h₁ with
    | typLo h₁ =>
        cases h₂ with
        | typLo h₂ =>
            rcases h₁.commuteTyped h₂ hi hp hq₀ with heq | ⟨V, hl, hr⟩
            · exact Or.inl (congrArg (fun X => Dec.typ _ X _) heq)
            · exact Or.inr ⟨.typ _ V _, .typLo hl, .typLo hr⟩
        | typHi h₂ =>
            exact Or.inr ⟨.typ _ _ _, .typHi h₂, .typLo h₁⟩
    | typHi h₁ =>
        cases h₂ with
        | typLo h₂ =>
            exact Or.inr ⟨.typ _ _ _, .typLo h₂, .typHi h₁⟩
        | typHi h₂ =>
            rcases h₁.commuteTyped h₂ hi hp hq₀ with heq | ⟨V, hl, hr⟩
            · exact Or.inl (congrArg (fun X => Dec.typ _ _ X) heq)
            · exact Or.inr ⟨.typ _ _ V, .typHi hl, .typHi hr⟩
    | trm h₁ =>
        cases h₂ with
        | trm h₂ =>
            rcases h₁.commuteTyped h₂ hi hp hq₀ with heq | ⟨V, hl, hr⟩
            · exact Or.inl (congrArg (fun X => Dec.trm _ X) heq)
            · exact Or.inr ⟨.trm _ V, .trm hl, .trm hr⟩
end

theorem ReplacementPath.replacementPQ {G : Ctx}
    {subject aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (hsubject : ReplacementPath G subject T)
    (halias : PreciseFlow G aliasPath (.sngl target) (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp aliasPath target T T') :
    ReplacementPath G subject T' := by
  have ha3 : PreciseTyping3 G aliasPath (.sngl target) := .precise (.flow halias)
  have ht3 : PreciseTyping3 G target V := .precise htarget
  generalize heq : T = U at hsubject
  induction hsubject generalizing T T' with
  | invertible h =>
      cases heq
      exact h.replacementPQ hi halias htarget hr
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
          exact ih (hr.openPath halias.sourceNamed htarget.toGeneral.pathNamed p) rfl
  | sel h hf ih =>
      cases heq
      obtain ⟨fields, hsrc, hdst⟩ := hr.path_target
      rw [hsrc] at hf
      have hnil := halias.snglFieldsElim hi hf
      rw [hnil, Path.selectFields_nil] at hf
      have hsource := halias.source_unique hi hf
      obtain ⟨B, hB⟩ := hf.recordSource_bnd hi
      rw [hB, halias.snglSource_eq hi] at hsource
      cases hsource
  | rcdIntro h ih =>
      cases heq
      cases hr with
      | rcd hr =>
          cases hr with
          | trm hr => exact .rcdIntro (ih hr rfl)
  | recQP hp hq h hr₀ ih =>
      cases heq
      cases hr with
      | bnd hr =>
          rcases hr₀.commuteTyped hr hi hp halias with heq | ⟨W, hl, hr⟩
          · cases heq
            exact h
          · have hmid := ih (.bnd hl) rfl
            exact hmid.replacementQP hi hp hq (.bnd hr)
  | selQP hp hq h ih =>
      cases heq
      rename_i p₀ q₀ W r fields A
      let hstep : ReplTyp q₀ p₀ (.path (q₀.selectFields fields) A)
          (.path (p₀.selectFields fields) A) := .path
      rcases hstep.commuteTyped hr hi hp halias with heq | ⟨W, hl, hr⟩
      · cases heq
        exact h
      · have hmid := ih hl rfl
        exact hmid.replacementQP hi hp hq hr
  | snglQP hp hq h ih =>
      cases heq
      rename_i p₀ q₀ W r fields
      let hstep : ReplTyp q₀ p₀ (.sngl (q₀.selectFields fields))
          (.sngl (p₀.selectFields fields)) := .sngl
      rcases hstep.commuteTyped hr hi hp halias with heq | ⟨W, hl, hr⟩
      · cases heq
        exact h
      · have hmid := ih hl rfl
        exact hmid.replacementQP hi hp hq hr
  | top h ih =>
      cases heq
      cases hr
  | trm h hs ih =>
      cases heq
      cases hr with
      | rcd hr =>
          cases hr with
          | trm hr => exact .trm h (.trans hs (.snglPQ ha3 ht3 hr))
  | typ h hLo hHi ih =>
      cases heq
      cases hr with
      | rcd hr =>
          cases hr with
          | typLo hr =>
              exact .typ h (.trans (.snglQP ha3 ht3 hr.swap) hLo) hHi
          | typHi hr =>
              exact .typ h hLo (.trans hHi (.snglPQ ha3 ht3 hr))
  | all L h hdom hbody ih =>
      cases heq
      cases hr with
      | allDom hr =>
          let L' := L ∪ G.dom
          apply ReplacementPath.all L' h
            (.trans (.snglQP ha3 ht3 hr.swap) hdom)
          intro y hy
          simp only [L', Finset.mem_union, not_or] at hy
          exact (hbody y hy.1).narrow
            (Subenv.last (TightSubtyp.snglQP ha3 ht3 hr.swap).toGeneral
              (Env.okPush hi.ok hy.2) (Env.okPush hi.ok hy.2))
      | allCod hr =>
          let L' := L ∪ G.dom
          apply ReplacementPath.all L' h hdom
          intro y hy
          simp only [L', Finset.mem_union, not_or] at hy
          exact .trans (hbody y hy.1)
            (TightSubtyp.snglPQ
              (ha3.mono (.pushRight hy.2 _) (Env.okPush hi.ok hy.2))
              (ht3.mono (.pushRight hy.2 _) (Env.okPush hi.ok hy.2))
              (hr.openVar halias.sourceNamed htarget.toGeneral.pathNamed y)).toGeneral

theorem ReplacementPath.replacementPQ2 {G : Ctx}
    {subject aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (hsubject : ReplacementPath G subject T)
    (halias : PreciseTyping2 G aliasPath (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp aliasPath target T T') :
    ReplacementPath G subject T' := by
  generalize heq : Typ.sngl target = U at halias
  induction halias generalizing subject target T T' V with
  | flow halias =>
      cases heq
      have hsource := halias.snglSource_eq hi
      subst hsource
      exact hsubject.replacementPQ hi halias htarget hr
  | snglTrans hp hfield ihp ihfield =>
      cases heq
      obtain ⟨V', htarget'⟩ := htarget.backtrack
      exact ihp hsubject htarget' hr.fieldElim rfl

theorem ReplacementPath.replacementPQ3 {G : Ctx}
    {subject aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (hsubject : ReplacementPath G subject T)
    (halias : PreciseTyping3 G aliasPath (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp aliasPath target T T') :
    ReplacementPath G subject T' := by
  generalize heq : Typ.sngl target = U at halias
  induction halias generalizing subject target T T' V with
  | precise halias =>
      cases heq
      exact hsubject.replacementPQ2 hi halias htarget hr
  | snglTrans hp hrest ih =>
      obtain ⟨W, hr₁, hr₂⟩ := hr.insert _
      obtain ⟨V', hmiddle⟩ := hrest.precise2Exists
      have hmid := hsubject.replacementPQ2 hi hp hmiddle hr₁
      exact ih hmid htarget hr₂ heq

theorem ReplacementPath.replacementPQStar {G : Ctx}
    {subject aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (hsubject : ReplacementPath G subject T)
    (halias : PreciseTyping3 G aliasPath (.sngl target))
    (htarget : PreciseTyping2 G target V)
    (hr : Star (ReplTyp aliasPath target) T T') :
    ReplacementPath G subject T' := by
  induction hr generalizing subject with
  | refl => exact hsubject
  | step hr _ ih =>
      exact ih (hsubject.replacementPQ3 hi halias htarget hr)

theorem ReplacementPath.pathSelIntro {G : Ctx} {p q : Path}
    {A : Signature.TypLabel} {T : Typ} (hi : Inert G)
    (hp : PreciseTyping3 G p (.rcd (.typ A T T)))
    (h : ReplacementPath G q T) : ReplacementPath G q (.path p A) := by
  generalize heq : Typ.rcd (Dec.typ A T T) = U at hp
  induction hp generalizing A T with
  | precise hp =>
      cases heq
      cases hp with
      | flow hp => exact .sel h hp
  | snglTrans hs hp ih =>
      have hq := ih h heq
      obtain ⟨V, htarget⟩ := hp.precise2Exists
      exact hq.replacementQP2 hi hs htarget (.pathRoot _ _ A)

theorem ReplacementPath.bot_false {G : Ctx} {p : Path} (hi : Inert G)
    (h : ReplacementPath G p .bot) : False := by
  cases h with
  | invertible h => exact h.bot_false hi

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

theorem InvertiblePath.snglTransReplacement {G : Ctx} {p q : Path}
    {T : Typ} (hi : Inert G) (hpq : PreciseTyping3 G p (.sngl q))
    (h : InvertiblePath G q T) : ReplacementPath G p T := by
  generalize heq : q = r at h
  induction h generalizing p q with
  | precise h =>
      cases heq
      exact .invertible (.precise (hpq.snglTrans3 h))
  | recPQ hs ht h hr ih =>
      cases heq
      exact (ih hpq rfl).replacementPQ hi hs ht (.bnd hr)
  | selPQ hs ht h ih =>
      cases heq
      exact (ih hpq rfl).replacementPQ hi hs ht .path
  | snglPQ hs ht h ih =>
      cases heq
      exact (ih hpq rfl).replacementPQ hi hs ht .sngl
  | self h =>
      cases heq
      exact .invertible (.precise hpq)

theorem ReplacementPath.snglTransPrecise {G : Ctx} {p q : Path}
    {T : Typ} (hi : Inert G) (hpq : PreciseTyping3 G p (.sngl q))
    (h : ReplacementPath G q T) : ReplacementPath G p T := by
  generalize heq : q = r at h
  induction h generalizing p q with
  | invertible h =>
      cases heq
      exact h.snglTransReplacement hi hpq
  | and hT hU ihT ihU =>
      cases heq
      exact .and (ihT hpq rfl) (ihU hpq rfl)
  | bnd h ih =>
      cases heq
      obtain ⟨V, hq⟩ := h.preciseExists
      obtain ⟨W, hq₂⟩ := hq.precise2Exists
      have hopen := ih hpq rfl
      exact .bnd (hopen.replacementQPStar hi hpq hq₂ (Typ.openPath_repl _ _ _))
  | sel h hf ih =>
      cases heq
      exact .sel (ih hpq rfl) hf
  | rcdIntro h ih =>
      cases heq
      obtain ⟨V, hqfield⟩ := h.preciseExists
      have hfield := hpq.fieldSngl hqfield
      exact .rcdIntro (ih hfield rfl)
  | recQP hs ht h hr ih =>
      cases heq
      exact .recQP hs ht (ih hpq rfl) hr
  | selQP hs ht h ih =>
      cases heq
      exact .selQP hs ht (ih hpq rfl)
  | snglQP hs ht h ih =>
      cases heq
      exact .snglQP hs ht (ih hpq rfl)
  | top h ih =>
      cases heq
      exact .top (ih hpq rfl)
  | trm h hs ih =>
      cases heq
      exact .trm (ih hpq rfl) hs
  | typ h hLo hHi ih =>
      cases heq
      exact .typ (ih hpq rfl) hLo hHi
  | all L h hdom hbody ih =>
      cases heq
      exact .all L (ih hpq rfl) hdom hbody

theorem InvertiblePath.snglTrans {G : Ctx} {p q : Path} {T : Typ}
    (hi : Inert G) (hpq : InvertiblePath G p (.sngl q))
    (hq : ReplacementPath G q T) : ReplacementPath G p T := by
  generalize heq : Typ.sngl q = U at hpq
  induction hpq generalizing q T with
  | precise hpq =>
      cases heq
      exact hq.snglTransPrecise hi hpq
  | recPQ hs ht h hr ih => cases heq
  | selPQ hs ht h ih => cases heq
  | snglPQ hs ht h ih =>
      cases heq
      obtain ⟨V, htarget⟩ := hq.preciseExists
      have hfield := (PreciseTyping3.precise (.flow hs)).fieldTransSngl htarget
      have hmid := hq.snglTransPrecise hi hfield
      exact ih hmid rfl
  | self h =>
      cases heq
      exact hq

theorem InvertiblePath.snglPreciseCases {G : Ctx} {p q : Path} {U : Typ}
    (hi : Inert G) (hpq : InvertiblePath G p (.sngl q))
    (hq : PreciseTyping3 G q U) :
    (∃ r, PreciseTyping3 G p (.sngl r) ∧
      (r = q ∨ PreciseTyping3 G r (.sngl q))) ∨ p = q := by
  generalize heq : Typ.sngl q = T at hpq
  induction hpq generalizing q U with
  | precise hpq =>
      cases heq
      exact Or.inl ⟨q, hpq, Or.inl rfl⟩
  | recPQ hs ht h hr ih => cases heq
  | selPQ hs ht h ih => cases heq
  | snglPQ hs ht h ih =>
      cases heq
      have hs3 : PreciseTyping3 G _ (.sngl _) := .precise (.flow hs)
      have hsource := hs3.fieldTransSngl hq
      rcases ih hsource rfl with ⟨r, hpr, rfl | hra⟩ | rfl
      · exact Or.inl ⟨_, hpr, Or.inr (hs3.fieldTransSngl hq)⟩
      · exact Or.inl ⟨r, hpr,
          Or.inr (hra.snglTrans3 (hs3.fieldTransSngl hq))⟩
      · exact Or.inl ⟨_, hs3.fieldTransSngl hq, Or.inl rfl⟩
  | self h =>
      cases heq
      exact Or.inr rfl

theorem ReplacementPath.snglToInvertible {G : Ctx} {p q : Path} {U : Typ}
    (hi : Inert G) (hpq : ReplacementPath G p (.sngl q))
    (hq : PreciseTyping3 G q U) :
    ∃ r S, InvertiblePath G p (.sngl r) ∧ PreciseTyping3 G r S ∧
      (q = r ∨ PreciseTyping3 G q (.sngl r)) := by
  generalize heq : Typ.sngl q = T at hpq
  induction hpq generalizing q U with
  | invertible hpq =>
      cases heq
      exact ⟨q, U, hpq, hq, Or.inl rfl⟩
  | and hT hU ihT ihU => cases heq
  | bnd h ih => cases heq
  | sel h hf ih => cases heq
  | rcdIntro h ih => cases heq
  | recQP hs ht h hr ih => cases heq
  | selQP hs ht h ih => cases heq
  | snglQP hs ht h ih =>
      cases heq
      have hs3 : PreciseTyping3 G _ (.sngl _) := .precise (.flow hs)
      obtain ⟨V, hq₂⟩ := hq.precise2Exists
      obtain ⟨W, htarget₂⟩ := PreciseTyping2.fieldsOtherExists hi hs ht hq₂
      have htarget : PreciseTyping3 G _ W := .precise htarget₂
      obtain ⟨r, S, hpr, hr, hrel⟩ := ih htarget rfl
      apply Exists.intro r
      apply Exists.intro S
      refine ⟨hpr, hr, ?_⟩
      right
      rcases hrel with rfl | hrel
      · exact hs3.fieldTransSngl hr
      · exact (hs3.fieldTransSngl hrel).snglTrans3 hrel
  | top h ih => cases heq
  | trm h hs ih => cases heq
  | typ h hLo hHi ih => cases heq
  | all L h hdom hbody ih => cases heq

theorem ReplacementPath.snglReverse {G : Ctx} {p r s : Path} {U : Typ}
    (hi : Inert G) (hpr : ReplacementPath G p (.sngl r))
    (hsr : PreciseTyping3 G s (.sngl r)) (hr : PreciseTyping3 G r U) :
    ReplacementPath G p (.sngl s) := by
  obtain ⟨V, hr₂⟩ := hr.precise2Exists
  exact hpr.replacementQP3 hi hsr hr₂ (ReplTyp.rootSngl r s)

theorem ReplacementPath.snglTransPreciseRight {G : Ctx} {p q : Path}
    {T : Typ} (hi : Inert G) (hpq : ReplacementPath G p (.sngl q))
    (hqT : PreciseTyping3 G q T) : ReplacementPath G p T := by
  obtain ⟨r, S, hpr, hr, hqr⟩ := hpq.snglToInvertible hi hqT
  rcases hpr.snglPreciseCases hi hr with
    ⟨r', hpr', hr'r⟩ | rfl
  · have hprr : PreciseTyping3 G p (.sngl r) := by
      rcases hr'r with rfl | hr'r
      · exact hpr'
      · exact hpr'.snglTrans3 hr'r
    rcases hqr with rfl | hqr
    · exact .invertible (.precise (hprr.snglTrans3 hqT))
    · rcases hqT.invertSngl hi hqr with hrT | ⟨s, hsT, hrs⟩
      · exact .invertible (.precise (hprr.snglTrans3 hrT))
      · cases hsT
        rcases hrs with rfl | hsr
        · exact .invertible (.precise hprr)
        · exact (ReplacementPath.invertible (.precise hprr)).snglReverse
            hi hsr hr
  · rcases hqr with rfl | hqr
    · exact .invertible (.precise hqT)
    · rcases hqT.invertSngl hi hqr with hpT | ⟨s, hsT, hps⟩
      · exact .invertible (.precise hpT)
      · cases hsT
        rcases hps with rfl | hsp
        · exact .invertible hpr
        · exact (ReplacementPath.invertible hpr).snglReverse hi hsp hr

theorem InvertiblePath.snglTransFromReplacement {G : Ctx} {p q : Path}
    {T : Typ} (hi : Inert G) (hpq : ReplacementPath G p (.sngl q))
    (hq : InvertiblePath G q T) : ReplacementPath G p T := by
  generalize heq : q = r at hq
  induction hq generalizing p q with
  | precise hq =>
      cases heq
      exact hpq.snglTransPreciseRight hi hq
  | recPQ hs ht h hr ih =>
      cases heq
      exact (ih hpq rfl).replacementPQ hi hs ht (.bnd hr)
  | selPQ hs ht h ih =>
      cases heq
      exact (ih hpq rfl).replacementPQ hi hs ht .path
  | snglPQ hs ht h ih =>
      cases heq
      exact (ih hpq rfl).replacementPQ hi hs ht .sngl
  | self h =>
      cases heq
      exact hpq

theorem ReplacementPath.fieldAlias {G : Ctx} {p q : Path}
    {a : Signature.TrmLabel} {T : Typ} (hi : Inert G)
    (hpq : ReplacementPath G p (.sngl q))
    (hqa : ReplacementPath G (q.selectField a) T) :
    ReplacementPath G (p.selectField a) (.sngl (q.selectField a)) := by
  obtain ⟨U, hqa⟩ := hqa.preciseExists
  obtain ⟨V, hq⟩ := hqa.backtrack
  obtain ⟨r, S, hpr, hr, hqr⟩ := hpq.snglToInvertible hi hq
  have hra : ∃ W, PreciseTyping3 G (r.selectField a) W := by
    rcases hqr with rfl | hqr
    · exact ⟨U, hqa⟩
    · exact hqr.fieldOtherExists hi hqa
  obtain ⟨W, hra⟩ := hra
  rcases hpr.snglPreciseCases hi hr with
    ⟨r', hpr', hr'r⟩ | rfl
  · have hpra : PreciseTyping3 G (p.selectField a)
        (.sngl (r.selectField a)) := by
      rcases hr'r with rfl | hr'r
      · exact hpr'.fieldSngl hra
      · have hr'a := hr'r.fieldSngl hra
        exact (hpr'.fieldSngl hr'a).snglTrans3 hr'a
    rcases hqr with rfl | hqr
    · exact .invertible (.precise hpra)
    · exact (ReplacementPath.invertible (.precise hpra)).snglReverse
        hi (hqr.fieldSngl hra) hra
  · rcases hqr with rfl | hqr
    · obtain ⟨W, hpa⟩ := hra.precise2Exists
      exact .invertible (.self hpa)
    · obtain ⟨W, hpa⟩ := hra.precise2Exists
      exact (ReplacementPath.invertible (InvertiblePath.self hpa)).snglReverse
        hi (hqr.fieldSngl hra) hra

theorem ReplacementPath.snglTrans {G : Ctx} {p q : Path} {T : Typ}
    (hi : Inert G) (hpq : ReplacementPath G p (.sngl q))
    (hq : ReplacementPath G q T) : ReplacementPath G p T := by
  generalize heq : q = r at hq
  induction hq generalizing p q with
  | invertible hq =>
      cases heq
      exact hq.snglTransFromReplacement hi hpq
  | and hT hU ihT ihU =>
      cases heq
      exact .and (ihT hpq rfl) (ihU hpq rfl)
  | bnd h ih =>
      rename_i q T
      cases heq
      have hopen := ih hpq rfl
      obtain ⟨U, hq⟩ := h.preciseExists
      obtain ⟨r, S, hpr, hr, hqr⟩ := hpq.snglToInvertible hi hq
      obtain ⟨V, hr₂⟩ := hr.precise2Exists
      rcases hpr.snglPreciseCases hi hr with
        ⟨r', hpr', hr'r⟩ | rfl
      · have hopenr : ReplacementPath G p (T.openPath r) := by
          rcases hqr with rfl | hqr
          · exact hopen
          · exact hopen.replacementPQStar hi hqr hr₂
              (T.openPath_repl q r)
        have hopenr'_typed : ReplacementPath G p (T.openPath r') ∧
            ∃ V', PreciseTyping2 G r' V' := by
          rcases hr'r with rfl | hr'r
          · exact ⟨hopenr, V, hr₂⟩
          · exact ⟨hopenr.replacementQPStar hi hr'r hr₂
              (T.openPath_repl r r'), hr'r.precise2Exists⟩
        obtain ⟨hopenr', V', hr'₂⟩ := hopenr'_typed
        exact .bnd (hopenr'.replacementQPStar hi hpr' hr'₂
          (T.openPath_repl r' p))
      · rcases hqr with rfl | hqr
        · exact .bnd hopen
        · exact .bnd (hopen.replacementPQStar hi hqr hr₂
            (T.openPath_repl q p))
  | sel h hf ih =>
      cases heq
      exact .sel (ih hpq rfl) hf
  | rcdIntro h ih =>
      cases heq
      have hpqa := hpq.fieldAlias hi h
      exact .rcdIntro (ih hpqa rfl)
  | recQP hs ht h hr ih =>
      cases heq
      exact .recQP hs ht (ih hpq rfl) hr
  | selQP hs ht h ih =>
      cases heq
      exact .selQP hs ht (ih hpq rfl)
  | snglQP hs ht h ih =>
      cases heq
      exact .snglQP hs ht (ih hpq rfl)
  | top h ih =>
      cases heq
      exact .top (ih hpq rfl)
  | trm h hs ih =>
      cases heq
      exact .trm (ih hpq rfl) hs
  | typ h hLo hHi ih =>
      cases heq
      exact .typ (ih hpq rfl) hLo hHi
  | all L h hdom hbody ih =>
      cases heq
      exact .all L (ih hpq rfl) hdom hbody

theorem ReplacementPath.subtyp {G : Ctx} {p : Path} {T U : Typ}
    (hi : Inert G) (h : ReplacementPath G p T)
    (hs : TightSubtyp G T U) : ReplacementPath G p U := by
  apply TightSubtyp.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun G T U _ => Inert G → ∀ {p},
      ReplacementPath G p T → ReplacementPath G p U)
  case var => intros; trivial
  case allIntro => intros; trivial
  case allElim => intros; trivial
  case newIntro => intros; trivial
  case newElim => intros; trivial
  case rcdIntro => intros; trivial
  case letE => intros; trivial
  case caseE => intros; trivial
  case sngl => intros; trivial
  case self => intros; trivial
  case pathElim => intros; trivial
  case recIntro => intros; trivial
  case recElim => intros; trivial
  case andIntro => intros; trivial
  case sub => intros; trivial
  case top => intros; exact .top ‹ReplacementPath _ _ _›
  case bot =>
    intro G T hi p h
    exact False.elim (h.bot_false hi)
  case refl => intros; assumption
  case trans =>
    intro G S T U h₁ h₂ ih₁ ih₂ hi p h
    exact ih₂ hi (ih₁ hi h)
  case andLeft => intros; exact (‹ReplacementPath _ _ _›).andParts.1
  case andRight => intros; exact (‹ReplacementPath _ _ _›).andParts.2
  case andIntro =>
    intro G S T U h₁ h₂ ih₁ ih₂ hi p h
    exact .and (ih₁ hi h) (ih₂ hi h)
  case fld =>
    intro G T U a hs ih hi p h
    exact .trm h hs
  case typ =>
    intro G S₂ S₁ T₁ T₂ A hLo hHi ihLo ihHi hi p h
    exact .typ h hLo hHi
  case snglPQ =>
    intro G aliasPath target V T T' hp hq hr hi p h
    obtain ⟨W, hq₂⟩ := hq.precise2Exists
    exact h.replacementPQ3 hi hp hq₂ hr
  case snglQP =>
    intro G aliasPath target V T T' hp hq hr hi p h
    obtain ⟨W, hq₂⟩ := hq.precise2Exists
    exact h.replacementQP3 hi hp hq₂ hr
  case selLo =>
    intro G p A T hp hi q h
    exact h.pathSelIntro hi hp
  case selHi =>
    intro G p A T hp hi q h
    exact h.pathSel hi hp
  case all =>
    intro G S₂ S₁ T₁ T₂ L hdom hbody ih hi p h
    exact .all L h hdom hbody
  case t => exact hs
  all_goals assumption

theorem ReplacementPath.recElim {G : Ctx} {p : Path} {T : Typ}
    (hi : Inert G) (h : ReplacementPath G p (.bnd T)) :
    ReplacementPath G p (T.openPath p) := by
  generalize heq : Typ.bnd T = U at h
  induction h generalizing T with
  | invertible h =>
      cases heq
      generalize heq' : Typ.bnd T = U at h
      induction h generalizing T with
      | precise hp =>
          cases heq'
          rcases hp.bndCases with hopen | ⟨q, V, hpq, hq, hopen⟩
          · exact .invertible (.precise hopen)
          · exact (ReplacementPath.invertible (.precise hopen)).replacementQPStar
              hi hpq hq (T.openPath_repl q _)
      | recPQ hp hq h hr ih =>
          cases heq'
          have hopen := ih rfl
          exact hopen.replacementPQ hi hp hq
            (hr.openPath hp.sourceNamed hq.toGeneral.pathNamed _)
      | selPQ hp hq h ih => cases heq'
      | snglPQ hp hq h ih => cases heq'
      | self h => cases heq'
  | and hT hU ihT ihU => cases heq
  | bnd h ih =>
      cases heq
      exact h
  | sel h hf ih => cases heq
  | rcdIntro h ih => cases heq
  | recQP hp hq h hr ih =>
      cases heq
      have hopen := ih rfl
      exact hopen.replacementQP hi hp hq
        (hr.openPath hq.toGeneral.pathNamed hp.sourceNamed _)
  | selQP hp hq h ih => cases heq
  | snglQP hp hq h ih => cases heq
  | top h ih => cases heq
  | trm h hs ih => cases heq
  | typ h hLo hHi ih => cases heq
  | all L h hdom hbody ih => cases heq

theorem ReplacementPath.fieldElim {G : Ctx} {p : Path}
    {a : Signature.TrmLabel} {T : Typ} (hi : Inert G)
    (h : ReplacementPath G p (.rcd (.trm a T))) :
    ReplacementPath G (p.selectField a) T := by
  generalize heq : Typ.rcd (Dec.trm a T) = U at h
  induction h generalizing a T with
  | invertible h =>
      cases heq
      cases h with
      | precise h => exact .invertible (.precise h.fieldElim)
  | and hT hU ihT ihU => cases heq
  | bnd h ih => cases heq
  | sel h hf ih => cases heq
  | rcdIntro h ih =>
      cases heq
      exact h
  | recQP hp hq h hr ih => cases heq
  | selQP hp hq h ih => cases heq
  | snglQP hp hq h ih => cases heq
  | top h ih => cases heq
  | trm h hs ih =>
      cases heq
      exact (ih rfl).subtyp hi hs
  | typ h hLo hHi ih => cases heq
  | all L h hdom hbody ih => cases heq

theorem TightTyped.pathReplacement {G : Ctx} {p : Path} {T : Typ}
    (hi : Inert G) (h : TightTyped G (.path p) T) :
    ReplacementPath G p T := by
  apply TightTyped.rec
    (motive_1 := fun G t T _ => Inert G → ∀ p,
      t = .path p → ReplacementPath G p T)
    (motive_2 := fun _ _ _ _ => True)
  case var =>
    intro x T G hb hi p heq
    cases heq
    exact .invertible (.precise (.precise (.flow (.bind hi.ok hb))))
  case allIntro => intros; contradiction
  case allElim => intros; contradiction
  case newIntro => intros; contradiction
  case newElim =>
    intro G p a T h ih hi q heq
    cases heq
    exact (ih hi p rfl).fieldElim hi
  case rcdIntro =>
    intro G T p a h ih hi q heq
    cases heq
    exact .rcdIntro (ih hi _ rfl)
  case letE => intros; contradiction
  case caseE => intros; contradiction
  case sngl =>
    intro G p q T hpq hq ihp ihq hi r heq
    cases heq
    exact (ihp hi p rfl).snglTrans hi (ihq hi q rfl)
  case self =>
    intro G p T h ih hi q heq
    cases heq
    obtain ⟨U, hp⟩ := (ih hi p rfl).preciseExists
    obtain ⟨V, hp₂⟩ := hp.precise2Exists
    exact .invertible (.self hp₂)
  case pathElim =>
    intro G p q a T hpq hqa ihp ihq hi r heq
    cases heq
    exact (ihp hi p rfl).fieldAlias hi (ihq hi _ rfl)
  case recIntro =>
    intro G p T h ih hi q heq
    cases heq
    exact .bnd (ih hi p rfl)
  case recElim =>
    intro G p T h ih hi q heq
    cases heq
    exact (ih hi p rfl).recElim hi
  case andIntro =>
    intro G p T U hT hU ihT ihU hi q heq
    cases heq
    exact .and (ihT hi p rfl) (ihU hi p rfl)
  case sub =>
    intro G t S T ht hs iht ihs hi p heq
    exact (iht hi p heq).subtyp hi hs
  case top => intros; trivial
  case bot => intros; trivial
  case refl => intros; trivial
  case trans => intros; trivial
  case andLeft => intros; trivial
  case andRight => intros; trivial
  case andIntro => intros; trivial
  case fld => intros; trivial
  case typ => intros; trivial
  case snglPQ => intros; trivial
  case snglQP => intros; trivial
  case selLo => intros; trivial
  case selHi => intros; trivial
  case all => intros; trivial
  case t => exact h
  all_goals first | assumption | rfl

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

theorem InvertibleVal.replacementQP {G : Ctx} {v : Val}
    {aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (h : InvertibleVal G v T)
    (halias : PreciseFlow G aliasPath (.sngl target) (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp target aliasPath T T') :
    ReplacementVal G v T' := by
  have ha3 : PreciseTyping3 G aliasPath (.sngl target) := .precise (.flow halias)
  have ht3 : PreciseTyping3 G target V := .precise htarget
  cases h with
  | precise h =>
      cases h with
      | allIntro L hbody =>
          cases hr with
          | allDom hr =>
              exact .all ∅ (.invertible (.precise (.allIntro L hbody)))
                (.snglPQ ha3 ht3 hr.swap) (fun _ _ => .refl)
          | allCod hr =>
              let L' := G.dom
              apply ReplacementVal.all L' (.invertible (.precise (.allIntro L hbody))) .refl
              intro y hy
              exact (TightSubtyp.snglQP
                (ha3.mono (.pushRight hy _) (Env.okPush hi.ok hy))
                (ht3.mono (.pushRight hy _) (Env.okPush hi.ok hy))
                (hr.openVar htarget.toGeneral.pathNamed halias.sourceNamed y)).toGeneral
      | newIntro L hdefs hself =>
          cases hr with
          | bnd hr =>
              exact .recQP halias htarget
                (.invertible (.precise (.newIntro L hdefs hself))) hr
  | recPQ hp hq h hr₀ =>
      cases hr with
      | bnd hr => exact .recQP halias htarget (.invertible (.recPQ hp hq h hr₀)) hr

theorem ReplacementVal.replacementQP {G : Ctx} {v : Val}
    {aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (h : ReplacementVal G v T)
    (halias : PreciseFlow G aliasPath (.sngl target) (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp target aliasPath T T') :
    ReplacementVal G v T' := by
  have ha3 : PreciseTyping3 G aliasPath (.sngl target) := .precise (.flow halias)
  have ht3 : PreciseTyping3 G target V := .precise htarget
  generalize heq : T = U at h
  induction h generalizing T T' with
  | invertible h =>
      cases heq
      exact h.replacementQP hi halias htarget hr
  | and h₁ h₂ ih₁ ih₂ =>
      cases heq
      cases hr with
      | andLeft hr => exact .and (ih₁ hr rfl) h₂
      | andRight hr => exact .and h₁ (ih₂ hr rfl)
  | sel h hf ih =>
      cases heq
      obtain ⟨fields, hsrc, rfl⟩ := hr.path_target
      have hcur := ReplacementVal.sel h hf
      rw [hsrc] at hcur hr
      exact .selQP halias htarget hcur hr
  | recQP hp hq h hr₀ ih =>
      cases heq
      cases hr with
      | bnd hr => exact .recQP halias htarget (.recQP hp hq h hr₀) hr
  | selQP hp hq h hr₀ ih =>
      cases heq
      obtain ⟨fields, hsrc, rfl⟩ := hr.path_target
      exact .selQP halias htarget (.selQP hp hq h hr₀) hr
  | top h ih =>
      cases heq
      cases hr
  | all L h hdom hbody ih =>
      cases heq
      cases hr with
      | allDom hr =>
          let L' := L ∪ G.dom
          apply ReplacementVal.all L' h
            (.trans (.snglPQ ha3 ht3 hr.swap) hdom)
          intro y hy
          simp only [L', Finset.mem_union, not_or] at hy
          exact (hbody y hy.1).narrow
            (Subenv.last (TightSubtyp.snglPQ ha3 ht3 hr.swap).toGeneral
              (Env.okPush hi.ok hy.2) (Env.okPush hi.ok hy.2))
      | allCod hr =>
          let L' := L ∪ G.dom
          apply ReplacementVal.all L' h hdom
          intro y hy
          simp only [L', Finset.mem_union, not_or] at hy
          exact .trans (hbody y hy.1)
            (TightSubtyp.snglQP
              (ha3.mono (.pushRight hy.2 _) (Env.okPush hi.ok hy.2))
              (ht3.mono (.pushRight hy.2 _) (Env.okPush hi.ok hy.2))
              (hr.openVar htarget.toGeneral.pathNamed halias.sourceNamed y)).toGeneral

theorem ReplacementVal.replacementQP2 {G : Ctx} {v : Val}
    {aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (h : ReplacementVal G v T) (halias : PreciseTyping2 G aliasPath (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp target aliasPath T T') :
    ReplacementVal G v T' := by
  generalize heq : Typ.sngl target = U at halias
  induction halias generalizing target T T' V with
  | flow halias =>
      cases heq
      have hsource := halias.snglSource_eq hi
      subst hsource
      exact h.replacementQP hi halias htarget hr
  | snglTrans hp hfield ihp ihfield =>
      cases heq
      obtain ⟨V', htarget'⟩ := htarget.backtrack
      exact ihp h htarget' hr.fieldElim rfl

theorem ReplacementVal.replacementQP3 {G : Ctx} {v : Val}
    {aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (h : ReplacementVal G v T) (halias : PreciseTyping3 G aliasPath (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp target aliasPath T T') :
    ReplacementVal G v T' := by
  generalize heq : Typ.sngl target = U at halias
  induction halias generalizing target T T' V with
  | precise halias =>
      cases heq
      exact h.replacementQP2 hi halias htarget hr
  | snglTrans hp hrest ih =>
      obtain ⟨W, hr₁, hr₂⟩ := hr.insert _
      obtain ⟨V', hmiddle⟩ := hrest.precise2Exists
      have hmid := ih h htarget hr₁ heq
      exact hmid.replacementQP2 hi hp hmiddle hr₂

theorem InvertibleVal.replacementPQ {G : Ctx} {v : Val}
    {aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (h : InvertibleVal G v T)
    (halias : PreciseFlow G aliasPath (.sngl target) (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp aliasPath target T T') :
    ReplacementVal G v T' := by
  have ha3 : PreciseTyping3 G aliasPath (.sngl target) := .precise (.flow halias)
  have ht3 : PreciseTyping3 G target V := .precise htarget
  cases h with
  | precise h =>
      cases h with
      | allIntro L hbody =>
          cases hr with
          | allDom hr =>
              exact .all ∅ (.invertible (.precise (.allIntro L hbody)))
                (.snglQP ha3 ht3 hr.swap) (fun _ _ => .refl)
          | allCod hr =>
              let L' := G.dom
              apply ReplacementVal.all L' (.invertible (.precise (.allIntro L hbody))) .refl
              intro y hy
              exact (TightSubtyp.snglPQ
                (ha3.mono (.pushRight hy _) (Env.okPush hi.ok hy))
                (ht3.mono (.pushRight hy _) (Env.okPush hi.ok hy))
                (hr.openVar halias.sourceNamed htarget.toGeneral.pathNamed y)).toGeneral
      | newIntro L hdefs hself =>
          cases hr with
          | bnd hr =>
              exact .invertible
                (.recPQ halias htarget (.precise (.newIntro L hdefs hself)) hr)
  | recPQ hp hq h hr₀ =>
      cases hr with
      | bnd hr => exact .invertible (.recPQ halias htarget (.recPQ hp hq h hr₀) hr)

theorem ReplacementVal.replacementPQ {G : Ctx} {v : Val}
    {aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (h : ReplacementVal G v T)
    (halias : PreciseFlow G aliasPath (.sngl target) (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp aliasPath target T T') :
    ReplacementVal G v T' := by
  have ha3 : PreciseTyping3 G aliasPath (.sngl target) := .precise (.flow halias)
  have ht3 : PreciseTyping3 G target V := .precise htarget
  generalize heq : T = U at h
  induction h generalizing T T' with
  | invertible h =>
      cases heq
      exact h.replacementPQ hi halias htarget hr
  | and h₁ h₂ ih₁ ih₂ =>
      cases heq
      cases hr with
      | andLeft hr => exact .and (ih₁ hr rfl) h₂
      | andRight hr => exact .and h₁ (ih₂ hr rfl)
  | sel h hf ih =>
      cases heq
      obtain ⟨fields, hsrc, hdst⟩ := hr.path_target
      rw [hsrc] at hf
      have hnil := halias.snglFieldsElim hi hf
      rw [hnil, Path.selectFields_nil] at hf
      have hsource := halias.source_unique hi hf
      obtain ⟨B, hB⟩ := hf.recordSource_bnd hi
      rw [hB, halias.snglSource_eq hi] at hsource
      cases hsource
  | recQP hp hq h hr₀ ih =>
      cases heq
      cases hr with
      | bnd hr =>
          rcases hr₀.commuteTyped hr hi hp halias with heq | ⟨W, hl, hr⟩
          · cases heq
            exact h
          · have hmid := ih (.bnd hl) rfl
            exact hmid.replacementQP hi hp hq (.bnd hr)
  | selQP hp hq h hr₀ ih =>
      cases heq
      rcases hr₀.commuteTyped hr hi hp halias with heq | ⟨W, hl, hr⟩
      · cases heq
        exact h
      · have hmid := ih hl rfl
        exact hmid.replacementQP hi hp hq hr
  | top h ih =>
      cases heq
      cases hr
  | all L h hdom hbody ih =>
      cases heq
      cases hr with
      | allDom hr =>
          let L' := L ∪ G.dom
          apply ReplacementVal.all L' h
            (.trans (.snglQP ha3 ht3 hr.swap) hdom)
          intro y hy
          simp only [L', Finset.mem_union, not_or] at hy
          exact (hbody y hy.1).narrow
            (Subenv.last (TightSubtyp.snglQP ha3 ht3 hr.swap).toGeneral
              (Env.okPush hi.ok hy.2) (Env.okPush hi.ok hy.2))
      | allCod hr =>
          let L' := L ∪ G.dom
          apply ReplacementVal.all L' h hdom
          intro y hy
          simp only [L', Finset.mem_union, not_or] at hy
          exact .trans (hbody y hy.1)
            (TightSubtyp.snglPQ
              (ha3.mono (.pushRight hy.2 _) (Env.okPush hi.ok hy.2))
              (ht3.mono (.pushRight hy.2 _) (Env.okPush hi.ok hy.2))
              (hr.openVar halias.sourceNamed htarget.toGeneral.pathNamed y)).toGeneral

theorem ReplacementVal.replacementPQ2 {G : Ctx} {v : Val}
    {aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (h : ReplacementVal G v T) (halias : PreciseTyping2 G aliasPath (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp aliasPath target T T') :
    ReplacementVal G v T' := by
  generalize heq : Typ.sngl target = U at halias
  induction halias generalizing target T T' V with
  | flow halias =>
      cases heq
      have hsource := halias.snglSource_eq hi
      subst hsource
      exact h.replacementPQ hi halias htarget hr
  | snglTrans hp hfield ihp ihfield =>
      cases heq
      obtain ⟨V', htarget'⟩ := htarget.backtrack
      exact ihp h htarget' hr.fieldElim rfl

theorem ReplacementVal.replacementPQ3 {G : Ctx} {v : Val}
    {aliasPath target : Path} {T T' V : Typ} (hi : Inert G)
    (h : ReplacementVal G v T) (halias : PreciseTyping3 G aliasPath (.sngl target))
    (htarget : PreciseTyping2 G target V) (hr : ReplTyp aliasPath target T T') :
    ReplacementVal G v T' := by
  generalize heq : Typ.sngl target = U at halias
  induction halias generalizing target T T' V with
  | precise halias =>
      cases heq
      exact h.replacementPQ2 hi halias htarget hr
  | snglTrans hp hrest ih =>
      obtain ⟨W, hr₁, hr₂⟩ := hr.insert _
      obtain ⟨V', hmiddle⟩ := hrest.precise2Exists
      have hmid := h.replacementPQ2 hi hp hmiddle hr₁
      exact ih hmid htarget hr₂ heq

theorem ReplacementVal.pathSelIntro {G : Ctx} {v : Val} {p : Path}
    {A : Signature.TypLabel} {T : Typ} (hi : Inert G)
    (hp : PreciseTyping3 G p (.rcd (.typ A T T)))
    (h : ReplacementVal G v T) : ReplacementVal G v (.path p A) := by
  generalize heq : Typ.rcd (Dec.typ A T T) = U at hp
  induction hp generalizing A T with
  | precise hp =>
      cases heq
      cases hp with
      | flow hp => exact .sel h hp
  | snglTrans hs hp ih =>
      have hq := ih h heq
      obtain ⟨V, htarget⟩ := hp.precise2Exists
      exact hq.replacementQP2 hi hs htarget (.pathRoot _ _ A)

theorem ReplacementVal.pathSel {G : Ctx} {v : Val} {p : Path}
    {A : Signature.TypLabel} {T : Typ} (hi : Inert G)
    (hp : PreciseTyping3 G p (.rcd (.typ A T T)))
    (h : ReplacementVal G v (.path p A)) : ReplacementVal G v T := by
  generalize heq : Typ.path p A = U at h
  induction h generalizing p A T with
  | invertible h =>
      cases heq
      cases h with
      | precise h => cases h
  | and h₁ h₂ ih₁ ih₂ => cases heq
  | sel h hf ih =>
      cases heq
      have heqT := hp.decTypTarget_unique hi (.precise (.flow hf))
      cases heqT
      exact h
  | recQP hs ht h hr ih => cases heq
  | selQP hs ht h hr ih =>
      obtain ⟨fields, rfl, rfl⟩ := hr.path_prefixes
      cases heq
      have hsfield := (PreciseTyping3.precise (.flow hs)).fieldTransSnglFromLeft hi hp
      have hp' := hp.invertSngl_record hi
        (by exact ⟨_, .one .typ rfl⟩) hsfield
      exact ih hp' rfl
  | top h ih => cases heq
  | all L h hdom hbody ih => cases heq

theorem InvertibleVal.bot_false {G : Ctx} {v : Val}
    (h : InvertibleVal G v .bot) : False := by
  cases h with
  | precise h => cases h

theorem ReplacementVal.bot_false {G : Ctx} {v : Val}
    (h : ReplacementVal G v .bot) : False := by
  cases h with
  | invertible h => exact h.bot_false

theorem ReplacementVal.rcd_false {G : Ctx} {v : Val} {D : Dec}
    (h : ReplacementVal G v (.rcd D)) : False := by
  cases h with
  | invertible h =>
      cases h with
      | precise h => cases h

theorem ReplacementVal.subtyp {G : Ctx} {v : Val} {T U : Typ}
    (hi : Inert G) (h : ReplacementVal G v T)
    (hs : TightSubtyp G T U) : ReplacementVal G v U := by
  apply TightSubtyp.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun G T U _ => Inert G → ∀ {v},
      ReplacementVal G v T → ReplacementVal G v U)
  case var => intros; trivial
  case allIntro => intros; trivial
  case allElim => intros; trivial
  case newIntro => intros; trivial
  case newElim => intros; trivial
  case rcdIntro => intros; trivial
  case letE => intros; trivial
  case caseE => intros; trivial
  case sngl => intros; trivial
  case self => intros; trivial
  case pathElim => intros; trivial
  case recIntro => intros; trivial
  case recElim => intros; trivial
  case andIntro => intros; trivial
  case sub => intros; trivial
  case top => intros; exact .top ‹ReplacementVal _ _ _›
  case bot =>
    intro G T hi v h
    exact False.elim h.bot_false
  case refl => intros; assumption
  case trans =>
    intro G S T U h₁ h₂ ih₁ ih₂ hi v h
    exact ih₂ hi (ih₁ hi h)
  case andLeft => intros; exact (‹ReplacementVal _ _ _›).andParts.1
  case andRight => intros; exact (‹ReplacementVal _ _ _›).andParts.2
  case andIntro =>
    intro G S T U h₁ h₂ ih₁ ih₂ hi v h
    exact .and (ih₁ hi h) (ih₂ hi h)
  case fld =>
    intro G T U a hs ih hi v h
    exact False.elim h.rcd_false
  case typ =>
    intro G S₂ S₁ T₁ T₂ A hLo hHi ihLo ihHi hi v h
    exact False.elim h.rcd_false
  case snglPQ =>
    intro G aliasPath target V T T' hp hq hr hi v h
    obtain ⟨W, hq₂⟩ := hq.precise2Exists
    exact h.replacementPQ3 hi hp hq₂ hr
  case snglQP =>
    intro G aliasPath target V T T' hp hq hr hi v h
    obtain ⟨W, hq₂⟩ := hq.precise2Exists
    exact h.replacementQP3 hi hp hq₂ hr
  case selLo =>
    intro G p A T hp hi v h
    exact h.pathSelIntro hi hp
  case selHi =>
    intro G p A T hp hi v h
    exact h.pathSel hi hp
  case all =>
    intro G S₂ S₁ T₁ T₂ L hdom hbody ih hi v h
    exact .all L h hdom hbody
  case t => exact hs
  all_goals assumption

theorem TightTyped.valReplacement {G : Ctx} {v : Val} {T : Typ}
    (hi : Inert G) (h : TightTyped G (.val v) T) : ReplacementVal G v T := by
  apply TightTyped.rec
    (motive_1 := fun G t T _ => Inert G → ∀ v,
      t = .val v → ReplacementVal G v T)
    (motive_2 := fun _ _ _ _ => True)
  case var => intros; contradiction
  case allIntro =>
    intro G S t U L hbody hi v heq
    cases heq
    exact .invertible (.precise (.allIntro L hbody))
  case allElim => intros; contradiction
  case newIntro =>
    intro p A G T ds L hdefs hself hi v heq
    cases heq
    exact .invertible (.precise (.newIntro L hdefs hself))
  case newElim => intros; contradiction
  case rcdIntro => intros; contradiction
  case letE => intros; contradiction
  case caseE => intros; contradiction
  case sngl => intros; contradiction
  case self => intros; contradiction
  case pathElim => intros; contradiction
  case recIntro => intros; contradiction
  case recElim => intros; contradiction
  case andIntro =>
    intro G p T U h₁ h₂ ih₁ ih₂ hi v heq
    exact .and (ih₁ hi v heq) (ih₂ hi v heq)
  case sub =>
    intro G t S T ht hs iht ihs hi v heq
    exact (iht hi v heq).subtyp hi hs
  case top => intros; trivial
  case bot => intros; trivial
  case refl => intros; trivial
  case trans => intros; trivial
  case andLeft => intros; trivial
  case andRight => intros; trivial
  case andIntro => intros; trivial
  case fld => intros; trivial
  case typ => intros; trivial
  case snglPQ => intros; trivial
  case snglQP => intros; trivial
  case selLo => intros; trivial
  case selHi => intros; trivial
  case all => intros; trivial
  case t => exact h
  all_goals first | assumption | rfl

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

theorem ReplComposition.openPath {G : Ctx} {T U : Typ}
    (h : ReplComposition G T U) (r : Path) :
    ReplComposition G (T.openPath r) (U.openPath r) := by
  induction h with
  | refl => exact .refl _
  | step hstep hrest ih =>
      obtain ⟨p, q, W, hp, hq, hr⟩ := hstep
      have hpNamed := hp.sourceNamed
      have hqNamed := hq.toGeneral.pathNamed
      exact (Star.one ⟨p, q, W, hp, hq,
        hr.openPath hqNamed hpNamed r⟩).trans ih

theorem Star.replToComposition {G : Ctx} {p q : Path} {W T U : Typ}
    (h : Star (ReplTyp q p) T U)
    (hp : PreciseFlow G p (.sngl q) (.sngl q))
    (hq : PreciseTyping2 G q W) : ReplComposition G T U := by
  induction h with
  | refl => exact .refl _
  | step hr hrest ih => exact .step ⟨p, q, W, hp, hq, hr⟩ ih

theorem ReplComposition.recordHasBackward {G : Ctx} {T U : Typ}
    {a : Signature.TrmLabel} {V : Typ} (h : ReplComposition G T U)
    (hhas : RecordHas U (.trm a V)) :
    ∃ V', RecordHas T (.trm a V') ∧ ReplComposition G V' V := by
  induction h generalizing V with
  | refl => exact ⟨V, hhas, .refl V⟩
  | step hstep hrest ih =>
      obtain ⟨p, q, W, hp, hq, hr⟩ := hstep
      obtain ⟨Vmid, hmid, hmidV⟩ := ih hhas
      obtain ⟨Vsrc, hsrc, hsrcMid⟩ := hr.recordHasBackward hmid
      exact ⟨Vsrc, hsrc,
        (hsrcMid.replToComposition hp hq).trans hmidV⟩

theorem ReplComposition.recordHasForward {G : Ctx} {T U : Typ}
    {a : Signature.TrmLabel} {V : Typ} (h : ReplComposition G T U)
    (hhas : RecordHas T (.trm a V)) :
    ∃ V', RecordHas U (.trm a V') ∧ ReplComposition G V V' := by
  induction h generalizing V with
  | refl => exact ⟨V, hhas, .refl V⟩
  | step hstep hrest ih =>
      obtain ⟨p, q, W, hp, hq, hr⟩ := hstep
      obtain ⟨Vmid, hmid, hVMid⟩ := hr.recordHasForward hhas
      obtain ⟨Vdst, hdst, hmidDst⟩ := ih hmid
      exact ⟨Vdst, hdst,
        (hVMid.replToComposition hp hq).trans hmidDst⟩

/-- Two types obtained from a common type by typed path replacement.  This is
the symmetric replacement relation used by object canonical forms. -/
def CommonRepl (G : Ctx) (T U : Typ) : Prop :=
  ∃ W, ReplComposition G W T ∧ ReplComposition G W U

theorem CommonRepl.refl {G : Ctx} (T : Typ) : CommonRepl G T T :=
  ⟨T, .refl T, .refl T⟩

theorem CommonRepl.symm {G : Ctx} {T U : Typ}
    (h : CommonRepl G T U) : CommonRepl G U T := by
  obtain ⟨W, hT, hU⟩ := h
  exact ⟨W, hU, hT⟩

theorem CommonRepl.openPath {G : Ctx} {T U : Typ}
    (h : CommonRepl G T U) (p : Path) :
    CommonRepl G (T.openPath p) (U.openPath p) := by
  obtain ⟨W, hT, hU⟩ := h
  exact ⟨W.openPath p, hT.openPath p, hU.openPath p⟩

theorem ReplComposition.mono {G G' : Ctx} {T U : Typ}
    (h : ReplComposition G T U) (he : Env.Extends G G') (hok : Env.Ok G') :
    ReplComposition G' T U := by
  induction h with
  | refl => exact .refl _
  | step hstep hrest ih =>
      obtain ⟨p, q, W, hp, hq, hr⟩ := hstep
      exact .step ⟨p, q, W, hp.mono he hok, hq.mono he hok, hr⟩ ih

theorem CommonRepl.mono {G G' : Ctx} {T U : Typ}
    (h : CommonRepl G T U) (he : Env.Extends G G') (hok : Env.Ok G') :
    CommonRepl G' T U := by
  obtain ⟨W, hT, hU⟩ := h
  exact ⟨W, hT.mono he hok, hU.mono he hok⟩

theorem CommonRepl.bnd {G : Ctx} {T U : Typ}
    (h : CommonRepl G T U) : CommonRepl G (.bnd T) (.bnd U) := by
  obtain ⟨W, hT, hU⟩ := h
  exact ⟨.bnd W, hT.bndMap, hU.bndMap⟩

theorem CommonRepl.leftBnd {G : Ctx} {T U : Typ}
    (h : CommonRepl G (.bnd T) U) :
    ∃ U', U = .bnd U' ∧ CommonRepl G T U' := by
  obtain ⟨W, hWT, hWU⟩ := h
  obtain ⟨W', rfl, hW'T⟩ := hWT.targetBnd
  obtain ⟨U', rfl, hW'U'⟩ := hWU.sourceBnd
  exact ⟨U', rfl, W', hW'T, hW'U'⟩

theorem CommonRepl.rightBnd {G : Ctx} {T U : Typ}
    (h : CommonRepl G T (.bnd U)) :
    ∃ T', T = .bnd T' ∧ CommonRepl G T' U := by
  obtain ⟨T', heq, hc⟩ := h.symm.leftBnd
  exact ⟨T', heq, hc.symm⟩

theorem CommonRepl.rightSngl {G : Ctx} {T : Typ} {q : Path}
    (h : CommonRepl G T (.sngl q)) : ∃ p, T = .sngl p := by
  obtain ⟨W, hWT, hWq⟩ := h
  obtain ⟨r, hW⟩ := hWq.targetSngl
  subst W
  exact hWT.sourceSngl

theorem CommonRepl.snglAliases {G : Ctx} {p q : Path} {P Q : Typ}
    (h : CommonRepl G (.sngl p) (.sngl q))
    (hi : Inert G) (hwf : Wf G)
    (hp : PreciseTyping3 G p P) (hq : PreciseTyping3 G q Q) :
    ∃ r,
      (r = p ∨ PreciseTyping3 G p (.sngl r)) ∧
      (r = q ∨ PreciseTyping3 G q (.sngl r)) := by
  obtain ⟨W, hWp, hWq⟩ := h
  obtain ⟨r, hW⟩ := hWp.targetSngl
  subst W
  obtain ⟨p', hpEq, hpathsP⟩ := hWp.sourceSnglPaths
  obtain ⟨q', hqEq, hpathsQ⟩ := hWq.sourceSnglPaths
  have hpPath : p' = p := (Typ.sngl.inj hpEq).symm
  have hqPath : q' = q := (Typ.sngl.inj hqEq).symm
  subst p'
  subst q'
  obtain ⟨_, hpRel⟩ := hpathsP.transportBackward hi hwf hp
  obtain ⟨_, hqRel⟩ := hpathsQ.transportBackward hi hwf hq
  exact ⟨r, hpRel, hqRel⟩

theorem CommonRepl.rightAll {G : Ctx} {T S U : Typ}
    (h : CommonRepl G T (.all S U)) :
    ∃ S' U', T = .all S' U' := by
  obtain ⟨W, hWT, hWall⟩ := h
  obtain ⟨S₀, U₀, hW⟩ := hWall.targetAll
  subst W
  exact hWT.sourceAll

theorem CommonRepl.subtypes {G : Ctx} {T U : Typ}
    (h : CommonRepl G T U) :
    Subtyp G T U ∧ Subtyp G U T := by
  obtain ⟨W, hT, hU⟩ := h
  have hTW := hT.subtypes.2.toGeneral
  have hWU := hU.subtypes.1.toGeneral
  have hUW := hU.subtypes.2.toGeneral
  have hWT := hT.subtypes.1.toGeneral
  exact ⟨.trans hTW hWU, .trans hUW hWT⟩

theorem CommonRepl.recordHas {G : Ctx} {T U : Typ}
    {a : Signature.TrmLabel} {V : Typ} (h : CommonRepl G T U)
    (hhas : RecordHas T (.trm a V)) :
    ∃ V', RecordHas U (.trm a V') ∧ CommonRepl G V V' := by
  obtain ⟨W, hWT, hWU⟩ := h
  obtain ⟨V₀, hV₀, hV₀V⟩ := hWT.recordHasBackward hhas
  obtain ⟨V', hV', hV₀V'⟩ := hWU.recordHasForward hV₀
  exact ⟨V', hV', ⟨V₀, hV₀V, hV₀V'⟩⟩

end CDot
