import CDot.PreciseTyping
import CDot.Replacement

/-!
# Tight typing

Lean port of `cdot/TightTyping.v`.  Tight typing differs from general typing at
type selections and singleton replacement: those rules require third-level
precise typing.  Premises beneath binders deliberately remain general.
-/

namespace CDot

variable [Signature]

set_option autoImplicit true in
mutual
  inductive TightTyped : Ctx → Trm → Typ → Prop where
    | var : Env.Binds x T G → TightTyped G (.var x) T
    | allIntro (L : Vars) :
        (∀ x, x ∉ L → Typed (G.push x T) (t.open x) (U.open x)) →
        TightTyped G (.val (.lambda T t)) (.all T U)
    | allElim : TightTyped G (.path p) (.all S T) →
        TightTyped G (.path q) S →
        TightTyped G (.app p q) (T.openPath q)
    | newIntro (L : Vars) :
        (∀ z, z ∉ L →
          TypedDefs z [] (G.push z (T.open z)) (ds.open z) (T.open z)) →
        (∀ z, z ∉ L →
          Typed (G.push z (T.open z)) (.path (.var z))
            ((.path p A : Typ).open z)) →
        TightTyped G (.val (.new p A T ds)) (.bnd T)
    | newElim : TightTyped G (.path p) (.rcd (.trm a T)) →
        TightTyped G (.path (p.selectField a)) T
    | rcdIntro : TightTyped G (.path (p.selectField a)) T →
        TightTyped G (.path p) (.rcd (.trm a T))
    | letE (L : Vars) : TightTyped G t T →
        (∀ x, x ∉ L → Typed (G.push x T) (u.open x) U) →
        TightTyped G (.letE t u) U
    | caseE (L : Vars) : TightTyped G (.path p) S →
        TightTyped G (.path q) U →
        (∀ y, y ∉ L →
          Typed (G.push y (.and (.sngl p) (.path q A))) (t₁.open y) T) →
        TightTyped G t₂ T → TightTyped G (.caseE p q A t₁ t₂) T
    | sngl : TightTyped G (.path p) (.sngl q) →
        TightTyped G (.path q) T → TightTyped G (.path p) T
    | self : TightTyped G (.path p) T → TightTyped G (.path p) (.sngl p)
    | pathElim : TightTyped G (.path p) (.sngl q) →
        TightTyped G (.path (q.selectField a)) T →
        TightTyped G (.path (p.selectField a)) (.sngl (q.selectField a))
    | recIntro : TightTyped G (.path p) (T.openPath p) →
        TightTyped G (.path p) (.bnd T)
    | recElim : TightTyped G (.path p) (.bnd T) →
        TightTyped G (.path p) (T.openPath p)
    | andIntro : TightTyped G (.path p) T → TightTyped G (.path p) U →
        TightTyped G (.path p) (.and T U)
    | sub : TightTyped G t T → TightSubtyp G T U → TightTyped G t U

  inductive TightSubtyp : Ctx → Typ → Typ → Prop where
    | top : TightSubtyp G T .top
    | bot : TightSubtyp G .bot T
    | refl : TightSubtyp G T T
    | trans : TightSubtyp G S T → TightSubtyp G T U → TightSubtyp G S U
    | andLeft : TightSubtyp G (.and T U) T
    | andRight : TightSubtyp G (.and T U) U
    | andIntro : TightSubtyp G S T → TightSubtyp G S U →
        TightSubtyp G S (.and T U)
    | fld : TightSubtyp G T U →
        TightSubtyp G (.rcd (.trm a T)) (.rcd (.trm a U))
    | typ : TightSubtyp G S₂ S₁ → TightSubtyp G T₁ T₂ →
        TightSubtyp G (.rcd (.typ A S₁ T₁)) (.rcd (.typ A S₂ T₂))
    | snglPQ : PreciseTyping3 G p (.sngl q) → PreciseTyping3 G q U →
        ReplTyp p q T T' → TightSubtyp G T T'
    | snglQP : PreciseTyping3 G p (.sngl q) → PreciseTyping3 G q U →
        ReplTyp q p T T' → TightSubtyp G T T'
    | selLo : PreciseTyping3 G p (.rcd (.typ A T T)) →
        TightSubtyp G T (.path p A)
    | selHi : PreciseTyping3 G p (.rcd (.typ A T T)) →
        TightSubtyp G (.path p A) T
    | all (L : Vars) : TightSubtyp G S₂ S₁ →
        (∀ x, x ∉ L → Subtyp (G.push x S₂) (T₁.open x) (T₂.open x)) →
        TightSubtyp G (.all S₁ T₁) (.all S₂ T₂)
end

theorem TightSubtyp.toGeneral {G : Ctx} {T U : Typ}
    (h : TightSubtyp G T U) : Subtyp G T U := by
  apply TightSubtyp.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun G T U _ => Subtyp G T U)
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
  case top => intros; exact .top
  case bot => intros; exact .bot
  case refl => intros; exact .refl
  case trans =>
    intro G S T U h₁ h₂ ih₁ ih₂
    exact .trans ih₁ ih₂
  case andLeft => intros; exact .andLeft
  case andRight => intros; exact .andRight
  case andIntro =>
    intro G S T U h₁ h₂ ih₁ ih₂
    exact .andIntro ih₁ ih₂
  case fld =>
    intro G T U a h ih
    exact .fld ih
  case typ =>
    intro G S₂ S₁ T₁ T₂ A h₁ h₂ ih₁ ih₂
    exact .typ ih₁ ih₂
  case snglPQ =>
    intro G p q U T T' hp hq hr
    exact .snglPQ hp.toGeneral hq.toGeneral hr
  case snglQP =>
    intro G p q U T T' hp hq hr
    exact .snglQP hp.toGeneral hq.toGeneral hr
  case selLo =>
    intro G p A T hp
    exact .selLo hp.toGeneral
  case selHi =>
    intro G p A T hp
    exact .selHi hp.toGeneral
  case all =>
    intro G S₂ S₁ T₁ T₂ L hdom hbody ih
    exact .all L ih hbody
  case t => exact h

theorem TightTyped.toGeneral {G : Ctx} {t : Trm} {T : Typ}
    (h : TightTyped G t T) : Typed G t T := by
  apply TightTyped.rec
    (motive_1 := fun G t T _ => Typed G t T)
    (motive_2 := fun _ _ _ _ => True)
  case var =>
    intro x T G hb
    exact .var hb
  case allIntro =>
    intro G T t U L h
    exact .allIntro L h
  case allElim =>
    intro G p S T q h₁ h₂ ih₁ ih₂
    exact .allElim ih₁ ih₂
  case newIntro =>
    intro p A G T ds L hdefs hself
    exact .newIntro L hdefs hself
  case newElim =>
    intro G p a T h ih
    exact .newElim ih
  case rcdIntro =>
    intro G T p a h ih
    exact .rcdIntro ih
  case letE =>
    intro G t T U u L ht hbody ih
    exact .letE L ih hbody
  case caseE =>
    intro G p S q U A T t₂ t₁ L hp hq hbody ht₂ ihp ihq iht₂
    exact .caseE L ihp ihq hbody iht₂
  case sngl =>
    intro G p q T h₁ h₂ ih₁ ih₂
    exact .sngl ih₁ ih₂
  case self =>
    intro G p T h ih
    exact .self ih
  case pathElim =>
    intro G p q a T h₁ h₂ ih₁ ih₂
    exact .pathElim ih₁ ih₂
  case recIntro =>
    intro G p T h ih
    exact .recIntro ih
  case recElim =>
    intro G p T h ih
    exact .recElim ih
  case andIntro =>
    intro G p T U h₁ h₂ ih₁ ih₂
    exact .andIntro ih₁ ih₂
  case sub =>
    intro G t T U ht hs iht _
    exact .sub iht hs.toGeneral
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

end CDot
