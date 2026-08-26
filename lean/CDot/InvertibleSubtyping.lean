import CDot.Narrowing
import CDot.InvertibleTyping

/-!
# Invertible (semantic) subtyping

This transitivity-free presentation pushes intersection elimination and path
replacement into the derivation.  It is the relation called `subtyp_s` in the
Coq development.
-/

namespace CDot

variable [Signature]

inductive SemanticSubtyp : Ctx → Typ → Typ → Prop where
  | top : SemanticSubtyp G T .top
  | bot : SemanticSubtyp G .bot T
  | refl : SemanticSubtyp G T T
  | andLeft : SemanticSubtyp G T S → SemanticSubtyp G (.and T U) S
  | andRight : SemanticSubtyp G U S → SemanticSubtyp G (.and T U) S
  | andIntro : SemanticSubtyp G S T → SemanticSubtyp G S U →
      SemanticSubtyp G S (.and T U)
  | fld : SemanticSubtyp G T U →
      SemanticSubtyp G (.rcd (.trm a T)) (.rcd (.trm a U))
  | typ : TightSubtyp G S₂ S₁ → TightSubtyp G T₁ T₂ →
      SemanticSubtyp G (.rcd (.typ A S₁ T₁)) (.rcd (.typ A S₂ T₂))
  | snglPQRight : PreciseTyping3 G p (.sngl q) → PreciseTyping3 G q U →
      ReplTyp p q T T' → SemanticSubtyp G S T → SemanticSubtyp G S T'
  | snglQPRight : PreciseTyping3 G p (.sngl q) → PreciseTyping3 G q U →
      ReplTyp q p T T' → SemanticSubtyp G S T → SemanticSubtyp G S T'
  | snglPQLeft : PreciseTyping3 G p (.sngl q) → PreciseTyping3 G q U →
      ReplTyp p q S S' → SemanticSubtyp G S T → SemanticSubtyp G S' T
  | snglQPLeft : PreciseTyping3 G p (.sngl q) → PreciseTyping3 G q U →
      ReplTyp q p S S' → SemanticSubtyp G S T → SemanticSubtyp G S' T
  | selRight : PreciseTyping3 G p (.rcd (.typ A T T)) →
      SemanticSubtyp G S T → SemanticSubtyp G S (.path p A)
  | selLeft : PreciseTyping3 G p (.rcd (.typ A T T)) →
      SemanticSubtyp G T S → SemanticSubtyp G (.path p A) S
  | all (L : Vars) : TightSubtyp G S₂ S₁ →
      (∀ x, x ∉ L → Subtyp (G.push x S₂) (T₁.open x) (T₂.open x)) →
      SemanticSubtyp G (.all S₁ T₁) (.all S₂ T₂)

theorem SemanticSubtyp.toTight {G : Ctx} {S T : Typ}
    (h : SemanticSubtyp G S T) : TightSubtyp G S T := by
  induction h with
  | top => exact .top
  | bot => exact .bot
  | refl => exact .refl
  | andLeft _ ih => exact .trans .andLeft ih
  | andRight _ ih => exact .trans .andRight ih
  | andIntro _ _ ih₁ ih₂ => exact .andIntro ih₁ ih₂
  | fld _ ih => exact .fld ih
  | typ h₁ h₂ => exact .typ h₁ h₂
  | snglPQRight hp hq hr _ ih => exact .trans ih (.snglPQ hp hq hr)
  | snglQPRight hp hq hr _ ih => exact .trans ih (.snglQP hp hq hr)
  | snglPQLeft hp hq hr _ ih => exact .trans (.snglQP hp hq hr.swap) ih
  | snglQPLeft hp hq hr _ ih => exact .trans (.snglPQ hp hq hr.swap) ih
  | selRight hp _ ih => exact .trans ih (.selLo hp)
  | selLeft hp _ ih => exact .trans (.selHi hp) ih
  | all L hdom hbody => exact .all L hdom hbody

theorem SemanticSubtyp.topLeft {G : Ctx} {T U : Typ}
    (h : SemanticSubtyp G .top T) : SemanticSubtyp G U T := by
  generalize heq : Typ.top = S at h
  induction h generalizing U with
  | top => exact .top
  | bot => cases heq
  | refl =>
      cases heq
      exact .top
  | andLeft h ih => cases heq
  | andRight h ih => cases heq
  | andIntro hT hU ihT ihU => exact .andIntro (ihT heq) (ihU heq)
  | fld h ih => cases heq
  | typ hLo hHi => cases heq
  | snglPQRight hp hq hr h ih =>
      exact .snglPQRight hp hq hr (ih heq)
  | snglQPRight hp hq hr h ih =>
      exact .snglQPRight hp hq hr (ih heq)
  | snglPQLeft hp hq hr h ih => cases hr <;> cases heq
  | snglQPLeft hp hq hr h ih => cases hr <;> cases heq
  | selRight hp h ih => exact .selRight hp (ih heq)
  | selLeft hp h ih => cases heq
  | all L hdom hbody => cases heq

end CDot
