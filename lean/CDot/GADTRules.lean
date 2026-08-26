import CDot.Substitution

/-! # Derived replacement rules used by inversion proofs -/

namespace CDot

variable [Signature]

theorem TightSubtyp.snglPQLeft {G : Ctx} {p q : Path} {S S' T U : Typ}
    (hp : PreciseTyping3 G p (.sngl q)) (hq : PreciseTyping3 G q U)
    (hst : TightSubtyp G S T) (hr : ReplTyp p q S S') :
    TightSubtyp G S' T :=
  .trans (.snglQP hp hq hr.swap) hst

theorem TightSubtyp.snglPQRight {G : Ctx} {p q : Path} {S T T' U : Typ}
    (hp : PreciseTyping3 G p (.sngl q)) (hq : PreciseTyping3 G q U)
    (hst : TightSubtyp G S T) (hr : ReplTyp p q T T') :
    TightSubtyp G S T' :=
  .trans hst (.snglPQ hp hq hr)

theorem TightSubtyp.snglQPLeft {G : Ctx} {p q : Path} {S S' T U : Typ}
    (hp : PreciseTyping3 G p (.sngl q)) (hq : PreciseTyping3 G q U)
    (hst : TightSubtyp G S T) (hr : ReplTyp q p S S') :
    TightSubtyp G S' T :=
  .trans (.snglPQ hp hq hr.swap) hst

theorem TightSubtyp.snglQPRight {G : Ctx} {p q : Path} {S T T' U : Typ}
    (hp : PreciseTyping3 G p (.sngl q)) (hq : PreciseTyping3 G q U)
    (hst : TightSubtyp G S T) (hr : ReplTyp q p T T') :
    TightSubtyp G S T' :=
  .trans hst (.snglQP hp hq hr)

/-! ## Inversion for semantic subtyping -/

theorem SemanticSubtyp.trmInvert {G : Ctx} {a : Signature.TrmLabel}
    {T U : Typ}
    (h : SemanticSubtyp G (.rcd (.trm a T)) (.rcd (.trm a U))) :
    SemanticSubtyp G T U := by
  generalize hsrc : Typ.rcd (Dec.trm a T) = S at h
  generalize hdst : Typ.rcd (Dec.trm a U) = V at h
  induction h generalizing T U with
  | top => cases hdst
  | bot => cases hsrc
  | refl =>
      cases hsrc
      cases hdst
      exact .refl
  | andLeft h ih => cases hsrc
  | andRight h ih => cases hsrc
  | andIntro h₁ h₂ ih₁ ih₂ => cases hdst
  | fld h ih =>
      cases hsrc
      cases hdst
      exact h
  | typ hLo hHi => cases hsrc
  | snglPQRight hp hq hr h ih =>
      cases hr with
      | rcd hr =>
          cases hr with
          | trm hr =>
              cases hdst
              exact .snglPQRight hp hq hr (ih hsrc rfl)
          | typLo hr => cases hdst
          | typHi hr => cases hdst
      | andLeft hr => cases hdst
      | andRight hr => cases hdst
      | path => cases hdst
      | bnd hr => cases hdst
      | allDom hr => cases hdst
      | allCod hr => cases hdst
      | sngl => cases hdst
  | snglQPRight hp hq hr h ih =>
      cases hr with
      | rcd hr =>
          cases hr with
          | trm hr =>
              cases hdst
              exact .snglQPRight hp hq hr (ih hsrc rfl)
          | typLo hr => cases hdst
          | typHi hr => cases hdst
      | andLeft hr => cases hdst
      | andRight hr => cases hdst
      | path => cases hdst
      | bnd hr => cases hdst
      | allDom hr => cases hdst
      | allCod hr => cases hdst
      | sngl => cases hdst
  | snglPQLeft hp hq hr h ih =>
      cases hr with
      | rcd hr =>
          cases hr with
          | trm hr =>
              cases hsrc
              exact .snglPQLeft hp hq hr (ih rfl hdst)
          | typLo hr => cases hsrc
          | typHi hr => cases hsrc
      | andLeft hr => cases hsrc
      | andRight hr => cases hsrc
      | path => cases hsrc
      | bnd hr => cases hsrc
      | allDom hr => cases hsrc
      | allCod hr => cases hsrc
      | sngl => cases hsrc
  | snglQPLeft hp hq hr h ih =>
      cases hr with
      | rcd hr =>
          cases hr with
          | trm hr =>
              cases hsrc
              exact .snglQPLeft hp hq hr (ih rfl hdst)
          | typLo hr => cases hsrc
          | typHi hr => cases hsrc
      | andLeft hr => cases hsrc
      | andRight hr => cases hsrc
      | path => cases hsrc
      | bnd hr => cases hsrc
      | allDom hr => cases hsrc
      | allCod hr => cases hsrc
      | sngl => cases hsrc
  | selRight hp h ih => cases hdst
  | selLeft hp h ih => cases hsrc
  | all L hdom hbody => cases hsrc

theorem SemanticSubtyp.typInvert {G : Ctx} {A : Signature.TypLabel}
    {S₁ T₁ S₂ T₂ : Typ}
    (h : SemanticSubtyp G (.rcd (.typ A S₁ T₁))
      (.rcd (.typ A S₂ T₂))) :
    TightSubtyp G S₂ S₁ ∧ TightSubtyp G T₁ T₂ := by
  generalize hsrc : Typ.rcd (Dec.typ A S₁ T₁) = S at h
  generalize hdst : Typ.rcd (Dec.typ A S₂ T₂) = V at h
  induction h generalizing S₁ T₁ S₂ T₂ with
  | top => cases hdst
  | bot => cases hsrc
  | refl =>
      cases hsrc
      cases hdst
      exact ⟨.refl, .refl⟩
  | andLeft h ih => cases hsrc
  | andRight h ih => cases hsrc
  | andIntro h₁ h₂ ih₁ ih₂ => cases hdst
  | fld h ih => cases hsrc
  | typ hLo hHi =>
      cases hsrc
      cases hdst
      exact ⟨hLo, hHi⟩
  | snglPQRight hp hq hr h ih =>
      cases hr with
      | rcd hr =>
          cases hr with
          | typLo hr =>
              cases hdst
              obtain ⟨hLo, hHi⟩ := ih hsrc rfl
              exact ⟨.snglPQLeft hp hq hLo hr, hHi⟩
          | typHi hr =>
              cases hdst
              obtain ⟨hLo, hHi⟩ := ih hsrc rfl
              exact ⟨hLo, .snglPQRight hp hq hHi hr⟩
          | trm hr => cases hdst
      | andLeft hr => cases hdst
      | andRight hr => cases hdst
      | path => cases hdst
      | bnd hr => cases hdst
      | allDom hr => cases hdst
      | allCod hr => cases hdst
      | sngl => cases hdst
  | snglQPRight hp hq hr h ih =>
      cases hr with
      | rcd hr =>
          cases hr with
          | typLo hr =>
              cases hdst
              obtain ⟨hLo, hHi⟩ := ih hsrc rfl
              exact ⟨.snglQPLeft hp hq hLo hr, hHi⟩
          | typHi hr =>
              cases hdst
              obtain ⟨hLo, hHi⟩ := ih hsrc rfl
              exact ⟨hLo, .snglQPRight hp hq hHi hr⟩
          | trm hr => cases hdst
      | andLeft hr => cases hdst
      | andRight hr => cases hdst
      | path => cases hdst
      | bnd hr => cases hdst
      | allDom hr => cases hdst
      | allCod hr => cases hdst
      | sngl => cases hdst
  | snglPQLeft hp hq hr h ih =>
      cases hr with
      | rcd hr =>
          cases hr with
          | typLo hr =>
              cases hsrc
              obtain ⟨hLo, hHi⟩ := ih rfl hdst
              exact ⟨.snglPQRight hp hq hLo hr, hHi⟩
          | typHi hr =>
              cases hsrc
              obtain ⟨hLo, hHi⟩ := ih rfl hdst
              exact ⟨hLo, .snglPQLeft hp hq hHi hr⟩
          | trm hr => cases hsrc
      | andLeft hr => cases hsrc
      | andRight hr => cases hsrc
      | path => cases hsrc
      | bnd hr => cases hsrc
      | allDom hr => cases hsrc
      | allCod hr => cases hsrc
      | sngl => cases hsrc
  | snglQPLeft hp hq hr h ih =>
      cases hr with
      | rcd hr =>
          cases hr with
          | typLo hr =>
              cases hsrc
              obtain ⟨hLo, hHi⟩ := ih rfl hdst
              exact ⟨.snglQPRight hp hq hLo hr, hHi⟩
          | typHi hr =>
              cases hsrc
              obtain ⟨hLo, hHi⟩ := ih rfl hdst
              exact ⟨hLo, .snglQPLeft hp hq hHi hr⟩
          | trm hr => cases hsrc
      | andLeft hr => cases hsrc
      | andRight hr => cases hsrc
      | path => cases hsrc
      | bnd hr => cases hsrc
      | allDom hr => cases hsrc
      | allCod hr => cases hsrc
      | sngl => cases hsrc
  | selRight hp h ih => cases hdst
  | selLeft hp h ih => cases hsrc
  | all L hdom hbody => cases hsrc

end CDot
