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

theorem TightSubtyp.trmInvert {G : Ctx} {a : Signature.TrmLabel}
    {T U : Typ} (hi : Inert G)
    (h : TightSubtyp G (.rcd (.trm a T)) (.rcd (.trm a U))) :
    TightSubtyp G T U :=
  (h.toSemantic hi).trmInvert.toTight

theorem TightSubtyp.typInvert {G : Ctx} {A : Signature.TypLabel}
    {S₁ T₁ S₂ T₂ : Typ} (hi : Inert G)
    (h : TightSubtyp G (.rcd (.typ A S₁ T₁))
      (.rcd (.typ A S₂ T₂))) :
    TightSubtyp G S₂ S₁ ∧ TightSubtyp G T₁ T₂ :=
  (h.toSemantic hi).typInvert

theorem SemanticSubtyp.allInvert {G : Ctx} {S₁ T₁ S₂ T₂ : Typ}
    (hi : Inert G)
    (h : SemanticSubtyp G (.all S₁ T₁) (.all S₂ T₂)) :
    TightSubtyp G S₂ S₁ ∧ ∃ L : Vars, ∀ x, x ∉ L →
      Subtyp (G.push x S₂) (T₁.open x) (T₂.open x) := by
  generalize hsrc : Typ.all S₁ T₁ = S at h
  generalize hdst : Typ.all S₂ T₂ = V at h
  induction h generalizing S₁ T₁ S₂ T₂ with
  | top => cases hdst
  | bot => cases hsrc
  | refl =>
      cases hsrc
      cases hdst
      exact ⟨.refl, ∅, fun _ _ => .refl⟩
  | andLeft h ih => cases hsrc
  | andRight h ih => cases hsrc
  | andIntro h₁ h₂ ih₁ ih₂ => cases hdst
  | fld h ih => cases hsrc
  | typ hLo hHi => cases hsrc
  | snglPQRight hp hq hr h ih =>
      cases hr with
      | allDom hr =>
          cases hdst
          obtain ⟨hdom, L, hbody⟩ := ih hsrc rfl
          let L' := L ∪ G.dom
          refine ⟨.trans (.snglQP hp hq hr.swap) hdom, L', ?_⟩
          intro x hx
          simp only [L', Finset.mem_union, not_or] at hx
          exact (hbody x hx.1).narrow
            (Subenv.last (TightSubtyp.snglQP hp hq hr.swap).toGeneral
              (Env.okPush hi.ok hx.2) (Env.okPush hi.ok hx.2))
      | allCod hr =>
          cases hdst
          obtain ⟨hdom, L, hbody⟩ := ih hsrc rfl
          let L' := L ∪ G.dom
          refine ⟨hdom, L', ?_⟩
          intro x hx
          simp only [L', Finset.mem_union, not_or] at hx
          exact .trans (hbody x hx.1)
            (TightSubtyp.snglPQ
              (hp.mono (.pushRight hx.2 _) (Env.okPush hi.ok hx.2))
              (hq.mono (.pushRight hx.2 _) (Env.okPush hi.ok hx.2))
              (hr.openVar hp.toGeneral.pathNamed hq.toGeneral.pathNamed x)).toGeneral
      | rcd hr => cases hdst
      | andLeft hr => cases hdst
      | andRight hr => cases hdst
      | path => cases hdst
      | bnd hr => cases hdst
      | sngl => cases hdst
  | snglQPRight hp hq hr h ih =>
      cases hr with
      | allDom hr =>
          cases hdst
          obtain ⟨hdom, L, hbody⟩ := ih hsrc rfl
          let L' := L ∪ G.dom
          refine ⟨.trans (.snglPQ hp hq hr.swap) hdom, L', ?_⟩
          intro x hx
          simp only [L', Finset.mem_union, not_or] at hx
          exact (hbody x hx.1).narrow
            (Subenv.last (TightSubtyp.snglPQ hp hq hr.swap).toGeneral
              (Env.okPush hi.ok hx.2) (Env.okPush hi.ok hx.2))
      | allCod hr =>
          cases hdst
          obtain ⟨hdom, L, hbody⟩ := ih hsrc rfl
          let L' := L ∪ G.dom
          refine ⟨hdom, L', ?_⟩
          intro x hx
          simp only [L', Finset.mem_union, not_or] at hx
          exact .trans (hbody x hx.1)
            (TightSubtyp.snglQP
              (hp.mono (.pushRight hx.2 _) (Env.okPush hi.ok hx.2))
              (hq.mono (.pushRight hx.2 _) (Env.okPush hi.ok hx.2))
              (hr.openVar hq.toGeneral.pathNamed hp.toGeneral.pathNamed x)).toGeneral
      | rcd hr => cases hdst
      | andLeft hr => cases hdst
      | andRight hr => cases hdst
      | path => cases hdst
      | bnd hr => cases hdst
      | sngl => cases hdst
  | snglPQLeft hp hq hr h ih =>
      cases hr with
      | allDom hr =>
          cases hsrc
          obtain ⟨hdom, L, hbody⟩ := ih rfl hdst
          exact ⟨.trans hdom (.snglPQ hp hq hr), L, hbody⟩
      | allCod hr =>
          cases hsrc
          obtain ⟨hdom, L, hbody⟩ := ih rfl hdst
          let L' := L ∪ G.dom
          refine ⟨hdom, L', ?_⟩
          intro x hx
          simp only [L', Finset.mem_union, not_or] at hx
          exact .trans
            (TightSubtyp.snglQP
              (hp.mono (.pushRight hx.2 _) (Env.okPush hi.ok hx.2))
              (hq.mono (.pushRight hx.2 _) (Env.okPush hi.ok hx.2))
              (hr.openVar hp.toGeneral.pathNamed hq.toGeneral.pathNamed x).swap).toGeneral
            (hbody x hx.1)
      | rcd hr => cases hsrc
      | andLeft hr => cases hsrc
      | andRight hr => cases hsrc
      | path => cases hsrc
      | bnd hr => cases hsrc
      | sngl => cases hsrc
  | snglQPLeft hp hq hr h ih =>
      cases hr with
      | allDom hr =>
          cases hsrc
          obtain ⟨hdom, L, hbody⟩ := ih rfl hdst
          exact ⟨.trans hdom (.snglQP hp hq hr), L, hbody⟩
      | allCod hr =>
          cases hsrc
          obtain ⟨hdom, L, hbody⟩ := ih rfl hdst
          let L' := L ∪ G.dom
          refine ⟨hdom, L', ?_⟩
          intro x hx
          simp only [L', Finset.mem_union, not_or] at hx
          exact .trans
            (TightSubtyp.snglPQ
              (hp.mono (.pushRight hx.2 _) (Env.okPush hi.ok hx.2))
              (hq.mono (.pushRight hx.2 _) (Env.okPush hi.ok hx.2))
              (hr.openVar hq.toGeneral.pathNamed hp.toGeneral.pathNamed x).swap).toGeneral
            (hbody x hx.1)
      | rcd hr => cases hsrc
      | andLeft hr => cases hsrc
      | andRight hr => cases hsrc
      | path => cases hsrc
      | bnd hr => cases hsrc
      | sngl => cases hsrc
  | selRight hp h ih => cases hdst
  | selLeft hp h ih => cases hsrc
  | all L hdom hbody =>
      cases hsrc
      cases hdst
      exact ⟨hdom, L, hbody⟩

theorem TightSubtyp.allInvert {G : Ctx} {S₁ T₁ S₂ T₂ : Typ}
    (hi : Inert G) (h : TightSubtyp G (.all S₁ T₁) (.all S₂ T₂)) :
    TightSubtyp G S₂ S₁ ∧ ∃ L : Vars, ∀ x, x ∉ L →
      Subtyp (G.push x S₂) (T₁.open x) (T₂.open x) :=
  (h.toSemantic hi).allInvert hi

theorem SemanticSubtyp.andRcdCases {G : Ctx} {T U : Typ} {D : Dec}
    (h : SemanticSubtyp G (.and T U) (.rcd D)) :
    SemanticSubtyp G T (.rcd D) ∨ SemanticSubtyp G U (.rcd D) := by
  generalize hsrc : Typ.and T U = S at h
  generalize hdst : Typ.rcd D = V at h
  induction h generalizing T U D with
  | top => cases hdst
  | bot => cases hsrc
  | refl => cases hsrc; cases hdst
  | andLeft h ih =>
      cases hsrc
      exact Or.inl h
  | andRight h ih =>
      cases hsrc
      exact Or.inr h
  | andIntro h₁ h₂ ih₁ ih₂ => cases hdst
  | fld h ih => cases hsrc
  | typ hLo hHi => cases hsrc
  | snglPQRight hp hq hr h ih =>
      cases hr with
      | rcd hr =>
          cases hdst
          rcases ih hsrc rfl with h | h
          · exact Or.inl (.snglPQRight hp hq (.rcd hr) h)
          · exact Or.inr (.snglPQRight hp hq (.rcd hr) h)
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
          cases hdst
          rcases ih hsrc rfl with h | h
          · exact Or.inl (.snglQPRight hp hq (.rcd hr) h)
          · exact Or.inr (.snglQPRight hp hq (.rcd hr) h)
      | andLeft hr => cases hdst
      | andRight hr => cases hdst
      | path => cases hdst
      | bnd hr => cases hdst
      | allDom hr => cases hdst
      | allCod hr => cases hdst
      | sngl => cases hdst
  | snglPQLeft hp hq hr h ih =>
      cases hr with
      | rcd hr => cases hsrc
      | andLeft hr =>
          cases hsrc
          rcases ih rfl hdst with h | h
          · exact Or.inl (.snglPQLeft hp hq hr h)
          · exact Or.inr h
      | andRight hr =>
          cases hsrc
          rcases ih rfl hdst with h | h
          · exact Or.inl h
          · exact Or.inr (.snglPQLeft hp hq hr h)
      | path => cases hsrc
      | bnd hr => cases hsrc
      | allDom hr => cases hsrc
      | allCod hr => cases hsrc
      | sngl => cases hsrc
  | snglQPLeft hp hq hr h ih =>
      cases hr with
      | rcd hr => cases hsrc
      | andLeft hr =>
          cases hsrc
          rcases ih rfl hdst with h | h
          · exact Or.inl (.snglQPLeft hp hq hr h)
          · exact Or.inr h
      | andRight hr =>
          cases hsrc
          rcases ih rfl hdst with h | h
          · exact Or.inl h
          · exact Or.inr (.snglQPLeft hp hq hr h)
      | path => cases hsrc
      | bnd hr => cases hsrc
      | allDom hr => cases hsrc
      | allCod hr => cases hsrc
      | sngl => cases hsrc
  | selRight hp h ih => cases hdst
  | selLeft hp h ih => cases hsrc
  | all L hdom hbody => cases hsrc

theorem ReplDec.label_eq {p q : Path} {D E : Dec} (h : ReplDec p q D E) :
    D.label = E.label := by
  cases h <;> rfl

theorem SemanticSubtyp.rcdLabel_eq {G : Ctx} {D E : Dec}
    (h : SemanticSubtyp G (.rcd D) (.rcd E)) : D.label = E.label := by
  generalize hsrc : Typ.rcd D = S at h
  generalize hdst : Typ.rcd E = T at h
  induction h generalizing D E with
  | top => cases hdst
  | bot => cases hsrc
  | refl =>
      cases hsrc
      cases hdst
      rfl
  | andLeft h ih => cases hsrc
  | andRight h ih => cases hsrc
  | andIntro h₁ h₂ ih₁ ih₂ => cases hdst
  | fld h ih =>
      cases hsrc
      cases hdst
      rfl
  | typ hLo hHi =>
      cases hsrc
      cases hdst
      rfl
  | snglPQRight hp hq hr h ih =>
      cases hr with
      | rcd hr =>
          cases hdst
          exact (ih hsrc rfl).trans hr.label_eq
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
          cases hdst
          exact (ih hsrc rfl).trans hr.label_eq
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
          cases hsrc
          have hmid := ih (D := _) (E := E) rfl hdst
          exact hr.label_eq.symm.trans hmid
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
          cases hsrc
          have hmid := ih (D := _) (E := E) rfl hdst
          exact hr.label_eq.symm.trans hmid
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

theorem SemanticSubtyp.bndRcd_false {G : Ctx} {T : Typ} {D : Dec}
    (h : SemanticSubtyp G (.bnd T) (.rcd D)) : False := by
  generalize hsrc : Typ.bnd T = S at h
  generalize hdst : Typ.rcd D = U at h
  induction h generalizing T D with
  | top => cases hdst
  | bot => cases hsrc
  | refl => cases hsrc; cases hdst
  | andLeft h ih => cases hsrc
  | andRight h ih => cases hsrc
  | andIntro h₁ h₂ ih₁ ih₂ => cases hdst
  | fld h ih => cases hsrc
  | typ hLo hHi => cases hsrc
  | snglPQRight hp hq hr h ih =>
      cases hr with
      | rcd hr => cases hdst; exact ih hsrc rfl
      | andLeft hr => cases hdst
      | andRight hr => cases hdst
      | path => cases hdst
      | bnd hr => cases hdst
      | allDom hr => cases hdst
      | allCod hr => cases hdst
      | sngl => cases hdst
  | snglQPRight hp hq hr h ih =>
      cases hr with
      | rcd hr => cases hdst; exact ih hsrc rfl
      | andLeft hr => cases hdst
      | andRight hr => cases hdst
      | path => cases hdst
      | bnd hr => cases hdst
      | allDom hr => cases hdst
      | allCod hr => cases hdst
      | sngl => cases hdst
  | snglPQLeft hp hq hr h ih =>
      cases hr with
      | bnd hr => cases hsrc; exact ih rfl hdst
      | rcd hr => cases hsrc
      | andLeft hr => cases hsrc
      | andRight hr => cases hsrc
      | path => cases hsrc
      | allDom hr => cases hsrc
      | allCod hr => cases hsrc
      | sngl => cases hsrc
  | snglQPLeft hp hq hr h ih =>
      cases hr with
      | bnd hr => cases hsrc; exact ih rfl hdst
      | rcd hr => cases hsrc
      | andLeft hr => cases hsrc
      | andRight hr => cases hsrc
      | path => cases hsrc
      | allDom hr => cases hsrc
      | allCod hr => cases hsrc
      | sngl => cases hsrc
  | selRight hp h ih => cases hdst
  | selLeft hp h ih => cases hsrc
  | all L hdom hbody => cases hsrc

theorem UniqueMembership.memberLabel {U : Typ} {labels : Finset Label} {D : Dec}
    (h : UniqueMembership U labels (.rcd D)) : D.label ∈ labels := by
  generalize heq : Typ.rcd D = T at h
  induction h generalizing D with
  | typ =>
      cases heq
      simp [Dec.label]
  | trm =>
      cases heq
      simp [Dec.label]
  | bnd => cases heq
  | andLeft h₁ h₂ hd ih₁ ih₂ =>
      exact Finset.mem_union_left _ (ih₁ heq)
  | andRight h₁ h₂ hd ih₁ ih₂ =>
      exact Finset.mem_union_right _ (ih₂ heq)

theorem UniqueMembership.targetRcdLabel_mem {G : Ctx} {U T : Typ}
    {labels : Finset Label} {D : Dec}
    (hu : UniqueMembership U labels T)
    (h : SemanticSubtyp G U (.rcd D)) : D.label ∈ labels := by
  induction hu with
  | typ =>
      have heq := h.rcdLabel_eq
      rw [← heq]
      simp [Dec.label]
  | trm =>
      have heq := h.rcdLabel_eq
      rw [← heq]
      simp [Dec.label]
  | bnd => exact False.elim h.bndRcd_false
  | andLeft h₁ h₂ hd ih₁ ih₂ =>
      rcases h.andRcdCases with h | h
      · exact Finset.mem_union_left _ (ih₁ h)
      · exact Finset.mem_union_right _ (ih₂ h)
  | andRight h₁ h₂ hd ih₁ ih₂ =>
      rcases h.andRcdCases with h | h
      · exact Finset.mem_union_left _ (ih₁ h)
      · exact Finset.mem_union_right _ (ih₂ h)

theorem SemanticSubtyp.reduceUniqueSource {G : Ctx} {U : Typ}
    {labels : Finset Label} {D₁ D₂ : Dec}
    (hu : UniqueMembership U labels (.rcd D₁))
    (h : SemanticSubtyp G U (.rcd D₂))
    (hlab : D₁.label = D₂.label) :
    SemanticSubtyp G (.rcd D₁) (.rcd D₂) := by
  generalize heq : Typ.rcd D₁ = T at hu
  induction hu generalizing D₁ D₂ with
  | typ =>
      cases heq
      exact h
  | trm =>
      cases heq
      exact h
  | bnd => cases heq
  | andLeft h₁ h₂ hd ih₁ ih₂ =>
      rcases h.andRcdCases with hleft | hright
      · exact ih₁ hleft hlab heq
      · rw [← heq] at h₁
        have hselected := h₁.memberLabel
        have htarget := h₂.targetRcdLabel_mem hright
        rw [hlab] at hselected
        have hempty : D₂.label ∈ (∅ : Finset Label) :=
          hd.le_bot (Finset.mem_inter.mpr ⟨hselected, htarget⟩)
        simp at hempty
  | andRight h₁ h₂ hd ih₁ ih₂ =>
      rcases h.andRcdCases with hleft | hright
      · rw [← heq] at h₂
        have hselected := h₂.memberLabel
        have htarget := h₁.targetRcdLabel_mem hleft
        rw [hlab] at hselected
        have hempty : D₂.label ∈ (∅ : Finset Label) :=
          hd.le_bot (Finset.mem_inter.mpr ⟨htarget, hselected⟩)
        simp at hempty
      · exact ih₂ hright hlab heq

theorem TightSubtyp.trmInvertUnique {G : Ctx} {U : Typ}
    {a : Signature.TrmLabel} {T₁ T₂ : Typ} (hi : Inert G)
    (hu : Unique U (.rcd (.trm a T₁)))
    (h : TightSubtyp G U (.rcd (.trm a T₂))) :
    TightSubtyp G T₁ T₂ := by
  obtain ⟨labels, hu⟩ := hu
  have hrecord := (h.toSemantic hi).reduceUniqueSource hu rfl
  exact hrecord.trmInvert.toTight

theorem TightSubtyp.typInvertUnique {G : Ctx} {U : Typ}
    {A : Signature.TypLabel} {S₁ T₁ S₂ T₂ : Typ} (hi : Inert G)
    (hu : Unique U (.rcd (.typ A S₁ T₁)))
    (h : TightSubtyp G U (.rcd (.typ A S₂ T₂))) :
    TightSubtyp G S₂ S₁ ∧ TightSubtyp G T₁ T₂ := by
  obtain ⟨labels, hu⟩ := hu
  have hrecord := (h.toSemantic hi).reduceUniqueSource hu rfl
  exact hrecord.typInvert

end CDot
