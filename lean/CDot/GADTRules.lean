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

end CDot
