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

theorem SemanticSubtyp.andSource {G : Ctx} {S T U V : Typ}
    (hT : ∀ W, SemanticSubtyp G T W → SemanticSubtyp G S W)
    (hU : ∀ W, SemanticSubtyp G U W → SemanticSubtyp G S W)
    (h : SemanticSubtyp G (.and T U) V) : SemanticSubtyp G S V := by
  generalize heq : Typ.and T U = X at h
  induction h generalizing S T U with
  | top => exact .top
  | bot => cases heq
  | refl =>
      cases heq
      exact .andIntro (hT _ .refl) (hU _ .refl)
  | andLeft h ih =>
      cases heq
      exact hT _ h
  | andRight h ih =>
      cases heq
      exact hU _ h
  | andIntro h₁ h₂ ih₁ ih₂ =>
      exact .andIntro (ih₁ hT hU heq) (ih₂ hT hU heq)
  | fld h ih => cases heq
  | typ hLo hHi => cases heq
  | snglPQRight hp hq hr h ih =>
      exact .snglPQRight hp hq hr (ih hT hU heq)
  | snglQPRight hp hq hr h ih =>
      exact .snglQPRight hp hq hr (ih hT hU heq)
  | snglPQLeft hp hq hr h ih =>
      cases hr with
      | rcd hr => cases heq
      | andLeft hr =>
          cases heq
          apply ih
          · intro W hW
            exact hT W (.snglPQLeft hp hq hr hW)
          · exact hU
          · rfl
      | andRight hr =>
          cases heq
          apply ih
          · exact hT
          · intro W hW
            exact hU W (.snglPQLeft hp hq hr hW)
          · rfl
      | path => cases heq
      | bnd hr => cases heq
      | allDom hr => cases heq
      | allCod hr => cases heq
      | sngl => cases heq
  | snglQPLeft hp hq hr h ih =>
      cases hr with
      | rcd hr => cases heq
      | andLeft hr =>
          cases heq
          apply ih
          · intro W hW
            exact hT W (.snglQPLeft hp hq hr hW)
          · exact hU
          · rfl
      | andRight hr =>
          cases heq
          apply ih
          · exact hT
          · intro W hW
            exact hU W (.snglQPLeft hp hq hr hW)
          · rfl
      | path => cases heq
      | bnd hr => cases heq
      | allDom hr => cases heq
      | allCod hr => cases heq
      | sngl => cases heq
  | selRight hp h ih => exact .selRight hp (ih hT hU heq)
  | selLeft hp h ih => cases heq
  | all L hdom hbody => cases heq

theorem SemanticSubtyp.fldSource {G : Ctx} {a : Signature.TrmLabel}
    {S T U : Typ}
    (hST : ∀ W, SemanticSubtyp G T W → SemanticSubtyp G S W)
    (h : SemanticSubtyp G (.rcd (.trm a T)) U) :
    SemanticSubtyp G (.rcd (.trm a S)) U := by
  generalize heq : Typ.rcd (Dec.trm a T) = X at h
  induction h generalizing S T with
  | top => exact .top
  | bot => cases heq
  | refl =>
      cases heq
      exact .fld (hST _ .refl)
  | andLeft h ih => cases heq
  | andRight h ih => cases heq
  | andIntro h₁ h₂ ih₁ ih₂ =>
      exact .andIntro (ih₁ hST heq) (ih₂ hST heq)
  | fld h ih =>
      cases heq
      exact .fld (hST _ h)
  | typ hLo hHi => cases heq
  | snglPQRight hp hq hr h ih =>
      exact .snglPQRight hp hq hr (ih hST heq)
  | snglQPRight hp hq hr h ih =>
      exact .snglQPRight hp hq hr (ih hST heq)
  | snglPQLeft hp hq hr h ih =>
      cases hr with
      | rcd hr =>
          cases hr with
          | typLo hr => cases heq
          | typHi hr => cases heq
          | trm hr =>
              cases heq
              apply ih
              · intro W hW
                exact hST W (.snglPQLeft hp hq hr hW)
              · rfl
      | andLeft hr => cases heq
      | andRight hr => cases heq
      | path => cases heq
      | bnd hr => cases heq
      | allDom hr => cases heq
      | allCod hr => cases heq
      | sngl => cases heq
  | snglQPLeft hp hq hr h ih =>
      cases hr with
      | rcd hr =>
          cases hr with
          | typLo hr => cases heq
          | typHi hr => cases heq
          | trm hr =>
              cases heq
              apply ih
              · intro W hW
                exact hST W (.snglQPLeft hp hq hr hW)
              · rfl
      | andLeft hr => cases heq
      | andRight hr => cases heq
      | path => cases heq
      | bnd hr => cases heq
      | allDom hr => cases heq
      | allCod hr => cases heq
      | sngl => cases heq
  | selRight hp h ih => exact .selRight hp (ih hST heq)
  | selLeft hp h ih => cases heq
  | all L hdom hbody => cases heq

theorem SemanticSubtyp.typSource {G : Ctx} {A : Signature.TypLabel}
    {S₁ S₂ T₁ T₂ U : Typ}
    (hLo : TightSubtyp G S₂ S₁) (hHi : TightSubtyp G T₁ T₂)
    (h : SemanticSubtyp G (.rcd (.typ A S₂ T₂)) U) :
    SemanticSubtyp G (.rcd (.typ A S₁ T₁)) U := by
  generalize heq : Typ.rcd (Dec.typ A S₂ T₂) = X at h
  induction h generalizing S₂ T₂ with
  | top => exact .top
  | bot => cases heq
  | refl =>
      cases heq
      exact .typ hLo hHi
  | andLeft h ih => cases heq
  | andRight h ih => cases heq
  | andIntro h₁ h₂ ih₁ ih₂ =>
      exact .andIntro (ih₁ hLo hHi heq) (ih₂ hLo hHi heq)
  | fld h ih => cases heq
  | typ hLo' hHi' =>
      cases heq
      exact .typ (.trans hLo' hLo) (.trans hHi hHi')
  | snglPQRight hp hq hr h ih =>
      exact .snglPQRight hp hq hr (ih hLo hHi heq)
  | snglQPRight hp hq hr h ih =>
      exact .snglQPRight hp hq hr (ih hLo hHi heq)
  | snglPQLeft hp hq hr h ih =>
      cases hr with
      | rcd hr =>
          cases hr with
          | typLo hr =>
              cases heq
              apply ih (.trans (.snglPQ hp hq hr) hLo) hHi rfl
          | typHi hr =>
              cases heq
              apply ih hLo (.trans hHi (.snglQP hp hq hr.swap)) rfl
          | trm hr => cases heq
      | andLeft hr => cases heq
      | andRight hr => cases heq
      | path => cases heq
      | bnd hr => cases heq
      | allDom hr => cases heq
      | allCod hr => cases heq
      | sngl => cases heq
  | snglQPLeft hp hq hr h ih =>
      cases hr with
      | rcd hr =>
          cases hr with
          | typLo hr =>
              cases heq
              apply ih (.trans (.snglQP hp hq hr) hLo) hHi rfl
          | typHi hr =>
              cases heq
              apply ih hLo (.trans hHi (.snglPQ hp hq hr.swap)) rfl
          | trm hr => cases heq
      | andLeft hr => cases heq
      | andRight hr => cases heq
      | path => cases heq
      | bnd hr => cases heq
      | allDom hr => cases heq
      | allCod hr => cases heq
      | sngl => cases heq
  | selRight hp h ih => exact .selRight hp (ih hLo hHi heq)
  | selLeft hp h ih => cases heq
  | all L hdom hbody => cases heq

theorem SemanticSubtyp.allSource {G : Ctx} {S₁ S₂ T₁ T₂ U : Typ}
    (hi : Inert G) (L : Vars) (hDom : TightSubtyp G S₂ S₁)
    (hBody : ∀ x, x ∉ L →
      Subtyp (G.push x S₂) (T₁.open x) (T₂.open x))
    (h : SemanticSubtyp G (.all S₂ T₂) U) :
    SemanticSubtyp G (.all S₁ T₁) U := by
  generalize heq : Typ.all S₂ T₂ = X at h
  induction h generalizing S₂ T₂ L with
  | top => exact .top
  | bot => cases heq
  | refl =>
      cases heq
      exact .all L hDom hBody
  | andLeft h ih => cases heq
  | andRight h ih => cases heq
  | andIntro h₁ h₂ ih₁ ih₂ =>
      exact .andIntro (ih₁ L hDom hBody heq) (ih₂ L hDom hBody heq)
  | fld h ih => cases heq
  | typ hLo hHi => cases heq
  | snglPQRight hp hq hr h ih =>
      exact .snglPQRight hp hq hr (ih L hDom hBody heq)
  | snglQPRight hp hq hr h ih =>
      exact .snglQPRight hp hq hr (ih L hDom hBody heq)
  | snglPQLeft hp hq hr h ih =>
      cases hr with
      | rcd hr => cases heq
      | andLeft hr => cases heq
      | andRight hr => cases heq
      | path => cases heq
      | bnd hr => cases heq
      | allDom hr =>
          rename_i SPrev SFinal Cod
          cases heq
          let L' := L ∪ G.dom
          apply ih (S₂ := SPrev) (T₂ := T₂) L'
            (.trans (TightSubtyp.snglPQ hp hq hr) hDom)
          · intro x hx
            simp only [L', Finset.mem_union, not_or] at hx
            have hok₂ : Env.Ok (G.push x S₂) := Env.okPush hi.ok hx.2
            have hokPrev : Env.Ok (G.push x SPrev) := Env.okPush hi.ok hx.2
            exact (hBody x hx.1).narrow
              (Subenv.last (.snglPQ hp.toGeneral hq.toGeneral hr)
                hokPrev hok₂)
          · rfl
      | allCod hr =>
          rename_i TPrev TFinal Dom
          cases heq
          let L' := L ∪ G.dom
          apply ih (S₂ := S₂) (T₂ := TPrev) L' hDom
          · intro x hx
            simp only [L', Finset.mem_union, not_or] at hx
            have hok : Env.Ok (G.push x S₂) := Env.okPush hi.ok hx.2
            have hext : Env.Extends G (G.push x S₂) :=
              .pushRight hx.2 S₂
            have hp' := hp.mono hext hok
            have hq' := hq.mono hext hok
            have hr' := hr.openVar hp.toGeneral.pathNamed
              hq.toGeneral.pathNamed x
            exact .trans (hBody x hx.1)
              (TightSubtyp.snglQP hp' hq' hr'.swap).toGeneral
          · rfl
      | sngl => cases heq
  | snglQPLeft hp hq hr h ih =>
      cases hr with
      | rcd hr => cases heq
      | andLeft hr => cases heq
      | andRight hr => cases heq
      | path => cases heq
      | bnd hr => cases heq
      | allDom hr =>
          rename_i SPrev SFinal Cod
          cases heq
          let L' := L ∪ G.dom
          apply ih (S₂ := SPrev) (T₂ := T₂) L'
            (.trans (TightSubtyp.snglQP hp hq hr) hDom)
          · intro x hx
            simp only [L', Finset.mem_union, not_or] at hx
            have hok₂ : Env.Ok (G.push x S₂) := Env.okPush hi.ok hx.2
            have hokPrev : Env.Ok (G.push x SPrev) := Env.okPush hi.ok hx.2
            exact (hBody x hx.1).narrow
              (Subenv.last (.snglQP hp.toGeneral hq.toGeneral hr)
                hokPrev hok₂)
          · rfl
      | allCod hr =>
          rename_i TPrev TFinal Dom
          cases heq
          let L' := L ∪ G.dom
          apply ih (S₂ := S₂) (T₂ := TPrev) L' hDom
          · intro x hx
            simp only [L', Finset.mem_union, not_or] at hx
            have hok : Env.Ok (G.push x S₂) := Env.okPush hi.ok hx.2
            have hext : Env.Extends G (G.push x S₂) :=
              .pushRight hx.2 S₂
            have hp' := hp.mono hext hok
            have hq' := hq.mono hext hok
            have hr' := hr.openVar hq.toGeneral.pathNamed
              hp.toGeneral.pathNamed x
            exact .trans (hBody x hx.1)
              (TightSubtyp.snglPQ hp' hq' hr'.swap).toGeneral
          · rfl
      | sngl => cases heq
  | selRight hp h ih => exact .selRight hp (ih L hDom hBody heq)
  | selLeft hp h ih => cases heq
  | all L' hDom' hBody' =>
      rename_i S₂ T₂ S₃ T₃
      cases heq
      let L'' := (L ∪ L') ∪ G.dom
      apply SemanticSubtyp.all L'' (.trans hDom' hDom)
      intro x hx
      simp only [L'', Finset.mem_union, not_or] at hx
      have hok₂ : Env.Ok (G.push x S₂) := Env.okPush hi.ok hx.2
      have hokMid : Env.Ok (G.push x T₂) := Env.okPush hi.ok hx.2
      have hleft := (hBody x hx.1.1).narrow
        (Subenv.last hDom'.toGeneral hok₂ hokMid)
      exact .trans hleft (hBody' x hx.1.2)

theorem SemanticSubtyp.transWithSelection {G : Ctx} (hi : Inert G)
    (selInv : ∀ {p : Path} {A : Signature.TypLabel} {T U : Typ},
      PreciseTyping3 G p (.rcd (.typ A T T)) →
      SemanticSubtyp G (.path p A) U → SemanticSubtyp G T U)
    {S T U : Typ} (hST : SemanticSubtyp G S T)
    (hTU : SemanticSubtyp G T U) : SemanticSubtyp G S U := by
  induction hST generalizing U with
  | top => exact hTU.topLeft
  | bot => exact .bot
  | refl => exact hTU
  | andLeft h ih => exact .andLeft (ih hTU)
  | andRight h ih => exact .andRight (ih hTU)
  | andIntro hT hU ihT ihU =>
      exact hTU.andSource (fun _ h => ihT h) (fun _ h => ihU h)
  | fld h ih => exact hTU.fldSource (fun _ h => ih h)
  | typ hLo hHi => exact hTU.typSource hLo hHi
  | snglPQRight hp hq hr h ih =>
      exact ih (.snglQPLeft hp hq hr.swap hTU)
  | snglQPRight hp hq hr h ih =>
      exact ih (.snglPQLeft hp hq hr.swap hTU)
  | snglPQLeft hp hq hr h ih =>
      exact .snglPQLeft hp hq hr (ih hTU)
  | snglQPLeft hp hq hr h ih =>
      exact .snglQPLeft hp hq hr (ih hTU)
  | selRight hp h ih => exact ih (selInv hp hTU)
  | selLeft hp h ih => exact .selLeft hp (ih hTU)
  | all L hDom hBody => exact hTU.allSource hi L hDom hBody

end CDot
