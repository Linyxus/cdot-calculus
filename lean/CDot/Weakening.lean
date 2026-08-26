import CDot.RecordAndInertTypes

/-! # Weakening -/

namespace CDot

variable [Signature]

def Env.Extends (G G' : Env α) : Prop :=
  ∀ ⦃x a⦄, Env.Binds x a G → Env.Binds x a G'

namespace Env.Extends

omit [Signature] in
theorem refl (G : Env α) : Env.Extends G G := by
  intro x a h
  exact h

omit [Signature] in
theorem trans {G₁ G₂ G₃ : Env α}
    (h₁₂ : Env.Extends G₁ G₂) (h₂₃ : Env.Extends G₂ G₃) :
    Env.Extends G₁ G₃ := by
  intro x a h
  exact h₂₃ (h₁₂ h)

omit [Signature] in
theorem push {G G' : Env α} (h : Env.Extends G G') (x : Var) (a : α) :
    Env.Extends (G.push x a) (G'.push x a) := by
  intro y b hb
  cases hb with
  | here => exact .here
  | there hn hb => exact .there hn (h hb)

end Env.Extends

theorem Typed.mono {G G' : Ctx} {t T} (h : Typed G t T)
    (he : Env.Extends G G') : Typed G' t T := by
  revert G'
  apply Typed.rec
    (motive_1 := fun G t T _ => ∀ G', Env.Extends G G' → Typed G' t T)
    (motive_2 := fun x fs G d D _ => ∀ G', Env.Extends G G' → TypedDef x fs G' d D)
    (motive_3 := fun x fs G ds T _ => ∀ G', Env.Extends G G' → TypedDefs x fs G' ds T)
    (motive_4 := fun G S T _ => ∀ G', Env.Extends G G' → Subtyp G' S T)
  case var =>
    intro x T G hb G' he
    exact Typed.var (he hb)
  case allIntro =>
    intro G T t U L hb ih G' he
    exact Typed.allIntro L (fun z hz => ih z hz _ (he.push z T))
  case allElim =>
    intro G p S T q hf ha ihf iha G' he
    exact Typed.allElim (ihf G' he) (iha G' he)
  case newIntro =>
    intro p A G T ds L hd hs ihd ihs G' he
    exact Typed.newIntro L (fun z hz => ihd z hz _ (he.push z _))
      (fun z hz => ihs z hz _ (he.push z _))
  case newElim =>
    intro G p a T hp ih G' he
    exact Typed.newElim (ih G' he)
  case rcdIntro =>
    intro G T p a hp ih G' he
    exact Typed.rcdIntro (ih G' he)
  case letE =>
    intro G t T U u L ht hu iht ihu G' he
    exact Typed.letE L (iht G' he) (fun x hx => ihu x hx _ (he.push x _))
  case caseE =>
    intro G p S q U A T t₂ t₁ L hp hq ht hu ihp ihq iht ihu G' he
    exact Typed.caseE L (ihp G' he) (ihq G' he)
      (fun y hy => iht y hy _ (he.push y _)) (ihu G' he)
  case sngl =>
    intro G p q T hp hq ihp ihq G' he
    exact Typed.sngl (ihp G' he) (ihq G' he)
  case self =>
    intro G p T hp ih G' he
    exact Typed.self (ih G' he)
  case pathElim =>
    intro G p q a T hp hq ihp ihq G' he
    exact Typed.pathElim (ihp G' he) (ihq G' he)
  case recIntro =>
    intro G p T hp ih G' he
    exact Typed.recIntro (ih G' he)
  case recElim =>
    intro G p T hp ih G' he
    exact Typed.recElim (ih G' he)
  case andIntro =>
    intro G p T U hT hU ihT ihU G' he
    exact Typed.andIntro (ihT G' he) (ihU G' he)
  case sub =>
    intro G t T U ht hs iht ihs G' he
    exact Typed.sub (iht G' he) (ihs G' he)
  case typ =>
    intro x fields G A T G' he
    exact TypedDef.typ
  case all =>
    intro G T t U V x fields b ht ih G' he
    exact TypedDef.all (ih G' he)
  case new =>
    intro x fields T b G q A ds p hp tight hdefs ht ihdefs iht G' he
    exact TypedDef.new p hp tight (ihdefs G' he) (iht G' he)
  case path =>
    intro G q T x fields b ht ih G' he
    exact TypedDef.path (ih G' he)
  case one =>
    intro x fields G d D hd ih G' he
    exact TypedDefs.one (ih G' he)
  case cons =>
    intro x fields G ds T d D hds hd hno ihds ihd G' he
    exact TypedDefs.cons (ihds G' he) (ihd G' he) hno
  case top =>
    intro G T G' he
    exact Subtyp.top
  case bot =>
    intro G T G' he
    exact Subtyp.bot
  case refl =>
    intro G T G' he
    exact Subtyp.refl
  case trans =>
    intro G S T U h₁ h₂ ih₁ ih₂ G' he
    exact Subtyp.trans (ih₁ G' he) (ih₂ G' he)
  case andLeft =>
    intro G T U G' he
    exact Subtyp.andLeft
  case andRight =>
    intro G T U G' he
    exact Subtyp.andRight
  case andIntro =>
    intro G S T U h₁ h₂ ih₁ ih₂ G' he
    exact Subtyp.andIntro (ih₁ G' he) (ih₂ G' he)
  case fld =>
    intro G T U a h ih G' he
    exact Subtyp.fld (ih G' he)
  case fldInv =>
    intro G U₁ a T₂ T₁ h hu ih G' he
    exact Subtyp.fldInv (ih G' he) hu
  case typ =>
    intro G S₂ S₁ T₁ T₂ A h₁ h₂ ih₁ ih₂ G' he
    exact Subtyp.typ (ih₁ G' he) (ih₂ G' he)
  case typInvLo =>
    intro G U₁ A S₂ T₂ S₁ T₁ h hu ih G' he
    exact Subtyp.typInvLo (ih G' he) hu
  case typInvHi =>
    intro G U₁ A S₂ T₂ S₁ T₁ h hu ih G' he
    exact Subtyp.typInvHi (ih G' he) hu
  case allInv =>
    intro G S₁ T₁ S₂ T₂ h ih G' he
    exact Subtyp.allInv (ih G' he)
  case snglPQ =>
    intro G p q U T T' hp hq hr ihp ihq G' he
    exact Subtyp.snglPQ (ihp G' he) (ihq G' he) hr
  case snglQP =>
    intro G p q U T T' hp hq hr ihp ihq G' he
    exact Subtyp.snglQP (ihp G' he) (ihq G' he) hr
  case selLo =>
    intro G p A S T hp ih G' he
    exact Subtyp.selLo (ih G' he)
  case selHi =>
    intro G p A S T hp ih G' he
    exact Subtyp.selHi (ih G' he)
  case all =>
    intro G S₂ S₁ T₁ T₂ L hd hc ihd ihc G' he
    exact Subtyp.all L (ihd G' he) (fun x hx => ihc x hx _ (he.push x _))
  case t => exact h

end CDot
