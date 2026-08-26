import CDot.Subenvironments

/-!
# Narrowing

Typing, definition typing, and subtyping are preserved when the context is
replaced by a subenvironment.
-/

namespace CDot

variable [Signature]

theorem Typed.narrow {G G' : Ctx} {t : Trm} {T : Typ}
    (h : Typed G t T) (hsub : Subenv G' G) : Typed G' t T := by
  revert G'
  apply Typed.rec
    (motive_1 := fun G t T _ => ∀ G', Subenv G' G → Typed G' t T)
    (motive_2 := fun x fs G d D _ => ∀ G', Subenv G' G → TypedDef x fs G' d D)
    (motive_3 := fun x fs G ds T _ => ∀ G', Subenv G' G → TypedDefs x fs G' ds T)
    (motive_4 := fun G S T _ => ∀ G', Subenv G' G → Subtyp G' S T)
  case var =>
    intro x T G hb G' hsub
    obtain ⟨S, hbS, hST⟩ := hsub.binds hb
    exact .sub (.var hbS) hST
  case allIntro =>
    intro G T t U L hbody ih G' hsub
    let L' := (L ∪ G.dom) ∪ G'.dom
    exact .allIntro L' (fun x hx => by
      simp only [L', Finset.mem_union, not_or] at hx
      exact ih x hx.1.1 _ (hsub.extend
        (Env.okPush hsub.ok.1 hx.2) (Env.okPush hsub.ok.2 hx.1.2)))
  case allElim =>
    intro G p S T q hf ha ihf iha G' hsub
    exact .allElim (ihf G' hsub) (iha G' hsub)
  case newIntro =>
    intro p A G T ds L hd hs ihd ihs G' hsub
    let L' := (L ∪ G.dom) ∪ G'.dom
    exact .newIntro L'
      (fun z hz => by
        simp only [L', Finset.mem_union, not_or] at hz
        exact ihd z hz.1.1 _ (hsub.extend
          (Env.okPush hsub.ok.1 hz.2) (Env.okPush hsub.ok.2 hz.1.2)))
      (fun z hz => by
        simp only [L', Finset.mem_union, not_or] at hz
        exact ihs z hz.1.1 _ (hsub.extend
          (Env.okPush hsub.ok.1 hz.2) (Env.okPush hsub.ok.2 hz.1.2)))
  case newElim =>
    intro G p a T hp ih G' hsub
    exact .newElim (ih G' hsub)
  case rcdIntro =>
    intro G T p a hp ih G' hsub
    exact .rcdIntro (ih G' hsub)
  case letE =>
    intro G t T U u L ht hu iht ihu G' hsub
    let L' := (L ∪ G.dom) ∪ G'.dom
    exact .letE L' (iht G' hsub) (fun x hx => by
      simp only [L', Finset.mem_union, not_or] at hx
      exact ihu x hx.1.1 _ (hsub.extend
        (Env.okPush hsub.ok.1 hx.2) (Env.okPush hsub.ok.2 hx.1.2)))
  case caseE =>
    intro G p S q U A T t₂ t₁ L hp hq ht hu ihp ihq iht ihu G' hsub
    let L' := (L ∪ G.dom) ∪ G'.dom
    exact .caseE L' (ihp G' hsub) (ihq G' hsub)
      (fun y hy => by
        simp only [L', Finset.mem_union, not_or] at hy
        exact iht y hy.1.1 _ (hsub.extend
          (Env.okPush hsub.ok.1 hy.2) (Env.okPush hsub.ok.2 hy.1.2)))
      (ihu G' hsub)
  case sngl =>
    intro G p q T hp hq ihp ihq G' hsub
    exact .sngl (ihp G' hsub) (ihq G' hsub)
  case self =>
    intro G p T hp ih G' hsub
    exact .self (ih G' hsub)
  case pathElim =>
    intro G p q a T hp hq ihp ihq G' hsub
    exact .pathElim (ihp G' hsub) (ihq G' hsub)
  case recIntro =>
    intro G p T hp ih G' hsub
    exact .recIntro (ih G' hsub)
  case recElim =>
    intro G p T hp ih G' hsub
    exact .recElim (ih G' hsub)
  case andIntro =>
    intro G p T U hT hU ihT ihU G' hsub
    exact .andIntro (ihT G' hsub) (ihU G' hsub)
  case sub =>
    intro G t T U ht hs iht ihs G' hsub
    exact .sub (iht G' hsub) (ihs G' hsub)
  case typ =>
    intro x fields G A T G' hsub
    exact TypedDef.typ
  case all =>
    intro G T t U V x fields b ht ih G' hsub
    exact TypedDef.all (ih G' hsub)
  case new =>
    intro x fields T b G q A ds p hp tight hdefs ht ihdefs iht G' hsub
    exact TypedDef.new p hp tight (ihdefs G' hsub) (iht G' hsub)
  case path =>
    intro G q T x fields b ht ih G' hsub
    exact TypedDef.path (ih G' hsub)
  case one =>
    intro x fields G d D hd ih G' hsub
    exact TypedDefs.one (ih G' hsub)
  case cons =>
    intro x fields G ds T d D hds hd hno ihds ihd G' hsub
    exact TypedDefs.cons (ihds G' hsub) (ihd G' hsub) hno
  case top => intros; exact .top
  case bot => intros; exact .bot
  case refl => intros; exact .refl
  case trans =>
    intro G S T U h₁ h₂ ih₁ ih₂ G' hsub
    exact .trans (ih₁ G' hsub) (ih₂ G' hsub)
  case andLeft => intros; exact .andLeft
  case andRight => intros; exact .andRight
  case andIntro =>
    intro G S T U h₁ h₂ ih₁ ih₂ G' hsub
    exact .andIntro (ih₁ G' hsub) (ih₂ G' hsub)
  case fld =>
    intro G T U a h ih G' hsub
    exact .fld (ih G' hsub)
  case fldInv =>
    intro G U₁ a T₂ T₁ h hu ih G' hsub
    exact .fldInv (ih G' hsub) hu
  case typ =>
    intro G S₂ S₁ T₁ T₂ A h₁ h₂ ih₁ ih₂ G' hsub
    exact .typ (ih₁ G' hsub) (ih₂ G' hsub)
  case typInvLo =>
    intro G U₁ A S₂ T₂ S₁ T₁ h hu ih G' hsub
    exact .typInvLo (ih G' hsub) hu
  case typInvHi =>
    intro G U₁ A S₂ T₂ S₁ T₁ h hu ih G' hsub
    exact .typInvHi (ih G' hsub) hu
  case allInv =>
    intro G S₁ T₁ S₂ T₂ h ih G' hsub
    exact .allInv (ih G' hsub)
  case snglPQ =>
    intro G p q U T T' hp hq hr ihp ihq G' hsub
    exact .snglPQ (ihp G' hsub) (ihq G' hsub) hr
  case snglQP =>
    intro G p q U T T' hp hq hr ihp ihq G' hsub
    exact .snglQP (ihp G' hsub) (ihq G' hsub) hr
  case selLo =>
    intro G p A S T hp ih G' hsub
    exact .selLo (ih G' hsub)
  case selHi =>
    intro G p A S T hp ih G' hsub
    exact .selHi (ih G' hsub)
  case all =>
    intro G S₂ S₁ T₁ T₂ L hd hc ihd ihc G' hsub
    let L' := (L ∪ G.dom) ∪ G'.dom
    exact .all L' (ihd G' hsub) (fun x hx => by
      simp only [L', Finset.mem_union, not_or] at hx
      exact ihc x hx.1.1 _ (hsub.extend
        (Env.okPush hsub.ok.1 hx.2) (Env.okPush hsub.ok.2 hx.1.2)))
  case t => exact h

end CDot
