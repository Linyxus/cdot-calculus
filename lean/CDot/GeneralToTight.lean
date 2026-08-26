import CDot.ReplacementTyping
import CDot.GADTRules

/-!
# General typing to tight typing

In an inert context, general typing and subtyping derivations can be converted
to their tight counterparts.  This ports `cdot/GeneralToTight.v`.
-/

namespace CDot

variable [Signature]

theorem ReplTyp.aliasSubtypes {G : Ctx} {p q : Path} {T U V : Typ}
    (hpq : PreciseTyping3 G p (.sngl q)) (hq : PreciseTyping3 G q V)
    (hr : ReplTyp p q T U) :
    TightSubtyp G T U ∧ TightSubtyp G U T :=
  ⟨.snglPQ hpq hq hr, .snglQP hpq hq hr.swap⟩

theorem TightTyped.selectSubtypes {G : Ctx} {p : Path}
    {A : Signature.TypLabel} {S U : Typ} (hi : Inert G)
    (h : TightTyped G (.path p) (.rcd (.typ A S U))) :
    TightSubtyp G (.path p A) U ∧ TightSubtyp G S (.path p A) := by
  obtain ⟨T, hp, hTU, hST⟩ := (h.pathReplacement hi).rcdToPrecise hi
  exact ⟨.trans (.selHi hp) hTU, .trans hST (.selLo hp)⟩

theorem TightTyped.precise2Exists {G : Ctx} {p : Path} {T : Typ}
    (hi : Inert G) (h : TightTyped G (.path p) T) :
    ∃ U, PreciseTyping2 G p U := by
  obtain ⟨U, hp⟩ := (h.pathReplacement hi).preciseExists
  exact hp.precise2Exists

theorem TightTyped.snglSubtypes {G : Ctx} {p q : Path}
    {T U S : Typ} (hi : Inert G)
    (hp : TightTyped G (.path p) (.sngl q))
    (hq : TightTyped G (.path q) S) (hr : ReplTyp p q T U) :
    TightSubtyp G T U ∧ TightSubtyp G U T := by
  obtain ⟨V, hq₂⟩ := hq.precise2Exists hi
  let hq₃ : PreciseTyping3 G q V := .precise hq₂
  have hp' := hp.pathReplacement hi
  obtain ⟨r, W, hpr, hr₃, hqr⟩ := hp'.snglToInvertible hi hq₃
  rcases hpr.snglPreciseCases hi hr₃ with
    ⟨r', hpr', hr'r⟩ | rfl
  · have hprr : PreciseTyping3 G p (.sngl r) := by
      rcases hr'r with rfl | hr'r
      · exact hpr'
      · exact hpr'.snglTrans3 hr'r
    rcases hqr with rfl | hqr
    · exact hr.aliasSubtypes hprr hr₃
    · obtain ⟨X, hprX, hXq⟩ := hr.insert r
      have hpPair := hprX.aliasSubtypes hprr hr₃
      have hqPair := hXq.swap.aliasSubtypes hqr hr₃
      exact ⟨.trans hpPair.1 hqPair.2, .trans hqPair.1 hpPair.2⟩
  · rcases hqr with rfl | hqr
    · have heq := hr.eq_of_paths_eq rfl
      cases heq
      exact ⟨.refl, .refl⟩
    · have hpair := hr.swap.aliasSubtypes hqr hr₃
      exact ⟨hpair.2, hpair.1⟩

theorem Subtyp.toTight {G : Ctx} {S T : Typ}
    (h : Subtyp G S T) (hi : Inert G) : TightSubtyp G S T := by
  apply Subtyp.rec
    (motive_1 := fun G t T _ => Inert G → TightTyped G t T)
    (motive_2 := fun _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
    (motive_4 := fun G S T _ => Inert G → TightSubtyp G S T)
  case var => intro x T G hb hi; exact .var hb
  case allIntro => intro G T t U L hbody ihbody hi; exact .allIntro L hbody
  case allElim =>
    intro G p S T q hp hq ihp ihq hi
    exact .allElim (ihp hi) (ihq hi)
  case newIntro =>
    intro p A G T ds L hdefs hself ihdefs ihself hi
    exact .newIntro L hdefs hself
  case newElim => intro G p a T h ih hi; exact .newElim (ih hi)
  case rcdIntro => intro G T p a h ih hi; exact .rcdIntro (ih hi)
  case letE =>
    intro G t T U u L ht hbody ih ihbody hi
    exact .letE L (ih hi) hbody
  case caseE =>
    intro G p S q U A T t₂ t₁ L hp hq hbody ht₂ ihp ihq ihbody iht₂ hi
    exact .caseE L (ihp hi) (ihq hi) hbody (iht₂ hi)
  case sngl =>
    intro G p q T hp hq ihp ihq hi
    exact .sngl (ihp hi) (ihq hi)
  case self => intro G p T h ih hi; exact .self (ih hi)
  case pathElim =>
    intro G p q a T hp hq ihp ihq hi
    exact .pathElim (ihp hi) (ihq hi)
  case recIntro => intro G p T h ih hi; exact .recIntro (ih hi)
  case recElim => intro G p T h ih hi; exact .recElim (ih hi)
  case andIntro =>
    intro G p T U hT hU ihT ihU hi
    exact .andIntro (ihT hi) (ihU hi)
  case sub =>
    intro G t S T ht hs iht ihs hi
    exact .sub (iht hi) (ihs hi)
  case new => intros; trivial
  case path => intros; trivial
  case one => intros; trivial
  case cons => intros; trivial
  case top => intros; exact .top
  case bot => intros; exact .bot
  case refl => intros; exact .refl
  case trans =>
    intro G S T U hST hTU ihST ihTU hi
    exact .trans (ihST hi) (ihTU hi)
  case andLeft => intros; exact .andLeft
  case andRight => intros; exact .andRight
  case andIntro =>
    intro G S T U hST hSU ihST ihSU hi
    exact .andIntro (ihST hi) (ihSU hi)
  case fld => intro G T U a h ih hi; exact .fld (ih hi)
  case fldInv =>
    intro G U a T₂ T₁ h hu ih hi
    exact (ih hi).trmInvertUnique hi hu
  case typ => intros; trivial
  case typ =>
    intro G S₂ S₁ T₁ T₂ A hLo hHi ihLo ihHi hi
    exact .typ (ihLo hi) (ihHi hi)
  case typInvLo =>
    intro G U A S₂ T₂ S₁ T₁ h hu ih hi
    exact ((ih hi).typInvertUnique hi hu).1
  case typInvHi =>
    intro G U A S₂ T₂ S₁ T₁ h hu ih hi
    exact ((ih hi).typInvertUnique hi hu).2
  case allInv =>
    intro G S₁ T₁ S₂ T₂ h ih hi
    exact ((ih hi).allInvert hi).1
  case snglPQ =>
    intro G p q V T T' hp hq hr ihp ihq hi
    exact ((ihp hi).snglSubtypes hi (ihq hi) hr).1
  case snglQP =>
    intro G p q V T T' hp hq hr ihp ihq hi
    exact ((ihp hi).snglSubtypes hi (ihq hi) hr.swap).2
  case selLo =>
    intro G p A S T hp ih hi
    exact ((ih hi).selectSubtypes hi).2
  case selHi =>
    intro G p A S T hp ih hi
    exact ((ih hi).selectSubtypes hi).1
  case all => intros; trivial
  case all =>
    intro G S₂ S₁ T₁ T₂ L hdom hbody ih ihbody hi
    exact .all L (ih hi) hbody
  case t => exact h
  all_goals assumption

theorem Typed.toTight {G : Ctx} {t : Trm} {T : Typ}
    (h : Typed G t T) (hi : Inert G) : TightTyped G t T := by
  apply Typed.rec
    (motive_1 := fun G t T _ => Inert G → TightTyped G t T)
    (motive_2 := fun _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True)
  case var => intro x T G hb hi; exact .var hb
  case allIntro => intro G T t U L hbody ihbody hi; exact .allIntro L hbody
  case allElim =>
    intro G p S T q hp hq ihp ihq hi
    exact .allElim (ihp hi) (ihq hi)
  case newIntro =>
    intro p A G T ds L hdefs hself ihdefs ihself hi
    exact .newIntro L hdefs hself
  case newElim => intro G p a T h ih hi; exact .newElim (ih hi)
  case rcdIntro => intro G T p a h ih hi; exact .rcdIntro (ih hi)
  case letE =>
    intro G t T U u L ht hbody ih ihbody hi
    exact .letE L (ih hi) hbody
  case caseE =>
    intro G p S q U A T t₂ t₁ L hp hq hbody ht₂ ihp ihq ihbody iht₂ hi
    exact .caseE L (ihp hi) (ihq hi) hbody (iht₂ hi)
  case sngl =>
    intro G p q T hp hq ihp ihq hi
    exact .sngl (ihp hi) (ihq hi)
  case self => intro G p T h ih hi; exact .self (ih hi)
  case pathElim =>
    intro G p q a T hp hq ihp ihq hi
    exact .pathElim (ihp hi) (ihq hi)
  case recIntro => intro G p T h ih hi; exact .recIntro (ih hi)
  case recElim => intro G p T h ih hi; exact .recElim (ih hi)
  case andIntro =>
    intro G p T U hT hU ihT ihU hi
    exact .andIntro (ihT hi) (ihU hi)
  case sub =>
    intro G t S T ht hs iht ihs hi
    exact .sub (iht hi) (hs.toTight hi)
  case new => intros; trivial
  case path => intros; trivial
  case one => intros; trivial
  case cons => intros; trivial
  case top => intros; trivial
  case bot => intros; trivial
  case refl => intros; trivial
  case trans => intros; trivial
  case andLeft => intros; trivial
  case andRight => intros; trivial
  case andIntro => intros; trivial
  case fld => intros; trivial
  case fldInv => intros; trivial
  case typ => intros; trivial
  case typ => intros; trivial
  case typInvLo => intros; trivial
  case typInvHi => intros; trivial
  case allInv => intros; trivial
  case snglPQ => intros; trivial
  case snglQP => intros; trivial
  case selLo => intros; trivial
  case selHi => intros; trivial
  case all => intros; trivial
  case all => intros; trivial
  case t => exact h
  all_goals assumption

theorem Typed.precise3Exists {G : Ctx} {p : Path} {T : Typ}
    (h : Typed G (.path p) T) (hi : Inert G) :
    ∃ U, PreciseTyping3 G p U := by
  obtain ⟨U, hp⟩ := (h.toTight hi).precise2Exists hi
  exact ⟨U, .precise hp⟩

theorem Typed.pathAllToPrecise {G : Ctx} {p : Path} {S T : Typ}
    (h : Typed G (.path p) (.all S T)) (hi : Inert G) :
    ∃ S' T', ∃ L : Vars, PreciseTyping3 G p (.all S' T') ∧
      Subtyp G S S' ∧
      (∀ y, y ∉ L → Subtyp (G.push y S) (T'.open y) (T.open y)) := by
  obtain ⟨S', T', L, hp, hdom, hbody⟩ :=
    ((h.toTight hi).pathReplacement hi).allToPrecise hi
  exact ⟨S', T', L, hp, hdom.toGeneral, hbody⟩

theorem Typed.valAllToLambda {G : Ctx} {v : Val} {S T : Typ}
    (h : Typed G (.val v) (.all S T)) (hi : Inert G) :
    ∃ L : Vars, ∃ S' t, v = .lambda S' t ∧ Subtyp G S S' ∧
      (∀ y, y ∉ L → Typed (G.push y S) (t.open y) (T.open y)) := by
  exact ((h.toTight hi).valReplacement hi).lambdaExists hi

theorem Subtyp.allInvertGeneral {G : Ctx} {S₁ T₁ S₂ T₂ : Typ}
    (h : Subtyp G (.all S₁ T₁) (.all S₂ T₂)) (hi : Inert G) :
    Subtyp G S₂ S₁ ∧ ∃ L : Vars, ∀ x, x ∉ L →
      Subtyp (G.push x S₂) (T₁.open x) (T₂.open x) := by
  obtain ⟨hdom, L, hbody⟩ := (h.toTight hi).allInvert hi
  exact ⟨hdom.toGeneral, L, hbody⟩

end CDot
