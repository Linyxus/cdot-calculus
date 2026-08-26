import CDot.Substitution

/-!
# Context transport

A typing environment maps every source binding to a typing derivation in a
target context.  The fundamental transport theorem subsumes the specialized
`open_env_rules` argument from the Coq development.
-/

namespace CDot

variable [Signature]

structure TypingEnv (E E' : Ctx) : Prop where
  sourceOk : Env.Ok E
  targetOk : Env.Ok E'
  lookup : ∀ {x T}, Env.Binds x T E → Typed E' (.var x) T

theorem TypingEnv.push {E E' : Ctx} (h : TypingEnv E E')
    {x : Var} {T : Typ} (hxE : Env.Fresh x E) (hxE' : Env.Fresh x E') :
    TypingEnv (E.push x T) (E'.push x T) := by
  refine ⟨Env.okPush h.sourceOk hxE, Env.okPush h.targetOk hxE', ?_⟩
  intro y U hb
  cases hb with
  | here => exact .var .here
  | there hne hb =>
      exact (h.lookup hb).mono (.pushRight hxE' T)

theorem Typed.transport {E E' : Ctx} {t : Trm} {T : Typ}
    (h : Typed E t T) (he : TypingEnv E E') : Typed E' t T := by
  revert E'
  apply Typed.rec
    (motive_1 := fun E t T _ => ∀ E', TypingEnv E E' → Typed E' t T)
    (motive_2 := fun x fs E d D _ => ∀ E', TypingEnv E E' → TypedDef x fs E' d D)
    (motive_3 := fun x fs E ds T _ => ∀ E', TypingEnv E E' → TypedDefs x fs E' ds T)
    (motive_4 := fun E S T _ => ∀ E', TypingEnv E E' → Subtyp E' S T)
  case var => intro x T E hb E' he; exact he.lookup hb
  case allIntro =>
    intro E S t T L hbody ih E' he
    let L' := (L ∪ E.dom) ∪ E'.dom
    exact .allIntro L' (fun x hx => by
      simp only [L', Finset.mem_union, not_or] at hx
      exact ih x hx.1.1 _ (he.push hx.1.2 hx.2))
  case allElim =>
    intro E p S T q hp hq ihp ihq E' he
    exact .allElim (ihp E' he) (ihq E' he)
  case newIntro =>
    intro p A E T ds L hdefs hself ihdefs ihself E' he
    let L' := (L ∪ E.dom) ∪ E'.dom
    exact .newIntro L'
      (fun x hx => by
        simp only [L', Finset.mem_union, not_or] at hx
        exact ihdefs x hx.1.1 _ (he.push hx.1.2 hx.2))
      (fun x hx => by
        simp only [L', Finset.mem_union, not_or] at hx
        exact ihself x hx.1.1 _ (he.push hx.1.2 hx.2))
  case newElim =>
    intro E p a T hp ih E' he
    exact .newElim (ih E' he)
  case rcdIntro =>
    intro E T p a hp ih E' he
    exact .rcdIntro (ih E' he)
  case letE =>
    intro E t T U u L ht hbody iht ihbody E' he
    let L' := (L ∪ E.dom) ∪ E'.dom
    exact .letE L' (iht E' he) (fun x hx => by
      simp only [L', Finset.mem_union, not_or] at hx
      exact ihbody x hx.1.1 _ (he.push hx.1.2 hx.2))
  case caseE =>
    intro E p S q U A T t₂ t₁ L hp hq hbody ht₂ ihp ihq ihbody iht₂ E' he
    let L' := (L ∪ E.dom) ∪ E'.dom
    exact .caseE L' (ihp E' he) (ihq E' he)
      (fun x hx => by
        simp only [L', Finset.mem_union, not_or] at hx
        exact ihbody x hx.1.1 _ (he.push hx.1.2 hx.2))
      (iht₂ E' he)
  case sngl =>
    intro E p q T hp hq ihp ihq E' he
    exact .sngl (ihp E' he) (ihq E' he)
  case self => intro E p T hp ih E' he; exact .self (ih E' he)
  case pathElim =>
    intro E p q a T hp hq ihp ihq E' he
    exact .pathElim (ihp E' he) (ihq E' he)
  case recIntro => intro E p T hp ih E' he; exact .recIntro (ih E' he)
  case recElim => intro E p T hp ih E' he; exact .recElim (ih E' he)
  case andIntro =>
    intro E p T U hT hU ihT ihU E' he
    exact .andIntro (ihT E' he) (ihU E' he)
  case sub =>
    intro E t S T ht hs iht ihs E' he
    exact .sub (iht E' he) (ihs E' he)
  case typ => intros; exact .typ
  case all =>
    intro E T t U V x fs b ht ih E' he
    exact .all (ih E' he)
  case new =>
    intro x fs T b E q A ds p hp ht hdefs htag ihdefs ihtag E' he
    exact .new p hp ht (ihdefs E' he) (ihtag E' he)
  case path =>
    intro E q T x fs b ht ih E' he
    exact .path (ih E' he)
  case one =>
    intro x fs E d D hd ih E' he
    exact .one (ih E' he)
  case cons =>
    intro x fs E ds T d D hds hd hno ihds ihd E' he
    exact .cons (ihds E' he) (ihd E' he) hno
  case top => intros; exact .top
  case bot => intros; exact .bot
  case refl => intros; exact .refl
  case trans =>
    intro E S T U hST hTU ihST ihTU E' he
    exact .trans (ihST E' he) (ihTU E' he)
  case andLeft => intros; exact .andLeft
  case andRight => intros; exact .andRight
  case andIntro =>
    intro E S T U hST hSU ihST ihSU E' he
    exact .andIntro (ihST E' he) (ihSU E' he)
  case fld =>
    intro E T U a h ih E' he
    exact .fld (ih E' he)
  case fldInv =>
    intro E U a T₂ T₁ h hu ih E' he
    exact .fldInv (ih E' he) hu
  case typ =>
    intro E S₂ S₁ T₁ T₂ A hS hT ihS ihT E' he
    exact .typ (ihS E' he) (ihT E' he)
  case typInvLo =>
    intro E U A S₂ T₂ S₁ T₁ h hu ih E' he
    exact .typInvLo (ih E' he) hu
  case typInvHi =>
    intro E U A S₂ T₂ S₁ T₁ h hu ih E' he
    exact .typInvHi (ih E' he) hu
  case allInv =>
    intro E S₁ T₁ S₂ T₂ h ih E' he
    exact .allInv (ih E' he)
  case snglPQ =>
    intro E p q U T T' hp hq hr ihp ihq E' he
    exact .snglPQ (ihp E' he) (ihq E' he) hr
  case snglQP =>
    intro E p q U T T' hp hq hr ihp ihq E' he
    exact .snglQP (ihp E' he) (ihq E' he) hr
  case selLo =>
    intro E p A S T hp ih E' he
    exact .selLo (ih E' he)
  case selHi =>
    intro E p A S T hp ih E' he
    exact .selHi (ih E' he)
  case all =>
    intro E S₂ S₁ T₁ T₂ L hdom hbody ihdom ihbody E' he
    let L' := (L ∪ E.dom) ∪ E'.dom
    exact .all L' (ihdom E' he) (fun x hx => by
      simp only [L', Finset.mem_union, not_or] at hx
      exact ihbody x hx.1.1 _ (he.push hx.1.2 hx.2))
  case t => exact h

theorem TypingEnv.openSelf {G : Ctx} {x : Var} {T : Typ}
    (hok : Env.Ok (G.push x (T.open x))) :
    TypingEnv (G.push x (T.open x)) (G.push x (.bnd T)) := by
  refine ⟨hok, ?_, ?_⟩
  · simpa [Env.Ok, Env.push] using hok
  · intro y U hb
    cases hb with
    | here => simpa only [Trm.var, Typ.openRec_eq_openRecPath_var] using
        Typed.recElim (Typed.var (G := G.push x (.bnd T)) (T := .bnd T) .here)
    | there hne hb => exact .var (.there hne hb)

theorem Typed.openSelfContext {G : Ctx} {x : Var} {S : Typ}
    {t : Trm} {T : Typ} (h : Typed (G.push x (S.open x)) t T)
    (hok : Env.Ok (G.push x (S.open x))) :
    Typed (G.push x (.bnd S)) t T :=
  h.transport (.openSelf hok)

theorem TypedDefs.transport {z : Var} {fields : Fields} {E E' : Ctx}
    {ds : Defs} {T : Typ} (h : TypedDefs z fields E ds T)
    (he : TypingEnv E E') : TypedDefs z fields E' ds T := by
  revert E'
  apply TypedDefs.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun z fs E d D _ => ∀ E', TypingEnv E E' → TypedDef z fs E' d D)
    (motive_3 := fun z fs E ds T _ => ∀ E', TypingEnv E E' → TypedDefs z fs E' ds T)
    (motive_4 := fun _ _ _ _ => True)
  case typ => intros; exact .typ
  case all =>
    intro E S t U V z fs b ht iht E' he
    exact .all (ht.transport he)
  case new =>
    intro z fs T b E q A ds p hp ht hdefs htag ihdefs ihtag E' he
    exact .new p hp ht (ihdefs E' he) (htag.transport he)
  case path =>
    intro E q T z fs b ht iht E' he
    exact .path (ht.transport he)
  case one =>
    intro z fs E d D hd ih E' he
    exact .one (ih E' he)
  case cons =>
    intro z fs E ds T d D hds hd hno ihds ihd E' he
    exact .cons (ihds E' he) (ihd E' he) hno
  case t => exact h
  all_goals intros; trivial

theorem TypedDefs.openSelfContext {G : Ctx} {z x : Var} {S T : Typ}
    {fields : Fields} {ds : Defs}
    (h : TypedDefs z fields (G.push x (S.open x)) ds T)
    (hok : Env.Ok (G.push x (S.open x))) :
    TypedDefs z fields (G.push x (.bnd S)) ds T :=
  h.transport (.openSelf hok)

end CDot
