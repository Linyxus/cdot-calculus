import CDotFCCT.CoreDerivation
import CDotFCCT.CTML.InterfaceIntersections
import CTMLCore.Declarative.KindModel

/-!
# A regression case for bounds exposing two views of one abstract value

The source gives `q.X` two upper bounds, `{A : Top .. Top}` and
`{A : Bottom .. Bottom}`. For `p : q.X`, both views constrain the same `p.A`,
so the context entails `Top <: Bottom`.

Two independent weak existential packages do not preserve this fact: the very
same target term can supply the first package using `Top` and the second using
`Bottom`. No common witness satisfies both. A general translation must synchronize
these views even when they are reached through an abstract member's upper bounds;
merely intersecting separately translated packages is insufficient.

This is a counterexample to that particular interface construction, not an
impossibility theorem for translating DOT to CTML.
-/

set_option autoImplicit false

namespace CDotFCCT.SharedWitnessRegression

open CTMLCore CTML

local instance : CDot.Signature where
  TypLabel := String
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

def topView : CDot.Typ := .rcd (.typ "A" .top .top)
def bottomView : CDot.Typ := .rcd (.typ "A" .bot .bot)

def ownerType : CDot.Typ :=
  .and (.rcd (.typ "X" .bot topView)) (.rcd (.typ "X" .bot bottomView))

def sourceContext : CDot.Ctx := [(1, .path (.var 0) "X"), (0, ownerType)]

def sourceTopView : Core.Typing sourceContext (.var 1) topView :=
  .sub (.var .here) (.selHi
    (.sub (.var (.there (by decide) .here)) .andLeft))

def sourceBottomView : Core.Typing sourceContext (.var 1) bottomView :=
  .sub (.var .here) (.selHi
    (.sub (.var (.there (by decide) .here)) .andRight))

def sourceCollapse : Core.Subtyping sourceContext .top .bot :=
  .trans (.selLo sourceTopView) (.selHi sourceBottomView)

theorem sourceCollapse_checked : CDot.Subtyp sourceContext .top .bot := sourceCollapse.source

def exactMember (endpoint : WFTy 0) : Interface 0 :=
  .bind (.guard (WFConstraint.constr endpoint.weaken (WFTy.var 0 (by decide)))
    (.guard (WFConstraint.constr (WFTy.var 0 (by decide)) endpoint.weaken)
      (.payload WFTy.top)))

def topInstance : Interface.Instance SubtypingContext.empty (exactMember WFTy.top) WFTy.top := by
  change Interface.Instance ⟨0, []⟩ (exactMember WFTy.top) WFTy.top
  refine .bind WFTy.top ?_
  simp only [Interface.instantiate]
  rw [Interface.substAt.eq_2, Interface.substAt.eq_2, Interface.substAt.eq_1]
  change Interface.Instance ⟨0, []⟩
    (.guard (WFConstraint.constr WFTy.top WFTy.top)
      (.guard (WFConstraint.constr WFTy.top WFTy.top) (.payload WFTy.top))) WFTy.top
  exact .guard .refl (.guard .refl (.payload _))

def bottomInstance :
    Interface.Instance SubtypingContext.empty (exactMember WFTy.bottom) WFTy.top := by
  change Interface.Instance ⟨0, []⟩ (exactMember WFTy.bottom) WFTy.top
  refine .bind WFTy.bottom ?_
  simp only [Interface.instantiate]
  rw [Interface.substAt.eq_2, Interface.substAt.eq_2, Interface.substAt.eq_1]
  change Interface.Instance ⟨0, []⟩
    (.guard (WFConstraint.constr WFTy.bottom WFTy.bottom)
      (.guard (WFConstraint.constr WFTy.bottom WFTy.bottom) (.payload WFTy.top))) WFTy.top
  exact .guard .refl (.guard .refl (.payload _))

def payload : Syntax.Term := .record "Unit" .nil
def independentlyPacked : Syntax.Term := pack payload

theorem payloadTyping : HasType SubtypingContext.empty TypingContext.empty payload WFTy.top :=
  (HasType.record .nil).subsumption .leTop

/-- This is the same native target term in both premises, not a pair of different producers. -/
theorem bothPackageViews (answer : WFTy 0) :
    HasType SubtypingContext.empty TypingContext.empty independentlyPacked
      (WFTy.intersection ((exactMember WFTy.top).package answer)
        ((exactMember WFTy.bottom).package answer)) :=
  .intersection (Interface.packTyping topInstance payloadTyping)
    (Interface.packTyping bottomInstance payloadTyping)

theorem noTopBottom : ¬ Subtype SubtypingContext.empty (WFTy.top : WFTy 0) WFTy.bottom := by
  intro impossible
  have membership := impossible.kinds_mono (fun _ => ∅)
    (SubtypingContext.empty_validates _) (a := Syntax.Kind.fun) (by trivial)
  exact membership

/-- The two legal packing instances cannot be replaced by one shared witness. -/
theorem noCommonWitness (witness : WFTy 0)
    (lower : Subtype SubtypingContext.empty WFTy.top witness)
    (upper : Subtype SubtypingContext.empty witness WFTy.bottom) : False :=
  noTopBottom (.trans lower upper)

end CDotFCCT.SharedWitnessRegression
