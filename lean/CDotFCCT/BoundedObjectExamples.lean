import CDotFCCT.BoundedObjectCompilation
import CDotFCCT.RecursiveAliasExamples

/-! # Requested bounds on a constructor with self and mutual alias cycles -/

set_option autoImplicit false

namespace CDotFCCT.BoundedObjectExamples

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation
open RecursiveAliasExamples (sourceObject sourceBody sourceA sourceC answer env observer result)
open BoundedObjectCompilation (returnSelf)

local instance : CDot.Signature where
  TypLabel := Nat
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

/-- Two conjuncts expose A with different bounds; B and C retain their mutual dependency. -/
def requested : CDot.Typ :=
  .and (.rcd (.typ (1 : Nat) .bot .top))
    (.and (.rcd (.typ (1 : Nat) sourceA sourceA))
      (.and (.rcd (.typ (2 : Nat) .bot .top)) (.rcd (.typ (3 : Nat) sourceC sourceC))))

def sourceDerivation : Core.Typing []
    (.letE (.val sourceObject) returnSelf) (.bnd requested) :=
  .letE ∅ RecursiveAliasExamples.sourceDerivation (fun _ _ =>
    .recIntro (.sub (.recElim (.var .here))
      (.andIntro (.trans (.trans .andLeft (.trans .andLeft .andRight)) (.typ .bot .top))
        (.andIntro (.trans .andLeft (.trans .andLeft .andRight))
          (.andIntro (.trans (.trans .andLeft .andRight) (.typ .bot .top)) .andRight)))))

theorem sourceTyping : CDot.Typed []
    (.letE (.val sourceObject) returnSelf) (.bnd requested) := sourceDerivation.source

def generated : Option (BoundedObjectCompilation.Result answer env sourceDerivation) :=
  match BoundedObjectCompilation.compile 100 answer env sourceDerivation with
  | .ok checked => some checked
  | _ => none

/-- The input contains only the source derivation, never target witnesses or bound proofs. -/
def compiled : BoundedObjectCompilation.Result answer env sourceDerivation :=
  generated.get (by decide +kernel)

theorem sharesA : (compiled.guards.get ⟨1, by decide +kernel⟩).sub =
    (compiled.guards.get ⟨2, by decide +kernel⟩).sup := by decide +kernel

theorem allBoundsDischarged :
    CTML.Satisfies (compiled.members.system.openContext SubtypingContext.empty) compiled.guards :=
  compiled.evidence

def program : Term := .app (TermCPS.compile env sourceDerivation) observer

def expectedGuards : List (WFConstraint 4) :=
  let a := WFTy.var 1 (by decide)
  let b := WFTy.var 2 (by decide)
  let c := WFTy.var 3 (by decide)
  let aBody := WFTy.intersection a (WFTy.arrow RecursiveAliasExamples.firstConsumer answer)
  [WFConstraint.constr (WFTy.arrow WFTy.top answer) a,
   WFConstraint.constr a (WFTy.arrow WFTy.bottom answer),
   WFConstraint.constr aBody a, WFConstraint.constr a aBody,
   WFConstraint.constr (WFTy.arrow WFTy.top answer) b,
   WFConstraint.constr b (WFTy.arrow WFTy.bottom answer),
   WFConstraint.constr b c, WFConstraint.constr c b]

theorem consumerComputed :
    (CTML.Interface.closeGuards compiled.only.entries.length compiled.guards
      TypeOnlyCompilation.payload).consumer answer =
    (CTML.Interface.closeGuards 4 expectedGuards TypeOnlyCompilation.payload).consumer answer := by
  decide +kernel

theorem observerTyping : HasType SubtypingContext.empty TypingContext.empty observer
    ((CTML.Interface.closeGuards compiled.only.entries.length compiled.guards
      TypeOnlyCompilation.payload).consumer answer) := by
  rw [consumerComputed]
  refine CTML.Interface.consumerTyping (s := SubtypingContext.empty)
    (context := TypingContext.empty) _ ?_
  exact HasType.application (.var _ 0 _ .here) ((HasType.record .nil).subsumption .leTop)

theorem programTyping :
    Recursive.HasType SubtypingContext.empty TypingContext.empty program answer :=
  .application compiled.typing (.native observerTyping)

theorem programSafe {reached : Term} (steps : Steps program reached) :
    Value reached ∨ ∃ next, Step reached next := programTyping.safe steps

theorem programSteps : Steps program result := by
  change Steps (.app BoundedObjectCompilation.repack observer) result
  refine .trans (.appBeta _ _ (.abs _)) ?_
  refine .trans (.appArg (.abs _) (.fixUnfold (.abs _))) ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  change Steps (.app (unfoldFix (.abs (.abs result))) TermCPS.unit) result
  refine .trans (.unfoldFix_beta (.record _ _ .nil)) ?_
  refine .trans (.appHead _ (.appBeta _ _ (.abs _))) ?_
  exact .single (.appBeta _ _ (.record _ _ .nil))

end CDotFCCT.BoundedObjectExamples
