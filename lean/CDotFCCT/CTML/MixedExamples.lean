import CDotFCCT.CTML.MixedSafety
import CDotFCCT.CTML.RecordGuardAnalysis
import CTMLCore.Declarative.RecursiveRecordSystemExamples

/-!
# Executing ordinary record recursion with ghost component inversion

The scalar program combines a directly record-recursive carrier with a cast
defined by arbitrary constraint abstraction and ghost component inversion. The
producer discharges the cast's ghost bound using the recursive equation. A second
program reuses the native mutual-record execution with two arrow-free equations.
These are target soundness regressions, not a full source translation theorem.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.MixedExamples

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

abbrev policy := RecordGuardAnalysis.policy

def selfType : WFTy 1 := WFTy.var 0 (by decide)

/-- The recursive occurrence is guarded directly by an ordinary native record. -/
def nodeDefinition : Mixed.Definition policy 0 :=
  .record "next" (by decide) (WFTy.union (WFTy.cls "Unit") selfType)

def context : SubtypingContext := nodeDefinition.native.openContext SubtypingContext.empty

def unit : Term := .record "Unit" .nil

def node : Term := .record "Node" (.cons "next" unit .nil (by decide))

def identity : Term := .abs (.var 0)

def ghostBound {n : Nat} (source target : WFTy n) : WFConstraint n :=
  WFConstraint.constr (WFTy.record "$member" source) (WFTy.record "$member" target)

/-- The bound is abstract here; cancellation is permitted only at the ghost label. -/
theorem castTyping {s : SubtypingContext} (ctx : TypingContext s.typeDepth)
    (source target : WFTy s.typeDepth) :
    Mixed.HasType policy s ctx identity
      (WFTy.constrained (ghostBound source target) (WFTy.arrow source target)) :=
  .constrained _ _ _ _ (.value (.abs _))
    (.abstraction ((Mixed.HasType.native (HasType.var _ 0 _ .here)).subsumption
      (.inverse (by decide) (.native (@Subtype.hyp (s.assume (ghostBound source target))
        (ghostBound source target) List.mem_cons_self)))))

theorem nodeTyping : Mixed.HasType policy context TypingContext.empty node selfType :=
  .native ((HasType.record (.cons ((HasType.record .nil).subsumption .leUnionLeft) .nil))
    |>.subsumption (.trans .interRight (nodeDefinition.native.fold SubtypingContext.empty)))

def view : WFTy 1 := WFTy.record "next" WFTy.top

/-- The constructor proves the cast's ghost bound; no assumed component inequality is needed. -/
theorem castBound : Subtype context (ghostBound selfType view).sub
    (ghostBound selfType view).sup :=
  .record (.trans (nodeDefinition.native.unfold SubtypingContext.empty) (.record .leTop))

theorem openedCastTyping :
    Mixed.HasType policy context TypingContext.empty identity (WFTy.arrow selfType view) :=
  (castTyping TypingContext.empty selfType view).subsumption
    (.native (.constrainedLeft _ _ castBound))

def program : Term := .proj (.app identity node) "next"

theorem programTyping :
    Mixed.HasType policy SubtypingContext.empty TypingContext.empty program WFTy.top :=
  .recursive nodeDefinition (.projection (.application openedCastTyping nodeTyping))

theorem programSteps : Steps program unit :=
  .trans (.projHead "next" (.appBeta _ _
    (.record _ _ (.cons (.record _ _ .nil) .nil))))
    (.trans (.proj (.record _ _ (.cons (.record _ _ .nil) .nil)) .here) .refl)

theorem programSafe {reached : Term} (steps : Steps program reached) :
    Value reached ∨ ∃ next, Step reached next := programTyping.safe steps

/-- The previously problematic constrained cycle is legal with an ordinary record guard. -/
theorem constrainedCycleConsistent :
    ¬ Mixed.InvertingSubtype policy
      (RecordGuardAnalysis.constrainedNode.native.openContext SubtypingContext.empty)
      WFTy.top WFTy.bottom :=
  RecordGuardAnalysis.constrainedNode.noCollapse

namespace Mutual

abbrev system := RecursiveRecordSystemExamples.system

/-- Both source field names are ordinary guards under the same policy as the ghost cast. -/
theorem ordinary : ∀ index, policy (system.field index) = false := by
  intro index
  change policy (if index.val = 0 then "next" else "back") = false
  split <;> decide

abbrev program := RecursiveRecordSystemExamples.program

abbrev unit := RecursiveRecordSystemExamples.unit

theorem programTyping :
    Mixed.HasType policy SubtypingContext.empty TypingContext.empty program WFTy.top :=
  .recursiveRecordSystem system ordinary (.native RecursiveRecordSystemExamples.programInScope)

/-- The mixed extension executes with exactly the native evaluator and native proof. -/
theorem programSteps : Steps program unit := RecursiveRecordSystemExamples.programSteps

theorem programSafe {reached : Term} (steps : Steps program reached) :
    Value reached ∨ ∃ next, Step reached next := programTyping.safe steps

end Mutual

end CDotFCCT.CTML.MixedExamples
