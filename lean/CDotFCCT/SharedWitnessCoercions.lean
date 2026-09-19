import CDotFCCT.SharedWitnessRegression
import CDotFCCT.CTML.Coercions

/-!
# Shared bounds using a precise native record

This checks a different representation against `SharedWitnessRegression`.
One witness and one payload type describe a precise record. Its subtyping
constraint can pass through an opaque type before exposing either member view.
The two views then give explicit identity coercions through that same witness.

The theorem is conditional on a precise-record constraint. Constructing that
constraint and its witness scope from every source context remains a compiler
obligation; this file does not assert the general DOT translation theorem.
-/

set_option autoImplicit false

namespace CDotFCCT.SharedWitnessCoercions

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTML.Coercion

/-- The opaque middle type does not need to be syntactically a member declaration. -/
theorem throughAbstractTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {payload value continuation : Term}
    {data witness opaqueType lower upper otherLower otherUpper answer : WFTy s.typeDepth}
    (precise : Subtype s (preciseMember data witness answer) opaqueType)
    (lowerView : Subtype s opaqueType (memberView lower otherUpper answer))
    (upperView : Subtype s opaqueType (memberView otherLower upper answer))
    (hd : HasType s context payload data) (hv : HasType s context value lower)
    (hk : HasType s context continuation (WFTy.arrow upper answer)) :
    HasType s context (throughMember payload value continuation) answer :=
  throughMemberTyping (.trans precise lowerView) (.trans precise upperView) hd hv hk

def collapse : Term :=
  throughMember SharedWitnessRegression.payload SharedWitnessRegression.payload (.abs (.var 0))

theorem collapseSteps : Steps collapse SharedWitnessRegression.payload :=
  (throughMemberSteps (.record _ _ .nil) (.record _ _ .nil) (.abs _)).trans'
    (.single (.appBeta _ _ (.record _ _ .nil)))

/-- The answer-`Bottom` specialization reaches a value at `Bottom` if both
closed bounds are supplied. -/
theorem noCommonPreciseRowAtBottom (witness : WFTy 0)
    (topView : Subtype SubtypingContext.empty
      (preciseMember WFTy.top witness WFTy.bottom)
      (memberView WFTy.top WFTy.top WFTy.bottom))
    (bottomView : Subtype SubtypingContext.empty
      (preciseMember WFTy.top witness WFTy.bottom)
      (memberView WFTy.bottom WFTy.bottom WFTy.bottom)) : False := by
  have typed : HasType SubtypingContext.empty TypingContext.empty collapse WFTy.bottom :=
    throughMemberTyping topView bottomView
      SharedWitnessRegression.payloadTyping SharedWitnessRegression.payloadTyping
      (.abstraction (.var _ 0 _ .here))
  exact (typed.soundness collapseSteps).1.kind_mem_record (fun _ => ∅)

private def observeBottom : Term := .abs (.app (.var 0) (.var 0))

private theorem observeBottomTyping (answer : WFTy 0) :
    HasType SubtypingContext.empty TypingContext.empty observeBottom
      (WFTy.arrow WFTy.bottom answer) :=
  .abstraction (.application ((HasType.var _ 0 _ .here).subsumption
    (Subtype.botLe (context := SubtypingContext.empty) (type := WFTy.arrow WFTy.top answer)))
      ((HasType.var _ 0 _ .here).subsumption .leTop))

private theorem unitApplicationNoStep {term : Term} :
    ¬ Step (.app SharedWitnessRegression.payload SharedWitnessRegression.payload) term := by
  intro step
  cases step with
  | appHead _ step => exact (Value.record _ _ .nil).not_step step
  | appArg _ step => exact (Value.record _ _ .nil).not_step step

/-- The shared-row contradiction holds at every answer type and with every
inhabited payload type. The proof uses the coercion's exact identity behavior. -/
theorem noCommonPreciseRow (data witness answer : WFTy 0) {payload : Term}
    (hd : HasType SubtypingContext.empty TypingContext.empty payload data) (vd : Value payload)
    (topView : Subtype SubtypingContext.empty (preciseMember data witness answer)
      (memberView WFTy.top WFTy.top answer))
    (bottomView : Subtype SubtypingContext.empty (preciseMember data witness answer)
      (memberView WFTy.bottom WFTy.bottom answer)) : False := by
  have typed := throughMemberTyping topView bottomView hd SharedWitnessRegression.payloadTyping
    (observeBottomTyping answer)
  have steps : Steps (throughMember payload SharedWitnessRegression.payload observeBottom)
      (.app SharedWitnessRegression.payload SharedWitnessRegression.payload) :=
    (throughMemberSteps vd (.record _ _ .nil) (.abs _)).trans'
      (.single (.appBeta _ _ (.record _ _ .nil)))
  rcases (typed.soundness steps).2 with value | ⟨_, step⟩
  · cases value
  · exact unitApplicationNoStep step

def viewContext (witness : WFTy 0) : SubtypingContext :=
  ⟨0, [WFConstraint.constr (preciseMember WFTy.top witness WFTy.bottom)
    (memberView WFTy.top WFTy.top WFTy.bottom),
    WFConstraint.constr (preciseMember WFTy.top witness WFTy.bottom)
      (memberView WFTy.bottom WFTy.bottom WFTy.bottom)]⟩

private theorem viewContextValidates (witness : WFTy 0) (env : KindEnv) :
    (viewContext witness).Validates env := by
  intro guard membership
  rcases List.mem_cons.mp membership with rfl | membership
  · exact (preciseMemberOwnView SubtypingContext.empty WFTy.top witness WFTy.bottom).kinds_mono
      env (SubtypingContext.empty_validates env)
  · have equal := List.mem_singleton.mp membership
    exact equal ▸ ((preciseMemberOwnView SubtypingContext.empty WFTy.top witness WFTy.bottom)
      |>.kinds_mono env (SubtypingContext.empty_validates env))

/-- The explicit conversion is not a native subtyping inversion theorem. The
kind model still rules out a native `Top ≤ Bottom` proof under these assumptions. -/
theorem noNativeCollapse (witness : WFTy 0) :
    ¬ Subtype (viewContext witness) WFTy.top WFTy.bottom := by
  intro impossible
  exact impossible.kinds_mono (fun _ => ∅) (viewContextValidates witness _)
    (a := Kind.fun) (by trivial)

end CDotFCCT.SharedWitnessCoercions
