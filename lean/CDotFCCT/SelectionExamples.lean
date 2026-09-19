import CDotFCCT.CTML.Selections

/-! # A closed, terminating check of constraint-abstracted member selection -/

set_option autoImplicit false

namespace CDotFCCT.SelectionExamples

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTML.Coercion

def dataType : WFTy 0 := WFTy.cls "Unit"
def witness : WFTy 0 := WFTy.arrow WFTy.top WFTy.top
def carrier : WFTy 0 := preciseMember dataType witness witness
def payload : Term := .record "Unit" .nil
def identity : Term := .abs (.var 0)
def program : Term := throughSelector payload identity identity

/-- All guards are discharged in the empty context, using the actual precise carrier. -/
theorem programTyping : HasType SubtypingContext.empty TypingContext.empty program witness :=
  throughSelectorTyping (s := SubtypingContext.empty) (context := TypingContext.empty)
    (data := dataType) (carrier := carrier) (witness := witness)
    (preciseMemberOwnView SubtypingContext.empty dataType witness witness)
    (preciseMemberOwnView SubtypingContext.empty dataType witness witness)
    (.refl : CTMLCore.Subtype SubtypingContext.empty carrier carrier)
    (.record .nil) (.abstraction (.var _ 0 _ .here)) (.abstraction (.var _ 0 _ .here))

/-- The selector passes the original function through both views and returns it. -/
theorem programSteps : Steps program identity :=
  (throughSelectorSteps (.record _ _ .nil) (.abs _) (.abs _)).trans'
    (.single (.appBeta _ _ (.abs _)))

end CDotFCCT.SelectionExamples
