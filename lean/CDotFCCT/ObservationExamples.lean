import CDotFCCT.CTML.ObservationViews

/-!
# Retaining observations across repeated member-bound conversions

The answer is `Unit`, while the selected witness is `Top → Top`. The first
conversion preserves two existing observations and adds a selector. The second
retains that selector, including its universal and constraint abstraction, and
adds a view through a wider carrier. Both pass the original identity function.
-/

set_option autoImplicit false

namespace CDotFCCT.ObservationExamples

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTML.Coercion

def unitType : WFTy 0 := WFTy.cls "Unit"
def witness : WFTy 0 := WFTy.arrow WFTy.top WFTy.top
def otherView : WFTy 0 := WFTy.arrow unitType unitType
def carrier : WFTy 0 := preciseMember unitType witness unitType
def widerCarrier : WFTy 0 := memberView witness WFTy.top unitType
def payload : Term := .record "Unit" .nil
def original : Term := .abs (.var 0)
def initial : Term := CTML.pack original
def first : Term := mapLower payload initial
def second : Term := mapLower payload first

def initialType : WFTy 0 :=
  WFTy.intersection (observation witness unitType) (observation otherView unitType)

def firstType : WFTy 0 :=
  WFTy.intersection initialType (selector unitType carrier unitType)

def secondType : WFTy 0 :=
  WFTy.intersection firstType (selector unitType widerCarrier unitType)

def initialShape : Observation unitType initialType := .both (.result _ _) (.result _ _)
def firstShape : Observation unitType firstType :=
  .both initialShape (selectorObservation _ _ _)

theorem payloadTyping : HasType SubtypingContext.empty TypingContext.empty payload unitType :=
  .record .nil

theorem initialTyping : HasType SubtypingContext.empty TypingContext.empty initial initialType :=
  .intersection
    (.abstraction (.application (.var _ 0 _ .here) (.abstraction (.var _ 0 _ .here))))
    (.abstraction (.application (.var _ 0 _ .here) (.abstraction (.var _ 0 _ .here))))

theorem firstTyping : HasType SubtypingContext.empty TypingContext.empty first firstType :=
  mapLower_refinement initialShape
    (preciseMemberOwnView SubtypingContext.empty unitType witness unitType)
    payloadTyping initialTyping (initialTyping.subsumption .interLeft)

theorem secondTyping : HasType SubtypingContext.empty TypingContext.empty second secondType :=
  mapLower_refinement firstShape
    (.refl : CTMLCore.Subtype SubtypingContext.empty widerCarrier widerCarrier)
    payloadTyping firstTyping (firstTyping.subsumption (.trans .interLeft .interLeft))

theorem secondReturns : Returns second original :=
  ((Returns.pack original).mapLower (.record _ _ .nil) (.abs _)).mapLower
    (.record _ _ .nil) (.abs _)

theorem preciseWider : CTMLCore.Subtype SubtypingContext.empty carrier widerCarrier :=
  .trans (preciseMemberOwnView SubtypingContext.empty unitType witness unitType)
    (memberViewVariance .refl .leTop)

def continuation : Term := .abs payload
def program : Term := .app second continuation

/-- Consume the newly added selector with its actual, shared witness. -/
theorem programTyping : HasType SubtypingContext.empty TypingContext.empty program unitType :=
  .application
    ((secondTyping.subsumption .interRight).subsumption
      (selectorInstance (s := SubtypingContext.empty) (data := unitType)
        (carrier := widerCarrier) (answer := unitType) (witness := witness) preciseWider))
    (.abstraction (.record .nil))

/-- The selected value is still the same function after both refinements. -/
theorem programSteps : Steps program payload :=
  (secondReturns continuation (.abs _)).trans' (.single (.appBeta _ _ (.abs _)))

end CDotFCCT.ObservationExamples
