import CDotFCCT.CTML.NegativeSelections

/-!
# A recursive package witness retaining its polymorphic view

The witness satisfies `A = CPS(A → A, Unit)`. The original package contains the
identity function and also has type `∀B. CPS(B → B, Unit)`. Lower-bound refinement
first constructs an abstract selector; its elimination uses the recursive package's
consumer to recover the same `A`. The carrier's lower and upper bounds come from
different intersection components. Both clients retain the original universal view,
close the recursive scope, and return a native Unit record.
-/

set_option autoImplicit false

namespace CDotFCCT.NegativeWitnessExamples

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTML.Coercion

def unitType {n : Nat} : WFTy n := WFTy.cls "Unit"
def alpha {n : Nat} : WFTy (n + 1) := WFTy.var 0 (Nat.zero_lt_succ n)
def interface : CTML.Interface 1 := .payload (WFTy.arrow alpha alpha)
def definition : RecursiveType 0 := recursivePackageDefinition interface unitType
def inside : SubtypingContext := definition.openContext SubtypingContext.empty
def originalType {n : Nat} : WFTy n :=
  WFTy.all (observation (WFTy.arrow alpha alpha) unitType)
def refinedType : WFTy 1 := WFTy.intersection originalType definition.name

def negative : NegativeWitness inside unitType definition.name :=
  .recursivePackage SubtypingContext.empty interface unitType

def originalNegative : NegativeWitness inside unitType originalType :=
  .ofView (.all (.arrow (WFTy.arrow (WFTy.arrow alpha alpha) unitType) unitType))

def unit : Term := .record "Unit" .nil
def identity : Term := .abs (.var 0)
def original : Term := CTML.pack identity
def refined : Term := lowerWitness unit original

theorem originalTyping : HasType inside TypingContext.empty original originalType :=
  .forall _ _ _ (.value (.abs _))
    (.abstraction (.application (.var _ 0 _ .here) (.abstraction (.var _ 0 _ .here))))

theorem originalBodyTyping : HasType inside TypingContext.empty original definition.body :=
  .abstraction (.application (.var _ 0 _ .here) (.abstraction (.var _ 0 _ .here)))

def carrier : WFTy 1 :=
  WFTy.intersection (memberView definition.body WFTy.top unitType)
    (memberView WFTy.bottom definition.body unitType)

theorem preciseCarrier :
    Subtype inside (preciseMember unitType definition.name unitType) carrier :=
  .leInter
    (.trans (preciseMemberOwnView inside unitType definition.name unitType)
      (memberViewVariance (definition.fold SubtypingContext.empty) .leTop))
    (.trans (preciseMemberOwnView inside unitType definition.name unitType)
      (memberViewVariance .botLe (definition.unfold SubtypingContext.empty)))

theorem refinedSelectorTyping : HasType inside TypingContext.empty refined
    (WFTy.intersection originalType (negativeSelector unitType carrier unitType)) :=
  lowerWitness_selectRefinement originalNegative (upper := WFTy.top) .interLeft
    (.record .nil) originalTyping originalBodyTyping

theorem selectedWitness :
    Subtype inside (negativeSelector unitType carrier unitType) definition.name :=
  negativeSelectorWitness (definition.unfold SubtypingContext.empty)
    (definition.fold SubtypingContext.empty) preciseCarrier

theorem refinedTyping : HasType inside TypingContext.empty refined refinedType :=
  refinedSelectorTyping.subsumption (.interMono .refl selectedWitness)

theorem refinedAtWitness : HasType inside TypingContext.empty refined definition.name :=
  refinedTyping.subsumption .interRight

theorem refinedValue : Value refined := .abs _

def discard : Term := .abs unit
def selfClient : Term :=
  .abs (.app (.app (.var 0) (refined.lift 1)) discard)
def selfProgram : Term := .app refined selfClient

theorem selfClientTyping : HasType inside TypingContext.empty selfClient
    (WFTy.arrow (WFTy.arrow definition.name definition.name) unitType) :=
  .abstraction (.application
    ((HasType.application (.var _ 0 _ .here)
      (refinedAtWitness.weakenFront (WFTy.arrow definition.name definition.name)))
        |>.subsumption (definition.unfold SubtypingContext.empty))
    (.abstraction (.record .nil)))

theorem selfProgramTypingInside : HasType inside TypingContext.empty selfProgram unitType :=
  .application (refinedAtWitness.subsumption (definition.unfold SubtypingContext.empty))
    selfClientTyping

theorem selfProgramTyping :
    Recursive.HasType SubtypingContext.empty TypingContext.empty selfProgram unitType :=
  .recursive definition (.native selfProgramTypingInside)

theorem refinedReturns : Returns refined identity :=
  (Returns.pack identity).lowerWitness (.record _ _ .nil) (.abs _)

theorem selfProgramSteps : Steps selfProgram unit := by
  refine (refinedReturns selfClient (.abs _)).trans' (.trans (.appBeta _ _ (.abs _)) ?_)
  change Steps (.app (.app identity ((refined.lift 1).substAt 0 identity)) discard) unit
  rw [Term.lift_substAt_cancel]
  refine .trans (.appHead _ (.appBeta _ _ refinedValue)) ?_
  exact (refinedReturns discard (.abs _)).trans' (.single (.appBeta _ _ (.abs _)))

def originalClient : Term := .abs (.app (.var 0) unit)
def originalProgram : Term := .app refined originalClient

theorem originalProgramTypingInside :
    HasType inside TypingContext.empty originalProgram unitType :=
  .application
    ((refinedTyping.subsumption .interLeft).subsumption
      (show Subtype inside originalType (observation (WFTy.arrow unitType unitType) unitType)
        from Subtype.forallLeft (context := inside)
          (argument := (unitType : WFTy 1))))
    (.abstraction (.application (.var _ 0 _ .here) (.record .nil)))

theorem originalProgramTyping :
    Recursive.HasType SubtypingContext.empty TypingContext.empty originalProgram unitType :=
  .recursive definition (.native originalProgramTypingInside)

theorem originalProgramSteps : Steps originalProgram unit :=
  (refinedReturns originalClient (.abs _)).trans'
    (.trans (.appBeta _ _ (.abs _)) (.single (.appBeta _ _ (.record _ _ .nil))))

def converted : Term := throughNegativeSelector unit original
def convertedProgram : Term := .app converted selfClient

theorem convertedTyping : HasType inside TypingContext.empty converted definition.body :=
  throughNegativeSelectorTyping (otherUpper := WFTy.top) (otherLower := WFTy.bottom)
    (definition.unfold SubtypingContext.empty) (definition.fold SubtypingContext.empty)
    preciseCarrier .interLeft .interRight (.record .nil) originalBodyTyping

theorem convertedProgramTyping :
    Recursive.HasType SubtypingContext.empty TypingContext.empty convertedProgram unitType :=
  .recursive definition (.native (.application convertedTyping selfClientTyping))

theorem convertedProgramSteps : Steps convertedProgram unit :=
  ((memberUpperDirectSteps (.record _ _ .nil) refinedValue).appHead selfClient).trans'
    selfProgramSteps

end CDotFCCT.NegativeWitnessExamples
