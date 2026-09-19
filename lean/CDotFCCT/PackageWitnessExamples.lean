import CDotFCCT.CTML.PackageWitnesses
import CDotFCCT.NegativeWitnessExamples

/-!
# A recursive member packaged with its negative representation

The producer chooses the recursive name `A = CPS(A → A, Unit)` and its actual
consumer, proves their equivalence, and exports them in one CPS telescope. The
client obtains its negative-witness evidence from that telescope's assumptions.
The payload uses native record fields throughout.
-/

set_option autoImplicit false

namespace CDotFCCT.PackageWitnessExamples

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTML.Coercion
open NegativeWitnessExamples (unitType alpha originalType definition inside unit original)

def row {n : Nat} : WFTy (n + 1) :=
  WFTy.intersection (WFTy.record "value" originalType)
    (WFTy.record "consume" (WFTy.arrow alpha unitType))

def lower {n : Nat} : WFConstraint (n + 1) := WFConstraint.constr originalType alpha

def rest {n : Nat} : CTML.Interface (n + 1) := .guard lower (.payload row)

def interface {n : Nat} : CTML.Interface n := CTML.Interface.bindPackageWitness unitType rest

def consume : Term := .abs (.app (.var 0) (.abs unit))

def record : Term :=
  .record "DOT.Package" (.cons "value" original
    (.cons "consume" consume .nil (by decide)) (by decide))

def producer : Term := CTML.pack record

def representation : PackageWitness inside unitType definition.name :=
  .recursive SubtypingContext.empty NegativeWitnessExamples.interface unitType

theorem lowerSatisfied : Subtype inside originalType definition.name :=
  .trans (show Subtype inside originalType definition.body from
    Subtype.forallLeft (context := inside) (argument := definition.name))
    (definition.fold SubtypingContext.empty)

def instanceAtWitness :
    CTML.Interface.Instance inside (rest.instantiate definition.name)
      (row.instantiate definition.name) := by
  change CTML.Interface.Instance inside ((rest (n := 1)).instantiate definition.name)
    ((row (n := 1)).instantiate definition.name)
  simp only [rest, CTML.Interface.instantiate, CTML.Interface.substAt]
  exact .guard lowerSatisfied (.payload _)

theorem recordTypingInside :
    HasType inside TypingContext.empty record (row.instantiate definition.name) :=
  (HasType.record (.cons NegativeWitnessExamples.originalTyping
    (.cons (.abstraction (.application
      ((HasType.var _ 0 _ .here).subsumption (definition.unfold SubtypingContext.empty))
      (.abstraction (.record .nil)))) .nil))).subsumption
    (.leInter (.trans .interLeft .interRight) .interRight)

theorem producerTypingInside :
    HasType inside TypingContext.empty producer (interface.package unitType) :=
  CTML.Interface.packTyping
    (CTML.Interface.bindPackageWitnessInstance representation instanceAtWitness) recordTypingInside

theorem producerTyping : Recursive.HasType SubtypingContext.empty TypingContext.empty producer
    (interface.package unitType) :=
  .recursive definition (.native producerTypingInside)

def opened : SubtypingContext :=
  (CTML.Interface.packageScope SubtypingContext.empty unitType).assume lower

def abstractRepresentation : PackageWitness opened unitType alpha :=
  (CTML.Interface.packageEvidence SubtypingContext.empty unitType).weakenAssumption lower

theorem lowerHyp : Subtype opened originalType alpha :=
  @Subtype.hyp opened lower List.mem_cons_self

def body : Term :=
  .app (.proj (.var 0) "consume") (lowerWitness unit (.proj (.var 0) "value"))

def client : Term := .abs body
def program : Term := .app producer client

theorem bodyTyping : HasType opened (TypingContext.empty.bind row) body unitType :=
  .application (.projection ((HasType.var _ 0 _ .here).subsumption .interRight))
    (lowerWitnessTyping abstractRepresentation.negative
      (.trans (preciseMemberOwnView opened unitType alpha unitType)
        (memberViewVariance lowerHyp .refl)) (.record .nil)
      (.projection ((HasType.var _ 0 _ .here).subsumption .interLeft)))

theorem clientTyping : HasType SubtypingContext.empty TypingContext.empty client
    (interface.consumer unitType) := by
  refine CTML.Interface.bindPackageWitness_consumerTyping ?_
  simp only [rest, CTML.Interface.liftAt, CTML.Interface.Opened]
  exact bodyTyping

theorem programTyping :
    Recursive.HasType SubtypingContext.empty TypingContext.empty program unitType :=
  .application producerTyping (.native clientTyping)

theorem recordValue : Value record := .record _ _ (.cons (.abs _) (.cons (.abs _) .nil))

theorem programSteps : Steps program unit := by
  refine (Returns.pack record client (.abs _)).trans' (.trans (.appBeta _ _ recordValue) ?_)
  change Steps (.app (.proj record "consume") (lowerWitness unit (.proj record "value"))) unit
  refine .trans (.appHead _ (.proj recordValue (.there .here))) ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  change Steps (.app (lowerWitness unit (.proj record "value")) (.abs unit)) unit
  refine (lowerWitness_stepsOfInput (.record _ _ .nil)
    (.single (.proj recordValue .here)) (.abs _) (.abs _)).trans' ?_
  exact (Returns.pack _ _ (.abs _)).trans' (.single (.appBeta _ _ (.abs _)))

end CDotFCCT.PackageWitnessExamples
