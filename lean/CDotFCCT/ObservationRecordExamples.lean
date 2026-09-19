import CDotFCCT.CTML.ObservationRecords
import CDotFCCT.ObservationExamples

/-! # Repeated field refinement retains the native row and its existing observations -/

set_option autoImplicit false

namespace CDotFCCT.ObservationRecordExamples

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTML.Coercion
open ObservationExamples (unitType witness carrier payload original)

def names : List FieldName := ["selected", "untouched"]
theorem unique : names.Nodup := by decide

def resultTypes (name : FieldName) : WFTy 0 :=
  if name = "selected" then witness else unitType

def types (name : FieldName) : WFTy 0 := observation (resultTypes name) unitType
def shapes (name : FieldName) : Observation unitType (types name) := .result _ _

def record : Term :=
  .record "Container" (.cons "selected" (CTML.pack original)
    (.cons "untouched" (CTML.pack payload) .nil (by decide)) (by decide))

def recordType : WFTy 0 := CTML.ObservationRecord.type "Container" names types
def refined : Term := CTML.ObservationRecord.mapLowerFields "Container" names unique payload record
def refinedTypes : FieldName → WFTy 0 :=
  CTML.ObservationRecord.strengthen types "selected" (selector unitType carrier unitType)

theorem recordTyping : HasType SubtypingContext.empty TypingContext.empty record recordType :=
  .record (.cons
    (.abstraction (.application (.var _ 0 _ .here) (.abstraction (.var _ 0 _ .here))))
    (.cons (.abstraction (.application (.var _ 0 _ .here) (.record .nil))) .nil))

theorem refinedRowTyping : HasType SubtypingContext.empty TypingContext.empty refined
    (CTML.ObservationRecord.type "Container" names refinedTypes) :=
  CTML.ObservationRecord.strengthenedTyping unique (fun name _ => shapes name)
    (field := "selected") (by decide)
    (preciseMemberOwnView SubtypingContext.empty unitType witness unitType)
    (.record .nil) recordTyping
    (.projection (recordTyping.subsumption
      (CTML.ObservationRecord.fieldType (s := SubtypingContext.empty)
        "Container" (names := names) types
        (name := "selected") (by decide))))

theorem refinedTyping : HasType SubtypingContext.empty TypingContext.empty refined
    (WFTy.intersection recordType (WFTy.record "selected" (selector unitType carrier unitType))) :=
  .intersection
    (refinedRowTyping.subsumption (CTML.ObservationRecord.strengthenLe _ _ _ _ _))
    (refinedRowTyping.subsumption
      (CTML.ObservationRecord.strengthenField (s := SubtypingContext.empty)
        "Container" (names := names) types (field := "selected") (by decide) _))

def refinedShapes : ∀ name ∈ names, Observation unitType (refinedTypes name) :=
  CTML.ObservationRecord.strengthenShapes (fun name _ => shapes name) (by decide)
    (selectorObservation unitType carrier unitType)

def secondCarrier : WFTy 0 := preciseMember unitType unitType unitType
def secondTypes : FieldName → WFTy 0 :=
  CTML.ObservationRecord.strengthen refinedTypes "untouched"
    (selector unitType secondCarrier unitType)
def second : Term := CTML.ObservationRecord.mapLowerFields "Container" names unique payload refined

theorem secondRowTyping : HasType SubtypingContext.empty TypingContext.empty second
    (CTML.ObservationRecord.type "Container" names secondTypes) :=
  CTML.ObservationRecord.strengthenedTyping unique refinedShapes
    (field := "untouched") (by decide)
    (preciseMemberOwnView SubtypingContext.empty unitType unitType unitType)
    (.record .nil) refinedRowTyping
    (.projection (refinedRowTyping.subsumption
      (CTML.ObservationRecord.fieldType (s := SubtypingContext.empty)
        "Container" (names := names) refinedTypes (name := "untouched") (by decide))))

theorem secondRetainsFirst : HasType SubtypingContext.empty TypingContext.empty second
    (CTML.ObservationRecord.type "Container" names refinedTypes) :=
  secondRowTyping.subsumption (CTML.ObservationRecord.strengthenLe _ _ _ _ _)

theorem recordValue : Value record := .record _ _ (.cons (.abs _) (.cons (.abs _) .nil))

theorem selectedReturns : Returns (.proj refined "selected") original :=
  CTML.ObservationRecord.projectReturns unique (by decide) (.record _ _ .nil) (.abs _)
    (fun continuation hk => .trans (.appHead _ (.proj recordValue .here))
      (Returns.pack original continuation hk))

theorem untouchedReturns : Returns (.proj refined "untouched") payload :=
  CTML.ObservationRecord.projectReturns unique (by decide)
    (.record _ _ .nil) (.record _ _ .nil)
    (fun continuation hk => .trans (.appHead _ (.proj recordValue (.there .here)))
      (Returns.pack payload continuation hk))

def selectedProgram : Term := .app (.proj refined "selected") (.abs payload)
def untouchedProgram : Term := .app (.proj refined "untouched") original

theorem selectedProgramTyping :
    HasType SubtypingContext.empty TypingContext.empty selectedProgram unitType :=
  .application
    ((HasType.projection (refinedTyping.subsumption .interRight)).subsumption
      (selectorInstance (s := SubtypingContext.empty) (data := unitType)
        (carrier := carrier) (answer := unitType) (witness := witness) .refl))
    (.abstraction (.record .nil))

theorem untouchedProgramTyping :
    HasType SubtypingContext.empty TypingContext.empty untouchedProgram unitType :=
  .application
    (.projection (refinedTyping.subsumption (.trans .interLeft
      (CTML.ObservationRecord.fieldType (s := SubtypingContext.empty)
        "Container" (names := names) types
        (name := "untouched") (by decide)))))
    (.abstraction (.var _ 0 _ .here))

theorem selectedProgramSteps : Steps selectedProgram payload :=
  (selectedReturns _ (.abs _)).trans' (.single (.appBeta _ _ (.abs _)))

theorem untouchedProgramSteps : Steps untouchedProgram payload :=
  (untouchedReturns _ (.abs _)).trans' (.single (.appBeta _ _ (.record _ _ .nil)))

theorem secondSelectedReturns : Returns (.proj second "selected") original :=
  CTML.ObservationRecord.projectReturns unique (by decide)
    (.record _ _ .nil) (.abs _) selectedReturns

theorem secondUntouchedReturns : Returns (.proj second "untouched") payload :=
  CTML.ObservationRecord.projectReturns unique (by decide)
    (.record _ _ .nil) (.record _ _ .nil) untouchedReturns

def secondSelectedProgram : Term := .app (.proj second "selected") (.abs payload)
def secondUntouchedProgram : Term := .app (.proj second "untouched") original

/-- The first field's selector survives refinement of the second field. -/
theorem secondSelectedProgramTyping :
    HasType SubtypingContext.empty TypingContext.empty secondSelectedProgram unitType :=
  .application
    ((HasType.projection (secondRetainsFirst.subsumption
      (CTML.ObservationRecord.strengthenField (s := SubtypingContext.empty)
        "Container" (names := names) types (field := "selected") (by decide) _))).subsumption
      (selectorInstance (s := SubtypingContext.empty) (data := unitType)
        (carrier := carrier) (answer := unitType) (witness := witness) .refl))
    (.abstraction (.record .nil))

/-- Consume the new selector with the second field's existing witness. -/
theorem secondUntouchedProgramTyping :
    HasType SubtypingContext.empty TypingContext.empty secondUntouchedProgram unitType :=
  .application
    ((HasType.projection (secondRowTyping.subsumption
      (CTML.ObservationRecord.strengthenField (s := SubtypingContext.empty)
        "Container" (names := names) refinedTypes
        (field := "untouched") (by decide) _))).subsumption
      (selectorInstance (s := SubtypingContext.empty) (data := unitType)
        (carrier := secondCarrier) (answer := unitType) (witness := unitType) .refl))
    (.abstraction (.var _ 0 _ .here))

theorem secondSelectedProgramSteps : Steps secondSelectedProgram payload :=
  (secondSelectedReturns _ (.abs _)).trans' (.single (.appBeta _ _ (.abs _)))

theorem secondUntouchedProgramSteps : Steps secondUntouchedProgram payload :=
  (secondUntouchedReturns _ (.abs _)).trans' (.single (.appBeta _ _ (.record _ _ .nil)))

end CDotFCCT.ObservationRecordExamples
