import CDotFCCT.CarrierRuntime
import CDotFCCT.CarrierCompilationExamples
import CDotFCCT.CTML.MixedCarrierOpening

/-!
# Checking carrier bounds against runtime payloads

The source regression runs the variable compiler on an actual singleton-based
typing derivation. The runtime checks exercise the payload slot and the same
continuation-encoded existential telescope that carries member witnesses.
-/

set_option autoImplicit false

namespace CDotFCCT.CarrierRuntimeExamples

open CDot CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTML.Mixed CarrierTranslation

local instance : Signature where
  TypLabel := String
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

def compiled : CompiledVariable CarrierCompilationExamples.aliasContext 1
    CarrierCompilationExamples.exactA :=
  (compileVariable CarrierCompilationExamples.throughAlias).get (by decide +kernel)

/-- The typing certificate covers the exact output of the existing runtime pass. -/
theorem compiledTyping (answer : WFTy compiled.layout.depth) :
    CTML.Mixed.HasType carrierPolicy ⟨compiled.layout.depth, compiled.guards⟩
      (compiled.layout.runtimeContext CarrierCompilationExamples.aliasContext)
      (TermCPS.compile (runtimeEnvironment CarrierCompilationExamples.aliasContext)
        CarrierCompilationExamples.throughAlias)
      (compiled.interface.package answer) :=
  compiled.runtime_eq CarrierCompilationExamples.throughAlias ▸ compiled.typing answer

/-- Singleton replacement also acts on whole packages, under exactly the source guards. -/
theorem replacementPackageTyping :
    CTML.Mixed.HasType carrierPolicy SubtypingContext.empty TypingContext.empty (.abs (.var 0))
      (CarrierCompilationExamples.compiledReplacement.closedPackageType (WFTy.cls "Unit")) :=
  CarrierCompilationExamples.compiledReplacement.closedPackageTyping _

/-- Field covariance is checked for the same continuation-encoded value packages. -/
theorem fieldPackageTyping :
    CTML.Mixed.HasType carrierPolicy SubtypingContext.empty TypingContext.empty (.abs (.var 0))
      (CarrierCompilationExamples.compiledField.closedPackageType (WFTy.cls "Unit")) :=
  CarrierCompilationExamples.compiledField.closedPackageTyping _

def compiledFieldIntroduction :
    CompiledVariable CarrierCompilationExamples.graphAliasContext 0
      (.rcd (.trm "a" CarrierCompilationExamples.graphMember)) :=
  (compileVariable CarrierCompilationExamples.graphAliasIntroduction).get (by decide +kernel)

/-- The source field-introduction derivation reuses its alias path's generated presence proof. -/
theorem fieldIntroductionTyping (answer : WFTy compiledFieldIntroduction.layout.depth) :
    CTML.Mixed.HasType carrierPolicy
      ⟨compiledFieldIntroduction.layout.depth, compiledFieldIntroduction.guards⟩
      (compiledFieldIntroduction.layout.runtimeContext CarrierCompilationExamples.graphAliasContext)
      (TermCPS.compile (runtimeEnvironment CarrierCompilationExamples.graphAliasContext)
        CarrierCompilationExamples.graphAliasIntroduction)
      (compiledFieldIntroduction.interface.package answer) :=
  compiledFieldIntroduction.runtime_eq CarrierCompilationExamples.graphAliasIntroduction ▸
    compiledFieldIntroduction.typing answer

def unit : Term := .record "Unit" .nil
def identity : Term := .abs (.var 0)
def unitType {depth : Nat} : WFTy depth := WFTy.cls "Unit"
def functionType {depth : Nat} : WFTy depth := WFTy.arrow unitType unitType
def recordType {depth : Nat} : WFTy depth := WFTy.record "run" functionType
def recordFields : TermFields ["run"] := .cons "run" identity .nil (by simp)
def record : Term := .record "Object" recordFields

def singleLayout {depth : Nat} (member payload : WFTy depth) : Layout where
  depth := depth
  labels := ["A"]
  fieldLabels := []
  witness _ _ := some member
  payload _ := some payload
  fieldPresence _ _ := none
  child _ _ := none

def absentLayout : Layout where
  depth := 0
  labels := []
  fieldLabels := ["a"]
  witness _ _ := none
  payload _ := some WFTy.top
  fieldPresence _ _ := some WFTy.bottom
  child _ _ := some WFTy.top

/-- A child bound of Top does not fabricate an absent source field. -/
theorem absentField :
    ¬ InvertingSubtype carrierPolicy SubtypingContext.empty (absentLayout.precise (.var 0))
      (absentLayout.fieldView "a" List.mem_cons_self WFTy.top) :=
  fun typing => CTML.Mixed.noCollapse
    (empty_validates carrierPolicy (fun _ _ => (fun _ => False, fun _ => False)) 0)
    (Layout.fieldPresenceBound (layout := absentLayout) (path := .var 0)
      List.mem_cons_self rfl typing)

def carrier {depth : Nat} (member payload : WFTy depth) : WFTy depth :=
  (singleLayout member payload).precise (.var 0)

def view {depth : Nat} : WFTy depth :=
  let layout := singleLayout (WFTy.top : WFTy depth) WFTy.top
  WFTy.intersection
    ((layout.memberSlot "A" List.mem_cons_self).view WFTy.top WFTy.top (fun _ => WFTy.top))
    (layout.runtimeView recordType)

def guard {depth : Nat} (member payload : WFTy depth) : WFConstraint depth :=
  WFConstraint.constr (carrier member payload) view

def alpha : WFTy 2 := WFTy.var 0 (by decide)
def delta : WFTy 2 := WFTy.var 1 (by decide)
def opened : Layout := singleLayout alpha delta
def inside : SubtypingContext := ⟨2, [guard alpha delta]⟩

/-- The payload is abstract until its own carrier supplies the native record view. -/
theorem payloadRecord : InvertingSubtype carrierPolicy inside delta recordType := by
  apply Layout.payloadBound (layout := opened) (path := .var 0) rfl
  exact (InvertingSubtype.native
    (@CTMLCore.Subtype.hyp inside (guard alpha delta) List.mem_cons_self)).trans
      (.native .interRight)

def interface : CTML.Interface 0 :=
  CarrierLayout.interface (singleLayout (WFTy.top : WFTy 0) WFTy.top).slots Slot.payload view

def clientBody : Term := .app (.proj (.var 0) "run") unit

def clientScope : CarrierLayout.Opening Slot :=
  CarrierLayout.opening (depth := 0) (singleLayout (WFTy.top : WFTy 0) WFTy.top).slots
    view [] TypingContext.empty clientBody unitType

theorem clientScopeTyping :
    CarrierLayout.Opening.Check carrierPolicy
      (singleLayout (WFTy.top : WFTy 0) WFTy.top).slots Slot.payload clientScope :=
  .application (.projection (.subsumption (.native (.var _ _ _ .here)) payloadRecord))
    (.native (.record .nil))

theorem clientTyping :
    InterfaceOpened carrierPolicy interface [] TypingContext.empty clientBody unitType :=
  (CarrierLayout.openComponents_iff _ _ _ _ _ _ _ _ _).mpr clientScopeTyping

theorem supplied : InvertingSubtype carrierPolicy SubtypingContext.empty
    (carrier WFTy.top recordType) view :=
  interIntro
    (Layout.memberView_intro (layout := singleLayout WFTy.top recordType) (path := .var 0)
      List.mem_cons_self rfl (.native .refl) (.native .refl))
    (Layout.runtimeView_intro (layout := singleLayout WFTy.top recordType) (path := .var 0)
      rfl (.native .refl))

def suppliedInstance :
    InterfaceInstance carrierPolicy SubtypingContext.empty interface recordType := by
  exact CarrierLayout.packingInstance (s := SubtypingContext.empty)
    (singleLayout WFTy.top recordType).slots Slot.payload List.mem_cons_self
    (fun slot => ((singleLayout WFTy.top recordType).component (.var 0) slot).getD WFTy.top)
    view supplied

theorem recordTyping :
    CTML.Mixed.HasType carrierPolicy SubtypingContext.empty TypingContext.empty record recordType :=
  .subsumption (.record (.cons (.native (.abstraction (.var _ _ _ .here))) .nil))
    (.native .interRight)

def packed : Term := CTML.packCBV record
def program : Term := .app packed (.abs clientBody)

theorem packedTyping : CTML.Mixed.HasType carrierPolicy SubtypingContext.empty TypingContext.empty
    packed (interface.package unitType) := interfacePackCBVTyping suppliedInstance recordTyping

theorem programTyping :
    CTML.Mixed.HasType carrierPolicy SubtypingContext.empty TypingContext.empty program unitType :=
  CarrierLayout.unpackTyping _ Slot.payload packedTyping clientScopeTyping

theorem programSafe {reached : Term} (steps : Steps program reached) :
    Value reached ∨ ∃ next, Step reached next := programTyping.safe steps

theorem recordValue : Value record := .record _ _ (.cons (.abs _) .nil)

theorem programSteps : Steps program unit := by
  refine .trans (.appHead (.abs clientBody) (CTML.packCBVStep recordValue)) ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  refine .trans (.appBeta _ _ recordValue) ?_
  refine .trans (.appHead unit (.proj recordValue .here)) ?_
  exact .trans (.appBeta _ _ (.record _ _ .nil)) .refl

end CDotFCCT.CarrierRuntimeExamples
