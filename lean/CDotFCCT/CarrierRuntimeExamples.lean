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
  witness _ _ := some member
  payload _ := some payload

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
  CarrierLayout.interface (singleLayout (WFTy.top : WFTy 0) WFTy.top).slots none view

def clientBody : Term := .app (.proj (.var 0) "run") unit

def clientScope : CarrierLayout.Opening (Option String) :=
  CarrierLayout.opening (depth := 0) (singleLayout (WFTy.top : WFTy 0) WFTy.top).slots
    view [] TypingContext.empty clientBody unitType

theorem clientScopeTyping :
    CarrierLayout.Opening.Check carrierPolicy
      (singleLayout (WFTy.top : WFTy 0) WFTy.top).slots none clientScope :=
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
    (singleLayout WFTy.top recordType).slots none List.mem_cons_self
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
  CarrierLayout.unpackTyping _ none packedTyping clientScopeTyping

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
