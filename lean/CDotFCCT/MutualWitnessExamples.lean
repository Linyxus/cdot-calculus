import CDotFCCT.CoreDerivation
import CDotFCCT.CTML.RecursivePackages
import CTMLCore.Declarative.IndexedFundamental

/-!
# A core-DOT object with mutually recursive type members

The source members are `A = {left : self.A} & {right : self.B}` and
`B = self.A → self.B`. Both equations have self and cross references.
The target witness check uses native field and function payloads in one system
of recursive CPS packages. A closed target program constructs both packages with Z,
projects native fields, calls through the cross-member types, and reduces to Unit.
Another exports and reopens the whole group through one shared existential telescope.
This checks the witness representation, not a general compilation of source derivations.
-/

set_option autoImplicit false

namespace CDotFCCT.MutualWitnessExamples

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTML.Coercion

local instance : CDot.Signature where
  TypLabel := Nat
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

def selected (self label : Nat) : CDot.Typ := .path (.select (.bound self) []) label

def sourceA : CDot.Typ :=
  .and (.rcd (.trm "left" (selected 0 1))) (.rcd (.trm "right" (selected 0 2)))

def sourceB : CDot.Typ := .all (selected 0 1) (selected 1 2)

def sourceBody : CDot.Typ :=
  .and (.and (.rcd (.typ (0 : Nat) .top .top)) (.rcd (.typ (1 : Nat) sourceA sourceA)))
    (.rcd (.typ (2 : Nat) sourceB sourceB))

def sourceObject : CDot.Val :=
  .new (.select (.bound 0) []) (0 : Nat) sourceBody
    (.cons (.cons (.cons .nil (.typ (0 : Nat) .top)) (.typ (1 : Nat) sourceA))
      (.typ (2 : Nat) sourceB))

def sourceDerivation : Core.Typing [] (.val sourceObject) (.bnd sourceBody) :=
  .newIntro ∅
    (fun _ _ => .cons (.cons (.one .typ) .typ
      (by simp [CDot.Defs.Hasnt, CDot.Defs.get, CDot.Defs.openRec, CDot.Def.openRec,
        CDot.Def.label])) .typ
      (by simp [CDot.Defs.Hasnt, CDot.Defs.get, CDot.Defs.openRec, CDot.Def.openRec,
        CDot.Def.label]
          decide))
    (fun _ _ => .sub (.sub (.var .here) .top)
      (.selLo (.sub (.var .here) (.trans .andLeft .andLeft))))

theorem sourceTyping : CDot.Typed [] (.val sourceObject) (.bnd sourceBody) :=
  sourceDerivation.source

def first : WFTy 2 := WFTy.var 0 (by decide)
def second : WFTy 2 := WFTy.var 1 (by decide)
def unitType {n : Nat} : WFTy n := WFTy.cls "Unit"

def firstPayload : WFTy 2 :=
  WFTy.intersection (WFTy.record "left" first) (WFTy.record "right" second)

def secondPayload : WFTy 2 := WFTy.arrow first second

def interfaces : Fin 2 → CTML.Interface 2 := fun index =>
  if index = 0 then .payload firstPayload else .payload secondPayload

def system : RecursiveSystem 0 2 := recursivePackages interfaces unitType
def context : SubtypingContext := system.openContext SubtypingContext.empty

def firstWitness : PackageWitness context unitType first :=
  .mutual SubtypingContext.empty interfaces unitType 0

def secondWitness : PackageWitness context unitType second :=
  .mutual SubtypingContext.empty interfaces unitType 1

theorem equationsValid (env : Indexed.Environment) (n : Nat) :
    context.IndexedValidates (system.indexedEnvironment env) n :=
  system.indexedValidates (SubtypingContext.empty_indexedValidates env n)

def unit : Term := .record "Unit" .nil

/-- `Z (λself. λk. k (λa. self))` constructs the second package. -/
def secondBuilder : Term := .abs (.abs (.app (.var 0) (.abs (.var 2))))
def secondPackage : Term := .fix secondBuilder

/-- The first package contains an ordinary record of both recursive package values. -/
def firstBuilder : Term := .abs (.abs (.app (.var 0)
  (.record "DOT.Pair" (.cons "left" (.var 1)
    (.cons "right" secondPackage .nil (by decide)) (by decide)))))
def firstPackage : Term := .fix firstBuilder

def discard : Term := .abs unit
def client : Term := .abs (.app (.proj (.var 0) "right")
  (.abs (.app (.app (.var 0) (.proj (.var 1) "left")) discard)))
def program : Term := .app firstPackage client

theorem secondBuilderTyping (gamma : TypingContext 2) :
    HasType context gamma secondBuilder (WFTy.arrow (system.body 1) (system.body 1)) :=
  .abstraction (.abstraction (.application (.var _ 0 _ .here)
    (.abstraction ((HasType.var _ 2 _ (.there (.there .here))).subsumption
      (system.fold SubtypingContext.empty 1)))))

theorem secondPackageTyping (gamma : TypingContext 2) :
    HasType context gamma secondPackage second :=
  (HasType.fixpoint (secondBuilderTyping gamma)).subsumption
    (system.fold SubtypingContext.empty 1)

theorem firstBuilderTyping (gamma : TypingContext 2) :
    HasType context gamma firstBuilder (WFTy.arrow (system.body 0) (system.body 0)) :=
  .abstraction (.abstraction (.application (.var _ 0 _ .here)
    ((HasType.record (.cons
      ((HasType.var _ 1 _ (.there .here)).subsumption (system.fold SubtypingContext.empty 0))
      (.cons (secondPackageTyping _) .nil))).subsumption
        (.leInter (.trans .interLeft .interRight) .interRight))))

theorem firstPackageTyping (gamma : TypingContext 2) :
    HasType context gamma firstPackage first :=
  (HasType.fixpoint (firstBuilderTyping gamma)).subsumption
    (system.fold SubtypingContext.empty 0)

theorem clientTyping : HasType context TypingContext.empty client
    (WFTy.arrow firstPayload unitType) :=
  .abstraction (.application
    ((HasType.projection ((HasType.var _ 0 _ .here).subsumption .interRight)).subsumption
      (system.unfold SubtypingContext.empty 1))
    (.abstraction (.application
      ((HasType.application (.var _ 0 _ .here)
        (.projection ((HasType.var _ 1 _ (.there .here)).subsumption .interLeft))).subsumption
          (system.unfold SubtypingContext.empty 1))
      (.abstraction (.record .nil)))))

theorem programTypingInside : HasType context TypingContext.empty program unitType :=
  .application ((firstPackageTyping _).subsumption (system.unfold SubtypingContext.empty 0))
    clientTyping

/-- Both recursive names are closed by the checked simultaneous rule. -/
theorem programTyping :
    Recursive.HasType SubtypingContext.empty TypingContext.empty program unitType :=
  .recursiveSystem system (.native programTypingInside)

theorem programSafe {reached : Term} (steps : Steps program reached) :
    Value reached ∨ ∃ next, Step reached next := programTyping.safe steps

def secondFunction : Term := .abs (delayedFix secondBuilder)
def payload : Term := .record "DOT.Pair"
  (.cons "left" (delayedFix firstBuilder)
    (.cons "right" (unfoldFix secondBuilder) .nil (by decide)) (by decide))

theorem payloadValue : Value payload :=
  .record _ _ (.cons (.abs _) (.cons (.abs _) .nil))

theorem secondReturns : Returns secondPackage secondFunction := by
  intro consumer value
  refine .trans (.appHead _ (.fixUnfold (.abs _))) ?_
  refine .trans (.unfoldFix_beta value) ?_
  refine .trans (.appHead _ (.appBeta _ _ (.abs _))) ?_
  exact .single (.appBeta _ _ value)

theorem firstReturns : Returns firstPackage payload := by
  intro consumer value
  refine .trans (.appHead _ (.fixUnfold (.abs _))) ?_
  refine .trans (.unfoldFix_beta value) ?_
  refine .trans (.appHead _ (.appBeta _ _ (.abs _))) ?_
  refine .trans (.appBeta _ _ value) ?_
  exact .single (.appArg value (.recordField
    (.tail (.abs _) (.head (.fixUnfold (.abs _))))))

theorem programSteps : Steps program unit := by
  refine (firstReturns client (.abs _)).trans' ?_
  refine .trans (.appBeta _ _ payloadValue) ?_
  refine .trans (.appHead _ (.proj payloadValue (.there .here))) ?_
  refine .trans (.unfoldFix_beta (.abs _)) ?_
  refine .trans (.appHead _ (.appBeta _ _ (.abs _))) ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  refine .trans (.appHead _ (.appArg (.abs _) (.proj payloadValue .here))) ?_
  refine .trans (.appHead _ (.appBeta _ _ (.abs _))) ?_
  change Steps (.app (delayedFix secondBuilder) discard) unit
  refine .trans (.delayedFix_beta (.abs _)) ?_
  refine (secondReturns discard (.abs _)).trans' ?_
  exact .single (.appBeta _ _ (.abs _))

def exportedInterface : CTML.Interface 0 := CTML.RecursivePackage.interface system first
def exportedProducer : Term := CTML.pack firstPackage
def exportedBody : Term := .app (.var 0) client
def exportedClient : Term := .abs exportedBody
def exportedProgram : Term := .app exportedProducer exportedClient

/-- The generic constructor generates and seals both witnesses and all four equation guards. -/
theorem exportedProducerTyping : Recursive.HasType SubtypingContext.empty TypingContext.empty
    exportedProducer (exportedInterface.package unitType) :=
  CTML.RecursivePackage.packTyping (s := SubtypingContext.empty) (context := TypingContext.empty)
    (term := firstPackage) (payload := first) system unitType (.native (firstPackageTyping _))

theorem exportedBodyTyping : HasType context (TypingContext.empty.bind first)
    exportedBody unitType :=
  .application ((HasType.var _ 0 _ .here).subsumption (system.unfold SubtypingContext.empty 0))
    (clientTyping.weakenFront first)

/-- The consumer uses abstract names and only the equations exported in the package. -/
theorem exportedClientTyping : HasType SubtypingContext.empty TypingContext.empty exportedClient
    (exportedInterface.consumer unitType) := by
  change HasType SubtypingContext.empty TypingContext.empty (.abs exportedBody)
    (exportedInterface.consumer unitType)
  apply CTML.Interface.consumerTyping (s := SubtypingContext.empty) (context := TypingContext.empty)
    (body := exportedBody) (answer := unitType) exportedInterface
  change HasType ⟨2, context.assumptions.reverse⟩ (TypingContext.empty.bind first)
    exportedBody unitType
  exact exportedBodyTyping.mapAssumptions
    (fun guard member => @Subtype.hyp ⟨2, context.assumptions.reverse⟩ guard
      (List.mem_reverse.mpr member))

theorem exportedProgramTyping : Recursive.HasType SubtypingContext.empty TypingContext.empty
    exportedProgram unitType := .application exportedProducerTyping (.native exportedClientTyping)

theorem exportedProgramSteps : Steps exportedProgram unit := by
  refine (Returns.pack firstPackage exportedClient (.abs _)).trans' ?_
  refine .trans (.appArg (.abs _) (.fixUnfold (.abs _))) ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  change Steps (.app (unfoldFix firstBuilder) client) unit
  cases programSteps with
  | trans step rest => exact step.deterministic (.appHead client (.fixUnfold (.abs _))) ▸ rest

end CDotFCCT.MutualWitnessExamples
