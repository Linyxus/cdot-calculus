import CDotFCCT.RecordCompilation
import CDotFCCT.CTML.DependentFunctions

/-!
# A dependent function called with the package's existing member witness

The source function has type `(x : {A : Bottom .. Top}) → x.A → x.A`.
Its erased lambda is universally typed over the caller's witness for `x.A`.
This checks the dependent result at an application, without introducing another
independent existential witness for the same argument.
-/

set_option autoImplicit false

namespace CDotFCCT.DependentCompilation

open CTMLCore

local instance : CDot.Signature where
  TypLabel := Nat
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

def sourceParam : CDot.Typ := .rcd (.typ (1 : Nat) .bot .top)

def sourceResult : CDot.Typ :=
  .all (.path (.select (.bound 0) []) (1 : Nat))
    (.path (.select (.bound 1) []) (1 : Nat))

def sourceFunction : CDot.Val :=
  .lambda sourceParam
    (.val (.lambda (.path (.select (.bound 0) []) (1 : Nat))
      (.path (.select (.bound 0) []))))

theorem sourceFunctionTyping (context : CDot.Ctx) :
    CDot.Typed context (.val sourceFunction) (.all sourceParam sourceResult) :=
  .allIntro ∅ (fun _ _ => .allIntro ∅ (fun _ _ => .var .here))

def functionType {n : Nat} : WFTy n :=
  CTML.dependentArrow (CTML.bounds WFTy.bottom WFTy.top) WFTy.top
    (WFTy.arrow (WFTy.var 0 (Nat.zero_lt_succ n)) (WFTy.var 0 (Nat.zero_lt_succ n)))

def functionTerm : CTMLCore.Syntax.Term := .abs (.abs (.var 0))

theorem functionTyping (s : SubtypingContext) (context : TypingContext s.typeDepth) :
    HasType s context functionTerm functionType :=
  CTML.dependentAbstractionTyping (.abstraction (.var _ 0 _ .here))

theorem functionCompilation :
    StaticCompilation.value RecordCompilation.compilationEnv sourceFunction =
      some functionTerm := rfl

def selected (p : CDot.Var) : CDot.Typ := .path (.var p) (1 : Nat)

private theorem sourceApplication {context : CDot.Ctx} {f p : CDot.Var}
    (function : CDot.Typed context (.var f) (.all sourceParam sourceResult))
    (self : CDot.Typed context (.var p) (RecordCompilation.interface p).source) :
    CDot.Typed context (.app (.var f) (.var p)) (.all (selected p) (selected p)) :=
  .allElim function (.sub self
    (.trans .andLeft (.trans .andLeft (.trans .andRight (.typ .bot .top)))))

private theorem sourceUseResult {context : CDot.Ctx} {g p : CDot.Var}
    (function : CDot.Typed context (.var g) (.all (selected p) (selected p)))
    (self : CDot.Typed context (.var p) (RecordCompilation.interface p).source) :
    CDot.Typed context (.app (.var g) ((CDot.Path.var p).selectField "value"))
      RecordCompilation.aliasType.source :=
  let member := RecordCompilation.sourceBounds p self (RecordCompilation.bound p)
    List.mem_cons_self
  .sub (.allElim function
    (.sub (.newElim (.sub self (.trans .andLeft .andRight))) (.selLo member))) (.selHi member)

def sourceBody : CDot.Trm :=
  .letE (.val sourceFunction)
    (.letE (.app (.select (.bound 0) []) (.select (.bound 1) []))
      (.app (.select (.bound 0) []) (.select (.bound 2) ["value"])))

def sourceProgram : CDot.Trm := .letE (.val RecordCompilation.sourceObject) sourceBody

theorem sourceProgramTyping :
    CDot.Typed [] sourceProgram RecordCompilation.aliasType.source := by
  refine .letE ∅ RecordCompilation.sourceObjectTyping (fun p _ => ?_)
  refine .letE {p} (sourceFunctionTyping _) (fun f hf => ?_)
  have self : CDot.Typed
      [(f, .all sourceParam sourceResult), (p, .bnd RecordCompilation.sourceObjectBody)]
      (.var p) (RecordCompilation.interface p).source :=
    .recElim (.var (.there (fun equal => hf (Finset.mem_singleton.mpr equal.symm)) .here))
  refine .letE
    (CDot.Env.dom ([(f, .all sourceParam sourceResult),
      (p, .bnd RecordCompilation.sourceObjectBody)] : CDot.Ctx))
    (sourceApplication (.var .here) self) (fun g hg => ?_)
  exact sourceUseResult (.var .here)
    (self.mono (CDot.Env.Extends.pushRight hg (.all (selected p) (selected p))))

def targetBody : CTMLCore.Syntax.Term :=
  .app
    (.abs (.app
      (.abs (.app (.var 0) (.proj (.var 2) "value")))
      (.app (.var 0) (.var 1))))
    functionTerm

def targetConsumer : CTMLCore.Syntax.Term := .abs targetBody

def targetProgram : CTMLCore.Syntax.Term :=
  .app (CTML.pack RecordCompilation.targetRecord) targetConsumer

theorem compilation :
    StaticCompilation.program RecordCompilation.compilationEnv sourceProgram =
      some targetProgram := rfl

private def memberWitness : WFTy 1 := WFTy.var 0 (by decide)

private def openedContext : SubtypingContext :=
  CTML.assumeMany SubtypingContext.empty.bindType RecordCompilation.guards

private theorem lowerBound :
    Subtype openedContext RecordCompilation.witness.weaken memberWitness :=
  @CTML.assumedGuard SubtypingContext.empty.bindType RecordCompilation.guards
    (WFConstraint.constr RecordCompilation.witness.weaken memberWitness)
    List.mem_cons_self

private theorem upperBound :
    Subtype openedContext memberWitness RecordCompilation.witness.weaken :=
  @CTML.assumedGuard SubtypingContext.empty.bindType RecordCompilation.guards
    (WFConstraint.constr memberWitness RecordCompilation.witness.weaken)
    (List.mem_cons_of_mem _ List.mem_cons_self)

private theorem targetBodyTyping :
    HasType openedContext (TypingContext.empty.bind RecordCompilation.payload)
      targetBody RecordCompilation.witness.weaken := by
  refine .application (.abstraction ?_) (functionTyping _ _)
  refine .application (param := WFTy.arrow memberWitness memberWitness) (.abstraction ?_) ?_
  · refine .subsumption (.application (.var _ 0 _ .here) ?_) upperBound
    refine .subsumption (.projection ?_) lowerBound
    exact (HasType.var _ 2 _ (.there (.there .here))).subsumption
      (.trans .interLeft .interRight)
  · exact CTML.dependentApplyTyping (.var _ 0 _ .here)
      ((HasType.var _ 1 _ (.there .here)).subsumption .leTop)
      (@CTML.boundsSatisfies openedContext WFTy.bottom WFTy.top memberWitness .botLe .leTop)

theorem targetConsumerTyping :
    HasType SubtypingContext.empty TypingContext.empty targetConsumer
      (CTML.consumer RecordCompilation.guards RecordCompilation.payload
        RecordCompilation.witness) :=
  CTML.consumerTyping targetBodyTyping

theorem targetProgramTyping :
    HasType SubtypingContext.empty TypingContext.empty targetProgram RecordCompilation.witness :=
  .application (CTML.packTyping RecordCompilation.targetRecordTyping
    RecordCompilation.guardsSatisfied) targetConsumerTyping

theorem targetProgramSteps :
    CTMLCore.Evaluation.Steps targetProgram RecordCompilation.targetIdentity := by
  refine .trans (.appBeta _ _ (.abs _)) ?_
  refine .trans (.appBeta _ _ RecordCompilation.targetRecordValue) ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  refine .trans (.appArg (.abs _) (.appBeta _ _ RecordCompilation.targetRecordValue)) ?_
  change CTMLCore.Evaluation.Steps
    (.app (.abs (.app (.var 0) (.proj RecordCompilation.targetRecord "value")))
      RecordCompilation.targetIdentity) RecordCompilation.targetIdentity
  refine .trans (.appBeta _ _ (.abs _)) ?_
  refine .trans (.appArg (.abs _) (.proj RecordCompilation.targetRecordValue .here)) ?_
  exact .trans (.appBeta _ _ (.abs _)) .refl

end CDotFCCT.DependentCompilation
