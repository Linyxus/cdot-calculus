import CDotFCCT.CarrierAliasCompilation

/-!
# A source field alias preserves its child's existing witnesses

The constructor pass consumes an actual core-DOT object derivation and generates
the target proof. A closed target client then runs the same compiled constructor,
projects its field and receives the original child value through the anchor.
-/

set_option autoImplicit false

namespace CDotFCCT.CarrierAliasExamples

open CDot CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTML.Mixed CarrierTranslation
open CTML.Mixed.CarrierFieldInvariant
open CarrierAliasCompilation

local instance : Signature where
  TypLabel := String
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

def context : Ctx := [(0, .top), (1, .rcd (.typ "Tag" .top .top))]
def body : Typ := .rcd (.trm "a" (.sngl (.var 0)))
def source : Trm := sourceObject (.var 1) "Tag" body "a" 0

def sourceDerivation : Core.Typing context source (.bnd body) :=
  .newIntro {0, 1}
    (fun self fresh => by
      have different : (0 : Var) ≠ self := by
        intro equal
        subst self
        simp at fresh
      exact .one (.path (.var (.there different .here))))
    (fun self fresh => by
      have different : (1 : Var) ≠ self := by
        intro equal
        subst self
        simp at fresh
      exact .sub (.sub (.var .here) .top)
        (.selLo (.var (.there different (.there (by decide) .here)))))

theorem sourceTyping : CDot.Typed context source (.bnd body) := sourceDerivation.source

/-- No target witness or subtyping proof is supplied to this computation. -/
def compiled : Result context 0 := (compile sourceDerivation).get (by decide +kernel)

def env : TermCPS.Env := environment context (.var 1) "Tag" body "a" 0
def constructor : Term := TermCPS.compile env sourceDerivation

theorem compiledTyping (answer : WFTy compiled.childCompilation.layout.depth) :
    CTML.Mixed.HasType carrierPolicy
      ⟨compiled.childCompilation.layout.depth, compiled.childCompilation.guards⟩
      (compiled.childCompilation.layout.runtimeContext context) constructor
      (compiled.computationType (env.fieldName "a") answer) :=
  compiled.typing sourceDerivation answer

theorem originalGuards : compiled.childCompilation.guards.length = context.length :=
  compiled.childCompilation.contextCode.length

theorem ordinaryField : carrierPolicy (env.fieldName "a") = false :=
  TermCPS.programEnv_ordinary _ _ _

/-- The actual source program constructs, projects and returns the existing variable's type. -/
def projectedDerivation : Core.Typing context
    (projectedSource (.var 1) "Tag" body "a" 0) .top :=
  .letE {0, 1} sourceDerivation (fun name fresh => by
    have different : (0 : Var) ≠ name := by
      intro equal
      subst name
      simp at fresh
    exact .sngl
      (.newElim (.recElim (.var .here) :
        Core.Typing (context.push name (.bnd body)) (.var name) body))
      (.var (.there different .here)))

theorem projectedSourceTyping : CDot.Typed context
    (projectedSource (.var 1) "Tag" body "a" 0) .top := projectedDerivation.source

def projectedCompiled : ProjectedResult context 0 .top :=
  (compileProjected projectedDerivation).get (by decide +kernel)

theorem projectedCompiledTyping (answer : WFTy projectedCompiled.childCompilation.layout.depth) :
    CTML.Mixed.HasType carrierPolicy
      ⟨projectedCompiled.childCompilation.layout.depth, projectedCompiled.childCompilation.guards⟩
      (projectedCompiled.childCompilation.layout.runtimeContext context)
      (TermCPS.compile (projectedEnvironment context (.var 1) "Tag" body "a" 0)
        projectedDerivation)
      (projectedCompiled.childCompilation.interface.package answer) :=
  projectedCompiled.typing projectedDerivation answer

/-- The projection retains the original source variable's complete generated package. -/
theorem projectedSameInterface :
    (projectedCompiled.childCompilation.interface.consumer WFTy.top).raw =
      (compiled.childCompilation.interface.consumer WFTy.top).raw := by
  with_unfolding_all rfl

def projectedDifferentResult : Core.Typing context
    (projectedSource (.var 1) "Tag" body "a" 0) (.and .top .top) :=
  .sub projectedDerivation (.andIntro .refl .refl)

/-- This pass checks exact result agreement even when another source result is equivalent. -/
theorem rejectsDifferentResult : compileProjected projectedDifferentResult = none := by
  decide +kernel

def unit : Term := .record "Unit" .nil
def unitType {depth : Nat} : WFTy depth := WFTy.cls "Unit"
def support : List (Option String) := [none, some "Tag"]
def fixed {depth : Nat} : Option String → WFTy depth := fun _ => unitType
def payload {depth : Nat} : WFTy depth := objectPayload support none fixed "f" unitType
def continuation : Term := .abs (fieldCall (.var 0) "f" (.abs (.var 0)))
def program : Term := .app (.abs (.app constructor continuation)) unit

/-- A concrete realization of the generated anchor consumes the original payload type. -/
theorem constructorTyping :
    CTML.Mixed.HasType carrierPolicy SubtypingContext.empty
      (TypingContext.empty.bind unitType) constructor
      (WFTy.arrow (WFTy.arrow payload unitType) unitType) := by
  change CTML.Mixed.HasType carrierPolicy _ _
    (.abs (.app (.var 0) (aliasObject "f" 1))) _
  exact .abstraction (.application (.native (.var _ _ _ .here))
    (aliasObjectTyping (s := SubtypingContext.empty) support none List.mem_cons_self
      fixed "f" unitType (.there .here)))

theorem continuationTyping :
    CTML.Mixed.HasType carrierPolicy SubtypingContext.empty
      (TypingContext.empty.bind unitType) continuation (WFTy.arrow payload unitType) :=
  .abstraction (fieldCallTyping (s := SubtypingContext.empty)
    support none List.mem_cons_self fixed "f" unitType
    (.native (.var _ _ _ .here)) (.native (.abstraction (.var _ _ _ .here))))

theorem programTyping :
    CTML.Mixed.HasType carrierPolicy SubtypingContext.empty TypingContext.empty program unitType :=
  .application (.abstraction (.application constructorTyping continuationTyping))
    (.native (.record .nil))

theorem programSafe {reached : Term} (steps : Steps program reached) :
    Value reached ∨ ∃ next, Step reached next := programTyping.safe steps

theorem programSteps : Steps program unit := by
  refine .trans (.appBeta _ _ (.record _ _ .nil)) ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  refine .trans (.appArg (.abs _) (.fixUnfold (.abs _))) ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  refine .trans (.appHead (.abs (.var 0))
    (.projHead "f" (.unfoldFix_beta (.record _ _ .nil)))) ?_
  refine .trans (.appHead (.abs (.var 0))
    (.projHead "f" (.appHead TermCPS.unit (.appBeta _ _ (.abs _))))) ?_
  refine .trans (.appHead (.abs (.var 0))
    (.projHead "f" (.appBeta _ _ (.record _ _ .nil)))) ?_
  refine .trans (.appHead (.abs (.var 0))
    (.proj (.record _ _ (.cons (.abs _) .nil)) .here)) ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  exact .single (.appBeta _ _ (.record _ _ .nil))

end CDotFCCT.CarrierAliasExamples
