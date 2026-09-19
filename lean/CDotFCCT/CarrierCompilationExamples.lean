import CDotFCCT.CarrierTranslation
import CDotFCCT.SharedWitnessRegression

/-!
# Running the carrier pass on the shared-witness source regression

The layout, context guards, intermediate bounds and target derivation below are
all produced by `compileSubtyping`. Only the original DOT derivation is supplied.
The source context is inconsistent; the closed result abstracts its two bindings
as constraints and therefore does not give a closed coercion from Top to Bottom.
-/

set_option autoImplicit false

namespace CDotFCCT.CarrierCompilationExamples

open CDot CTMLCore CTML.Transparent CarrierTranslation

local instance : Signature where
  TypLabel := String
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

def compiled : CompiledSubtyping SharedWitnessRegression.sourceContext .top .bot :=
  (compileSubtyping SharedWitnessRegression.sourceCollapse).get (by decide +kernel)

/-- Each path gets a runtime-type witness as well as both source member witnesses. -/
theorem completeRows : compiled.layout.depth = 6 := by decide +kernel

theorem twoContextGuards : compiled.guards.length = 2 := compiled.contextCode.length

theorem collapse :
    InvertingSubtype ⟨compiled.layout.depth, compiled.guards⟩ WFTy.top WFTy.bottom :=
  (compiled.result.subCode.unique .top) ▸
    (compiled.result.supCode.unique .bot) ▸ compiled.result.proof

theorem noValidEnvironment (env : Indexed.Environment) (index : Nat) :
    ¬ Validates ⟨compiled.layout.depth, compiled.guards⟩ env index :=
  fun valid => CTML.Transparent.noCollapse valid collapse

/-- This checked constraint abstraction is an output of the source compiler. -/
theorem closedTyping : CTML.Transparent.HasType SubtypingContext.empty TypingContext.empty
    (.abs (.var 0)) compiled.closedType := compiled.closedTyping

theorem closedSafe {reached : Syntax.Term}
    (steps : Evaluation.Steps (.abs (.var 0)) reached) :
    Evaluation.Value reached ∨ ∃ next, Evaluation.Step reached next := closedTyping.safe steps

def abstractMember : Typ := .path (.var 2) "X"
def exactA : Typ := .rcd (.typ "A" abstractMember abstractMember)
def aliasContext : Ctx :=
  [(1, .sngl (.var 0)), (0, exactA), (2, .rcd (.typ "X" .bot .top))]

def throughAlias : Core.Typing aliasContext (.var 1) exactA :=
  .sngl (.var .here) (.var (.there (by decide) .here))

def aliasBounds : Core.Subtyping aliasContext (.path (.var 1) "A")
    (.and abstractMember (.path (.var 1) "A")) :=
  .andIntro (.selHi throughAlias) .refl

def compiledAlias : CompiledSubtyping aliasContext (.path (.var 1) "A")
    (.and abstractMember (.path (.var 1) "A")) :=
  (compileSubtyping aliasBounds).get (by decide +kernel)

/-- `q.A` gets a witness even though the source derivation never selects it. -/
theorem aliasOwnerAllocated : (compiledAlias.layout.witness (.var 0) "A").isSome = true := by
  decide +kernel

theorem aliasClosedTyping : CTML.Transparent.HasType SubtypingContext.empty TypingContext.empty
    (.abs (.var 0)) compiledAlias.closedType := compiledAlias.closedTyping

def beforeReplacement : Typ :=
  .rcd (.typ "B" (.and (.path (.var 1) "A") abstractMember) .top)

def afterReplacement : Typ :=
  .rcd (.typ "B" (.and (.path (.var 0) "A") abstractMember) .top)

/-- Replacement occurs in a contravariant bound, underneath an intersection. -/
def replaceLower : Core.Subtyping aliasContext beforeReplacement afterReplacement :=
  .snglPQ (.var .here) (.var (.there (by decide) .here))
    (.rcd (.typLo (.andLeft (.path (fields := [])))))

def replaceLowerBack : Core.Subtyping aliasContext afterReplacement beforeReplacement :=
  .snglQP (.var .here) (.var (.there (by decide) .here))
    (.rcd (.typLo (.andLeft (.path (fields := [])))))

def compiledReplacement : CompiledSubtyping aliasContext beforeReplacement afterReplacement :=
  (compileSubtyping replaceLower).get (by decide +kernel)

def compiledReverse : CompiledSubtyping aliasContext afterReplacement beforeReplacement :=
  (compileSubtyping replaceLowerBack).get (by decide +kernel)

theorem replacementContextGuards : compiledReplacement.guards.length = 3 :=
  compiledReplacement.contextCode.length

theorem replacementClosedTyping :
    CTML.Transparent.HasType SubtypingContext.empty TypingContext.empty
      (.abs (.var 0)) compiledReplacement.closedType := compiledReplacement.closedTyping

theorem reverseClosedTyping :
    CTML.Transparent.HasType SubtypingContext.empty TypingContext.empty
      (.abs (.var 0)) compiledReverse.closedType := compiledReverse.closedTyping

def variance : Core.Subtyping [] (.rcd (.typ "A" .top .bot))
    (.rcd (.typ "A" .bot .top)) := .typ .bot .top

def compiledVariance : CompiledSubtyping [] (.rcd (.typ "A" .top .bot))
    (.rcd (.typ "A" .bot .top)) := (compileSubtyping variance).get (by decide +kernel)

theorem varianceClosedTyping :
    CTML.Transparent.HasType SubtypingContext.empty TypingContext.empty
      (.abs (.var 0)) compiledVariance.closedType := compiledVariance.closedTyping

/-- Unsupported recursive types fail at the encoder instead of receiving a dummy type. -/
theorem rejectsRecursive :
    (compileSubtyping (Core.Subtyping.refl : Core.Subtyping [] (.bnd .top) (.bnd .top))).isNone =
      true := by decide +kernel

end CDotFCCT.CarrierCompilationExamples
