import CDotFCCT.TypeOnlyCompilation
import CDotFCCT.CTML.DischargeSearch

/-!
# Constructing recursive objects at requested bounded interfaces

This constructor case accepts a source derivation for `let x = new … in x` at a
recursive type. It reads the requested member bounds from that type, generates
the simultaneous witnesses from the actual definitions, and proves the bounds
before packing them. The result types the exact output of `TermCPS.compile`.

The current case supports type-only objects and the alias type grammar in
`RecursiveAliasTranslation`. Unsupported source forms and unsuccessful proof
search return `failed`; fuel exhaustion remains `fuelOut`. No target evidence is
an input. This is a constructor phase, not the full derivation translation.
-/

set_option autoImplicit false

namespace CDotFCCT.BoundedObjectCompilation

open CTMLCore CTMLCore.Syntax
open RecursiveAliasTranslation TypeOnlyCompilation

variable [CDot.Signature]

/-- All bounds on a member use the same name, including bounds from distinct conjuncts. -/
def bounds {depth size : Nat} (labels : Fin size → CDot.Signature.TypLabel)
    (fieldName : CDot.Signature.TrmLabel → String) (answer : WFTy depth) :
    CDot.Typ → Option (List (WFConstraint (depth + size)))
  | .top => some []
  | .and left right => do
      return (← bounds labels fieldName answer left) ++ (← bounds labels fieldName answer right)
  | .rcd (.typ label lower upper) => do
      let index ← memberIndex labels label
      let lower ← type labels fieldName answer 0 lower
      let upper ← type labels fieldName answer 0 upper
      return [WFConstraint.constr (lower.denote names (answer.weakenBy size)) (names index),
        WFConstraint.constr (names index) (upper.denote names (answer.weakenBy size))]
  | _ => none

def returnSelf : CDot.Trm := .path (.select (.bound 0) [])

def repack : Term := .abs (.app (.abs (.app (.var 1) (.var 0))) objectThunk)

theorem compile_eq {definitions : CDot.Defs} (only : TypeOnly definitions)
    (env : TermCPS.Env) {sourceContext : CDot.Ctx} {tag : CDot.Path}
    {label : CDot.Signature.TypLabel} {body result : CDot.Typ}
    (derivation : Core.Typing sourceContext
      (.letE (.val (.new tag label body definitions)) returnSelf) result) :
    TermCPS.compile env derivation = repack := by
  simp only [TermCPS.compile, TermCPS.computation, TermCPS.run, returnSelf, TermCPS.value,
    only.fields_empty, Option.pure_def]
  rfl

omit [CDot.Signature] in
theorem repackTyping {s : SubtypingContext} {context : TypingContext s.typeDepth} {size : Nat}
    (system : RecursiveSystem s.typeDepth size)
    (guards : List (WFConstraint (s.typeDepth + size))) (answer : WFTy s.typeDepth)
    (evidence : CTML.Satisfies (system.openContext s) guards) :
    Recursive.HasType s context repack
      ((CTML.Interface.closeGuards size guards payload).package answer) := by
  refine .recursiveSystem system ?_
  exact .abstraction (.application
    (.abstraction (.application
      ((Recursive.HasType.native (HasType.var _ 1 _ (.there .here))).subsumption
        (CTML.RecursivePackage.consumerSubtypeWithGuards system guards payload answer evidence))
      (.native (HasType.var _ 0 _ .here))))
    (.native (objectThunkTyping _ _)))

structure Result (answer : WFTy 0) (env : TermCPS.Env)
    {sourceContext : CDot.Ctx} {tag : CDot.Path} {label : CDot.Signature.TypLabel}
    {body requested : CDot.Typ} {definitions : CDot.Defs}
    (derivation : Core.Typing sourceContext
      (.letE (.val (.new tag label body definitions)) returnSelf) (.bnd requested)) where
  only : TypeOnly definitions
  members : Compiled only.labels env.fieldName answer only.bodies
  guards : List (WFConstraint (0 + only.entries.length))
  parsed : bounds only.labels env.fieldName answer requested = some guards
  evidence : CTML.Satisfies (members.system.openContext SubtypingContext.empty) guards
  typing : Recursive.HasType SubtypingContext.empty TypingContext.empty
    (TermCPS.compile env derivation)
    ((CTML.Interface.closeGuards only.entries.length guards payload).package answer)

/-- Generate and discharge the requested constraints using only source input. -/
def compile (fuel : Nat) (answer : WFTy 0) (env : TermCPS.Env)
    {sourceContext : CDot.Ctx} {tag : CDot.Path} {label : CDot.Signature.TypLabel}
    {body requested : CDot.Typ} {definitions : CDot.Defs}
    (derivation : Core.Typing sourceContext
      (.letE (.val (.new tag label body definitions)) returnSelf) (.bnd requested)) :
    Outcome (Result answer env derivation) := do
  let only ← Outcome.ofOption (TypeOnly.inspect definitions)
  let members ← Outcome.ofOption
    (RecursiveAliasTranslation.compile only.labels env.fieldName answer only.bodies)
  match parsed : bounds only.labels env.fieldName answer requested with
  | none => .failed
  | some guards =>
      let evidence ← CTML.DischargeSearch.dischargeWithHints fuel
        (members.system.openContext SubtypingContext.empty)
        (CTML.RecursiveAliases.guards members.equations answer)
        (CTML.RecursiveAliases.guards_valid SubtypingContext.empty members.equations answer) guards
      return ⟨only, members, guards, parsed, evidence.down, by
        rw [compile_eq only env derivation]
        exact repackTyping (s := SubtypingContext.empty) (context := TypingContext.empty)
          members.system guards answer evidence.down⟩

end CDotFCCT.BoundedObjectCompilation
