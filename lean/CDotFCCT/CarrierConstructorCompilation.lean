import CDotFCCT.BoundedObjectCompilation
import CDotFCCT.CTML.TransparentRecursivePackages

/-!
# Existing source constructor passes in the carrier target

The automatically generated recursive alias systems satisfy the carrier target's
function guard. Their checked native bounds can therefore be reused in that
judgment. These proofs cover the exact existing CPS output and requested witness
interfaces; no target evidence is added to the source compiler's input.

This makes the type-only constructor passes available in the same judgment as
the carrier compiler. Their alias interfaces are still distinct from its general
carrier views, and fields and dependent constructors remain unfinished.
-/

set_option autoImplicit false

namespace CDotFCCT.TypeOnlyCompilation

open CTMLCore CTMLCore.Syntax

variable [CDot.Signature]

/-- Reuse all generated alias witnesses and original equations in the experimental target. -/
theorem Result.carrierTargetTyping {answer : WFTy 0} {env : TermCPS.Env}
    {sourceContext : CDot.Ctx} {tag : CDot.Path} {label : CDot.Signature.TypLabel}
    {body : CDot.Typ} {definitions : CDot.Defs}
    {derivation : Core.Typing sourceContext
      (.val (.new tag label body definitions)) (.bnd body)}
    (compiled : Result answer env derivation) :
    CTML.Transparent.HasType SubtypingContext.empty TypingContext.empty
      (TermCPS.compile env derivation) ((compiled.members.interface payload).package answer) := by
  rw [compiled.only.compile_eq env derivation]
  refine .recursiveSystem compiled.members.system ?_
  exact .abstraction (.application
    (.subsumption (.native (.var _ _ _ .here))
      (CTML.Transparent.RecursivePackage.consumerSubtypeWithGuards
        (s := SubtypingContext.empty) compiled.members.system
        (CTML.RecursiveAliases.guards compiled.members.equations answer) payload answer
        (fun guard member => .native
          (CTML.RecursiveAliases.guards_valid SubtypingContext.empty
            compiled.members.equations answer guard member))))
    (.native (objectThunkTyping _ _)))

end CDotFCCT.TypeOnlyCompilation

namespace CDotFCCT.BoundedObjectCompilation

open CTMLCore CTMLCore.Syntax TypeOnlyCompilation

variable [CDot.Signature]

/-- Requested bounds are the ones already proved by the source-driven discharge pass. -/
theorem Result.carrierTargetTyping {answer : WFTy 0} {env : TermCPS.Env}
    {sourceContext : CDot.Ctx} {tag : CDot.Path} {label : CDot.Signature.TypLabel}
    {body requested : CDot.Typ} {definitions : CDot.Defs}
    {derivation : Core.Typing sourceContext
      (.letE (.val (.new tag label body definitions)) returnSelf) (.bnd requested)}
    (compiled : Result answer env derivation) :
    CTML.Transparent.HasType SubtypingContext.empty TypingContext.empty
      (TermCPS.compile env derivation)
      ((CTML.Interface.closeGuards compiled.only.entries.length compiled.guards payload).package
        answer) := by
  rw [compile_eq compiled.only env derivation]
  refine .recursiveSystem compiled.members.system ?_
  exact .abstraction (.application
    (.abstraction (.application
      (.subsumption (.native (.var _ _ _ (.there .here)))
        (CTML.Transparent.RecursivePackage.consumerSubtypeWithGuards
          (s := SubtypingContext.empty) compiled.members.system
          compiled.guards payload answer (fun guard member => .native
            (compiled.evidence guard member))))
      (.native (.var _ _ _ .here))))
    (.native (objectThunkTyping _ _)))

end CDotFCCT.BoundedObjectCompilation
