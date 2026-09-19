import CDotFCCT.CTML.RecursivePackages
import CDotFCCT.CTML.TransparentInterfaces
import CDotFCCT.CTML.CarrierBinding

/-!
# Hiding mutually recursive witnesses in the carrier target

The same interface syntax closes a finite recursive scope. Its exported guards
may be proved using carrier inversion; every equation itself comes from the
generated function-guarded system. CBV packing evaluates the native payload once.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Transparent.RecursivePackage

open CTMLCore CTMLCore.Syntax

theorem consumerSubtypeWithGuards {s : SubtypingContext} {size : Nat}
    (system : RecursiveSystem s.typeDepth size)
    (constraints : List (WFConstraint (s.typeDepth + size)))
    (payload : WFTy (s.typeDepth + size)) (answer : WFTy s.typeDepth)
    (evidence : ∀ guard ∈ constraints,
      InvertingSubtype (system.openContext s) guard.sub guard.sup) :
    InvertingSubtype (system.openContext s)
      (((Interface.closeGuards size constraints payload).consumer answer).weakenBy size)
      (WFTy.arrow payload (answer.weakenBy size)) := by
  have opened := (Interface.bindBlock_open s size
    (Interface.guards constraints (.payload payload)) answer).mapAssumptions
      (target := (system.openContext s).assumptions)
      (fun guard member => @CTMLCore.Subtype.hyp (system.openContext s) guard
        (List.mem_append_right _ member))
  refine .trans (.native opened) (.nativeWith constraints ?_ evidence)
  exact Interface.guards_open constraints (.payload payload) (answer.weakenBy size)
    (fun guard member => @CTMLCore.Subtype.hyp ⟨s.typeDepth + size, constraints⟩ guard member)

/-- The exported type hides all locally solved names, including mutually negative witnesses. -/
theorem packWithGuardsTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {size : Nat} (system : RecursiveSystem s.typeDepth size)
    (constraints : List (WFConstraint (s.typeDepth + size))) {term : Term}
    {payload : WFTy (s.typeDepth + size)} (answer : WFTy s.typeDepth)
    (evidence : ∀ guard ∈ constraints,
      InvertingSubtype (system.openContext s) guard.sub guard.sup)
    (typing : HasType (system.openContext s) (context.bindTypes size)
      (term.liftTy size) payload) :
    HasType s context (packCBV term)
      ((Interface.closeGuards size constraints payload).package answer) :=
  .recursiveSystem system
    (packCBVConsumerTyping
      (consumerSubtypeWithGuards system constraints payload answer evidence) typing)

/-- Every defining equation is discharged from the common recursive scope. -/
theorem packTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {size : Nat} (system : RecursiveSystem s.typeDepth size) {term : Term}
    {payload : WFTy (s.typeDepth + size)} (answer : WFTy s.typeDepth)
    (typing : HasType (system.openContext s) (context.bindTypes size)
      (term.liftTy size) payload) :
    HasType s context (packCBV term)
      ((CTML.RecursivePackage.interface system payload).package answer) :=
  packWithGuardsTyping system system.equations answer
    (fun guard member => .native (@CTMLCore.Subtype.hyp (system.openContext s) guard
      (List.mem_append_left _ member))) typing

/-- Hide a solved recursive group behind the same carrier interface used by runtime variables.
Only the requested outer view is exported; the group's defining equations stay local. -/
theorem packCarrierTyping {Label : Type} [DecidableEq Label]
    {s : SubtypingContext} {context : TypingContext s.typeDepth} {size : Nat}
    (system : RecursiveSystem s.typeDepth size) (support : List Label) (payload : Label)
    (present : payload ∈ support) (types : Label → WFTy (s.typeDepth + size))
    (view answer : WFTy s.typeDepth) {term : Term}
    (included : InvertingSubtype (system.openContext s)
      (CarrierLayout.precise support types) (view.weakenBy size))
    (typing : HasType (system.openContext s) (context.bindTypes size)
      (term.liftTy size) (types payload)) :
    HasType s context (packCBV term)
      ((CarrierLayout.interface support payload view).package answer) := by
  refine .recursiveSystem system ?_
  change HasType (system.openContext s) (context.bindTypes size) (packCBV (term.liftTy size))
    (((CarrierLayout.interface support payload view).package answer).weakenBy size)
  rw [CarrierLayout.package_weakenBy]
  exact interfacePackCBVTyping
    (CarrierLayout.packingInstance (s := system.openContext s)
      support payload present types (view.weakenBy size) included) typing

end CDotFCCT.CTML.Transparent.RecursivePackage
