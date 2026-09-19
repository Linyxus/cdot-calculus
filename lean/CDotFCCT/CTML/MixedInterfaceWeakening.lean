import CDotFCCT.CTML.MixedInterfaces
import CDotFCCT.CTML.MixedTermWeakening

/-!
# Packing an arbitrary mixed-target payload

Term weakening lets the existential constructor use an existing payload typing
under its new continuation binder. The runtime term remains exactly `pack term`;
no substitution theorem or additional evaluation step is assumed.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax

variable {ghost : FieldName → Bool}

theorem packConsumerTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {consumer type answer : WFTy s.typeDepth} {term : Term}
    (included : InvertingSubtype ghost s consumer (WFTy.arrow type answer))
    (typing : HasType ghost s context term type) :
    HasType ghost s context (pack term) (WFTy.arrow consumer answer) :=
  .abstraction (.application
    ((HasType.native (.var _ 0 _ .here)).subsumption included)
    (typing.weakenFront consumer))

/-- All payload derivations, including nested recursive declarations, can be packaged. -/
theorem interfacePackTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {interface : Interface s.typeDepth} {type answer : WFTy s.typeDepth} {term : Term}
    (inst : InterfaceInstance ghost s interface type) (typing : HasType ghost s context term type) :
    HasType ghost s context (pack term) (interface.package answer) :=
  packConsumerTyping (inst.consumerSubtype answer) typing

end CDotFCCT.CTML.Mixed
