import CDotFCCT.CTML.Interfaces
import CDotFCCT.CTML.TransparentSafety

/-!
# Continuation-encoded existential interfaces in the experimental target

The telescope syntax and runtime packing operations are unchanged. Packing may
use bounds derived by carrier inversion; opening exposes those same bounds to
the continuation. The CBV packing theorem uses an explicitly typed packing
function, so it does not assume a weakening theorem for the experimental calculus.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Transparent

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

theorem InvertingSubtype.constrainedLeft {s : SubtypingContext}
    {guard : WFConstraint s.typeDepth} (body : WFTy s.typeDepth)
    (evidence : InvertingSubtype s guard.sub guard.sup) :
    InvertingSubtype s (WFTy.constrained guard body) body :=
  .cut guard evidence (.native (@CTMLCore.Subtype.constrainedLeft (s.assume guard) guard body
    (@CTMLCore.Subtype.hyp (s.assume guard) guard List.mem_cons_self)))

inductive InterfaceInstance (s : SubtypingContext) :
    Interface s.typeDepth → WFTy s.typeDepth → Type where
  | payload (type : WFTy s.typeDepth) : InterfaceInstance s (.payload type) type
  | guard {constraint : WFConstraint s.typeDepth} {rest : Interface s.typeDepth}
      {type : WFTy s.typeDepth} :
      InvertingSubtype s constraint.sub constraint.sup → InterfaceInstance s rest type →
      InterfaceInstance s (.guard constraint rest) type
  | bind {rest : Interface (s.typeDepth + 1)} {type : WFTy s.typeDepth}
      (witness : WFTy s.typeDepth) :
      InterfaceInstance s (rest.instantiate witness) type →
      InterfaceInstance s (.bind rest) type

theorem InterfaceInstance.consumerSubtype {s : SubtypingContext}
    {interface : Interface s.typeDepth} {type : WFTy s.typeDepth}
    (inst : InterfaceInstance s interface type) (answer : WFTy s.typeDepth) :
    InvertingSubtype s (interface.consumer answer) (WFTy.arrow type answer) :=
  match inst with
  | .payload _ => .native .refl
  | .guard evidence rest =>
      .trans (.constrainedLeft _ evidence) (rest.consumerSubtype answer)
  | .bind (rest := rest) witness inst =>
      .trans (.native (.forallLeft (argument := witness)))
        ((rest.consumer_instantiate answer witness).symm ▸ inst.consumerSubtype answer)

def InterfaceOpened {n : Nat} (interface : Interface n)
    (assumptions : List (WFConstraint n)) (context : TypingContext n)
    (body : Term) (answer : WFTy n) : Prop :=
  match interface with
  | .payload type => HasType ⟨n, assumptions⟩ (context.bind type) body answer
  | .guard constraint rest => InterfaceOpened rest (constraint :: assumptions) context body answer
  | .bind rest => InterfaceOpened rest (assumptions.map WFConstraint.weaken)
      context.bindType (body.liftTy 1) answer.weaken

theorem interfaceConsumerTyping {n : Nat} (interface : Interface n)
    {assumptions : List (WFConstraint n)} {context : TypingContext n}
    {body : Term} {answer : WFTy n}
    (typing : InterfaceOpened interface assumptions context body answer) :
    HasType ⟨n, assumptions⟩ context (.abs body) (interface.consumer answer) :=
  match interface with
  | .payload _ => .abstraction typing
  | .guard constraint rest =>
      @HasType.constrained ⟨n, assumptions⟩ constraint (rest.consumer answer)
        context (.abs body) (.value (.abs _)) (interfaceConsumerTyping rest typing)
  | .bind rest =>
      .forall _ _ _ (.value (.abs _)) (interfaceConsumerTyping rest typing)

/-- The only runtime work added by packing is a CBV administrative beta step. -/
theorem packCBVConsumerTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {consumer type answer : WFTy s.typeDepth} {term : Term}
    (included : InvertingSubtype s consumer (WFTy.arrow type answer))
    (typing : HasType s context term type) :
    HasType s context (packCBV term) (WFTy.arrow consumer answer) :=
  .application (.abstraction (.abstraction (.application
    ((HasType.native (.var _ 0 _ .here)).subsumption included)
    (.native (.var _ 1 _ (.there .here)))))) typing

theorem interfacePackCBVTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {interface : Interface s.typeDepth} {type answer : WFTy s.typeDepth} {term : Term}
    (inst : InterfaceInstance s interface type) (typing : HasType s context term type) :
    HasType s context (packCBV term) (interface.package answer) :=
  packCBVConsumerTyping (inst.consumerSubtype answer) typing

/-- Packing an environment value is the variable case of the runtime CPS pass. -/
theorem interfacePackVariableTyping {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {index : Nat}
    {interface : Interface s.typeDepth} {type answer : WFTy s.typeDepth}
    (inst : InterfaceInstance s interface type) (lookup : context.Lookup index type) :
    HasType s context (pack (.var index)) (interface.package answer) :=
  .abstraction (.application
    ((HasType.native (.var _ 0 _ .here)).subsumption (inst.consumerSubtype answer))
    (.native (.var _ (index + 1) _ (.there lookup))))

theorem interfaceUnpackTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {interface : Interface s.typeDepth} {answer : WFTy s.typeDepth} {value body : Term}
    (producer : HasType s context value (interface.package answer))
    (consumer : InterfaceOpened interface s.assumptions context body answer) :
    HasType s context (.app value (.abs body)) answer :=
  .application producer (interfaceConsumerTyping interface consumer)

end CDotFCCT.CTML.Transparent
