import CDotFCCT.CTML.QuantifiedInterfaces
import CTMLCore.Declarative.RecursiveAssumptions

/-!
# Existential and dependent interfaces with recursive witnesses

The package telescope and its bounds use ordinary CTML subtyping. Its payload and
client may now use local recursive type definitions anywhere in their derivations.
The result is explicitly in `Recursive.HasType`. Its operational safety theorem is
`Recursive.HasType.safe` in CTML Core's `IndexedFundamental.lean`.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Interface

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

def RecursiveOpened {n : Nat} (interface : Interface n)
    (assumptions : List (WFConstraint n)) (context : TypingContext n)
    (body : Term) (answer : WFTy n) : Prop :=
  match interface with
  | .payload type => Recursive.HasType ⟨n, assumptions⟩ (context.bind type) body answer
  | .guard constraint rest => rest.RecursiveOpened (constraint :: assumptions) context body answer
  | .bind rest =>
      rest.RecursiveOpened (assumptions.map WFConstraint.weaken) context.bindType
        (body.liftTy 1) answer.weaken

private theorem recursiveConsumerTypingAux {n : Nat} (interface : Interface n)
    {assumptions : List (WFConstraint n)} {context : TypingContext n}
    {body : Term} {answer : WFTy n}
    (typing : interface.RecursiveOpened assumptions context body answer) :
    Recursive.HasType ⟨n, assumptions⟩ context (.abs body) (interface.consumer answer) :=
  match interface with
  | .payload _ => .abstraction typing
  | .guard constraint rest =>
      @Recursive.HasType.constrained ⟨n, assumptions⟩ constraint (rest.consumer answer)
        context (.abs body) (.value (.abs _)) (rest.recursiveConsumerTypingAux typing)
  | .bind rest =>
      .forall _ _ _ (.value (.abs _)) (rest.recursiveConsumerTypingAux typing)

theorem recursiveConsumerTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {body : Term} {answer : WFTy s.typeDepth} (interface : Interface s.typeDepth)
    (typing : interface.RecursiveOpened s.assumptions context body answer) :
    Recursive.HasType s context (.abs body) (interface.consumer answer) :=
  interface.recursiveConsumerTypingAux typing

theorem recursivePackTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {interface : Interface s.typeDepth} {type answer : WFTy s.typeDepth} {value : Term}
    (inst : Instance s interface type) (typing : Recursive.HasType s context value type) :
    Recursive.HasType s context (pack value) (interface.package answer) :=
  .abstraction (.application
    ((Recursive.HasType.native (HasType.var _ 0 _ .here)).subsumption
      (inst.consumerSubtype answer))
    (typing.weakenFront (interface.consumer answer)))

theorem recursivePackCBVTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {interface : Interface s.typeDepth} {type answer : WFTy s.typeDepth} {term : Term}
    (inst : Instance s interface type) (typing : Recursive.HasType s context term type) :
    Recursive.HasType s context (packCBV term) (interface.package answer) :=
  .application (.abstraction
    (recursivePackTyping inst (.native (.var _ 0 _ .here)))) typing

theorem recursiveUnpackTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {interface : Interface s.typeDepth} {answer : WFTy s.typeDepth} {value body : Term}
    (producer : Recursive.HasType s context value (interface.package answer))
    (consumer : interface.RecursiveOpened s.assumptions context body answer) :
    Recursive.HasType s context (.app value (.abs body)) answer :=
  .application producer (interface.recursiveConsumerTyping consumer)

def RecursiveCheck {n : Nat} (interface : Interface n)
    (assumptions : List (WFConstraint n)) (context : TypingContext n) (term : Term) : Prop :=
  match interface with
  | .payload type => Recursive.HasType ⟨n, assumptions⟩ context term type
  | .guard constraint rest => rest.RecursiveCheck (constraint :: assumptions) context term
  | .bind rest =>
      rest.RecursiveCheck (assumptions.map WFConstraint.weaken) context.bindType (term.liftTy 1)

private theorem recursiveIntroduceAux {n : Nat} (interface : Interface n)
    {assumptions : List (WFConstraint n)} {context : TypingContext n} {term : Term}
    (nonexpansive : Nonexpansive term)
    (typing : interface.RecursiveCheck assumptions context term) :
    Recursive.HasType ⟨n, assumptions⟩ context term interface.close :=
  match interface with
  | .payload _ => typing
  | .guard constraint rest =>
      @Recursive.HasType.constrained ⟨n, assumptions⟩ constraint rest.close context term
        nonexpansive (rest.recursiveIntroduceAux nonexpansive typing)
  | .bind rest =>
      .forall _ _ _ nonexpansive (rest.recursiveIntroduceAux (nonexpansive.liftTy 1) typing)

theorem recursiveIntroduce {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {term : Term} (interface : Interface s.typeDepth) (nonexpansive : Nonexpansive term)
    (typing : interface.RecursiveCheck s.assumptions context term) :
    Recursive.HasType s context term interface.close :=
  interface.recursiveIntroduceAux nonexpansive typing

theorem recursiveApplyTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {interface : Interface s.typeDepth} {param result : WFTy s.typeDepth}
    {function argument : Term} (inst : Instance s interface (WFTy.arrow param result))
    (hFunction : Recursive.HasType s context function interface.close)
    (hArgument : Recursive.HasType s context argument param) :
    Recursive.HasType s context (.app function argument) result :=
  .application (hFunction.subsumption inst.closeSubtype) hArgument

end CDotFCCT.CTML.Interface
