import CDotFCCT.CTML.Existentials

/-!
# Existential interfaces with any finite number of shared witnesses

An interface is a telescope of type names and constraints ending in one native
payload type. Constraints may relate several witnesses and may appear at any
point where their free variables are in scope. The entire interface has one
consumer and one payload: fields are not independently packaged.

`Instance` supplies concrete witnesses and proves every instantiated constraint.
`OpenedBody` checks a consumer under the corresponding abstract names and bounds.
Both compile to ordinary CTML typing and subtyping derivations.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

inductive Interface : Nat → Type where
  | payload {n : Nat} (type : WFTy n) : Interface n
  | guard {n : Nat} (constraint : WFConstraint n) (rest : Interface n) : Interface n
  | bind {n : Nat} (rest : Interface (n + 1)) : Interface n

namespace Interface

/-- The consumer introduces every witness before inspecting the native payload. -/
def consumer {n : Nat} (interface : Interface n) (answer : WFTy n) : WFTy n :=
  match interface with
  | .payload type => WFTy.arrow type answer
  | .guard constraint rest => WFTy.constrained constraint (rest.consumer answer)
  | .bind rest => WFTy.all (rest.consumer answer.weaken)

/-- Existential packaging keeps the answer outside every witness's scope. -/
def package {n : Nat} (interface : Interface n) (answer : WFTy n) : WFTy n :=
  WFTy.arrow (interface.consumer answer) answer

/-- Capture-avoiding substitution through a telescope. -/
def substAt {n : Nat} (interface : Interface (n + 1)) (index : Nat)
    (valid : index ≤ n) (replacement : WFTy n) : Interface n :=
  match interface with
  | .payload type => .payload (type.substAt index valid replacement)
  | .guard constraint rest =>
      .guard (constraint.substAt index valid replacement) (rest.substAt index valid replacement)
  | .bind rest => .bind (rest.substAt (index + 1) (by omega) replacement.weaken)

def instantiate {n : Nat} (interface : Interface (n + 1)) (witness : WFTy n) : Interface n :=
  interface.substAt 0 (Nat.zero_le n) witness

theorem consumer_substAt {n : Nat} (interface : Interface (n + 1))
    (answer : WFTy (n + 1)) (index : Nat) (valid : index ≤ n) (replacement : WFTy n) :
    (interface.consumer answer).substAt index valid replacement =
      (interface.substAt index valid replacement).consumer
        (answer.substAt index valid replacement) :=
  match interface with
  | .payload type => by
      simpa only [consumer, substAt] using WFTy.substAt_arrow valid type answer replacement
  | .guard constraint rest => by
      simpa only [consumer, substAt] using
        (WFTy.substAt_constrained valid constraint (rest.consumer answer) replacement).trans
        (congrArg (WFTy.constrained (constraint.substAt index valid replacement))
          (rest.consumer_substAt answer index valid replacement))
  | .bind rest => by
      simpa only [consumer, substAt] using
        (WFTy.substAt_all valid (rest.consumer answer.weaken) replacement).trans
        ((congrArg WFTy.all
          (rest.consumer_substAt answer.weaken (index + 1) (by omega) replacement.weaken)).trans
            (congrArg
              (fun result => WFTy.all
                ((rest.substAt (index + 1) (by omega) replacement.weaken).consumer result))
              (WFTy.substAt_weaken valid answer replacement)))

theorem consumer_instantiate {n : Nat} (interface : Interface (n + 1))
    (answer witness : WFTy n) :
    (interface.consumer answer.weaken).instantiate witness =
      (interface.instantiate witness).consumer answer :=
  (interface.consumer_substAt answer.weaken 0 (Nat.zero_le n) witness).trans
    (congrArg (interface.instantiate witness).consumer
      (WFTy.weaken_instantiate_cancel answer witness))

/-- A packing instance, including actual proofs of the instantiated bounds.
Later witnesses may be chosen using the earlier witnesses already substituted into `rest`. -/
inductive Instance (s : SubtypingContext) : Interface s.typeDepth → WFTy s.typeDepth → Type where
  | payload (type : WFTy s.typeDepth) : Instance s (.payload type) type
  | guard {constraint : WFConstraint s.typeDepth} {rest : Interface s.typeDepth}
      {type : WFTy s.typeDepth} :
      Subtype s constraint.sub constraint.sup → Instance s rest type →
      Instance s (.guard constraint rest) type
  | bind {rest : Interface (s.typeDepth + 1)} {type : WFTy s.typeDepth}
      (witness : WFTy s.typeDepth) :
      Instance s (rest.instantiate witness) type → Instance s (.bind rest) type

/-- Instantiate the universal consumer and discharge all bounds, without a target assumption. -/
theorem Instance.consumerSubtype {s : SubtypingContext} {interface : Interface s.typeDepth}
    {type : WFTy s.typeDepth} (inst : Instance s interface type) (answer : WFTy s.typeDepth) :
    Subtype s (interface.consumer answer) (WFTy.arrow type answer) :=
  match inst with
  | .payload _ => .refl
  | .guard evidence rest =>
      .trans (.constrainedLeft _ _ evidence) (rest.consumerSubtype answer)
  | .bind (rest := rest) witness inst =>
      .trans (.forallLeft (argument := witness))
        ((rest.consumer_instantiate answer witness).symm ▸ inst.consumerSubtype answer)

/-- Consumer checking opens the same telescope over the whole client body. -/
def Opened {n : Nat} (interface : Interface n) (assumptions : List (WFConstraint n))
    (context : TypingContext n) (body : Term) (answer : WFTy n) : Prop :=
  match interface with
  | .payload type => HasType ⟨n, assumptions⟩ (context.bind type) body answer
  | .guard constraint rest => rest.Opened (constraint :: assumptions) context body answer
  | .bind rest =>
      rest.Opened (assumptions.map WFConstraint.weaken) context.bindType (body.liftTy 1)
        answer.weaken

def OpenedBody (s : SubtypingContext) (context : TypingContext s.typeDepth)
    (body : Term) (answer : WFTy s.typeDepth) (interface : Interface s.typeDepth) : Prop :=
  interface.Opened s.assumptions context body answer

private theorem consumerTypingAux {n : Nat} (interface : Interface n)
    {assumptions : List (WFConstraint n)} {context : TypingContext n}
    {body : Term} {answer : WFTy n}
    (typing : interface.Opened assumptions context body answer) :
    HasType ⟨n, assumptions⟩ context (.abs body) (interface.consumer answer) :=
  match interface with
  | .payload _ => .abstraction typing
  | .guard constraint rest =>
      @HasType.constrained ⟨n, assumptions⟩ constraint (rest.consumer answer) context (.abs body)
        (.value (.abs _)) (rest.consumerTypingAux typing)
  | .bind rest =>
      .forall _ _ _ (.value (.abs _)) (rest.consumerTypingAux typing)

theorem consumerTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {body : Term} {answer : WFTy s.typeDepth} (interface : Interface s.typeDepth)
    (typing : OpenedBody s context body answer interface) :
    HasType s context (.abs body) (interface.consumer answer) :=
  interface.consumerTypingAux typing

theorem packTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {interface : Interface s.typeDepth} {type answer : WFTy s.typeDepth} {value : Term}
    (inst : Instance s interface type) (typing : HasType s context value type) :
    HasType s context (pack value) (interface.package answer) :=
  .abstraction (.application
    ((HasType.var _ 0 _ .here).subsumption (inst.consumerSubtype answer))
    (typing.weakenFront (interface.consumer answer)))

theorem packCBVTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {interface : Interface s.typeDepth} {type answer : WFTy s.typeDepth} {term : Term}
    (inst : Instance s interface type) (typing : HasType s context term type) :
    HasType s context (packCBV term) (interface.package answer) :=
  .application (.abstraction (packTyping inst (.var _ 0 _ .here))) typing

theorem unpackTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {interface : Interface s.typeDepth} {answer : WFTy s.typeDepth} {value body : Term}
    (producer : HasType s context value (interface.package answer))
    (consumer : OpenedBody s context body answer interface) :
    HasType s context (.app value (.abs body)) answer :=
  .application producer (interface.consumerTyping consumer)

end Interface

end CDotFCCT.CTML
