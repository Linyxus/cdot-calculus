import CDotFCCT.CTML.ObservationBind
import CDotFCCT.CTML.RecursiveInterfaces
import CDotFCCT.CTML.InterfaceSubtyping

/-!
# Sequencing a whole existential interface

The input package opens its witness telescope over one consumer. That consumer
may return any answer view, including another constrained existential package.
The output's answer and free witnesses remain outside the input's local scope.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Interface

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation Coercion

private theorem consumerMonoAux {n : Nat} (interface : Interface n)
    {assumptions : List (WFConstraint n)} {first second : WFTy n}
    (sub : Subtype ⟨n, assumptions⟩ first second) :
    Subtype ⟨n, assumptions⟩ (interface.consumer first) (interface.consumer second) :=
  match interface with
  | .payload _ => .arrow .refl sub
  | .guard constraint rest =>
      .constrainedCovariant _ _ _
        (rest.consumerMonoAux (assumptions := constraint :: assumptions)
          (sub.weakenAssumption constraint))
  | .bind rest => .forallCovariant _ _ (rest.consumerMonoAux sub.weakenType)

theorem consumerMono {s : SubtypingContext} (interface : Interface s.typeDepth)
    {first second : WFTy s.typeDepth} (sub : Subtype s first second) :
    Subtype s (interface.consumer first) (interface.consumer second) :=
  interface.consumerMonoAux sub

theorem package_weaken {n : Nat} (interface : Interface n) (answer : WFTy n) :
    (interface.package answer).weaken = interface.weaken.package answer.weaken :=
  congrArg (fun type => WFTy.arrow type answer.weaken) (interface.consumer_weaken answer)

def applyConsumer (client argument : Term) : Term :=
  .abs (.app (.app (client.lift 1) (.var 0)) (argument.lift 1))

theorem applyConsumer_liftTy (client argument : Term) :
    (applyConsumer client argument).liftTy 1 =
      applyConsumer (client.liftTy 1) (argument.liftTy 1) := by
  change Term.abs (.app (.app ((client.lift 1).liftTy 1) (.var 0))
    ((argument.lift 1).liftTy 1)) = _
  rw [← Term.liftTy_liftAt_comm client 0 1 1,
    ← Term.liftTy_liftAt_comm argument 0 1 1]
  rfl

private theorem applyConsumerTypingAux {n : Nat} (interface : Interface n)
    {assumptions : List (WFConstraint n)} {context : TypingContext n}
    {client argument : Term} {param answer : WFTy n}
    (hc : Recursive.HasType ⟨n, assumptions⟩ context client
      (interface.consumer (WFTy.arrow param answer)))
    (ha : Recursive.HasType ⟨n, assumptions⟩ context argument param) :
    Recursive.HasType ⟨n, assumptions⟩ context (applyConsumer client argument)
      (interface.consumer answer) :=
  match interface with
  | .payload type =>
      .abstraction (.application
        (.application (hc.weakenFront type) (.native (.var _ 0 _ .here)))
        (ha.weakenFront type))
  | .guard constraint rest =>
      .constrained _ _ _ _ (.value (.abs _))
        (rest.applyConsumerTypingAux (assumptions := constraint :: assumptions)
          ((hc.weakenAssumption constraint).subsumption
            (@Subtype.constrainedLeft ⟨n, constraint :: assumptions⟩ constraint _
              (@Subtype.hyp ⟨n, constraint :: assumptions⟩ constraint List.mem_cons_self)))
          (ha.weakenAssumption constraint))
  | .bind rest =>
      .forall _ _ _ (.value (.abs _)) ((applyConsumer_liftTy client argument).symm ▸
        rest.applyConsumerTypingAux (param := param.weaken) (answer := answer.weaken)
          (hc.weakenType.subsumption (openUniversal (s := ⟨n, assumptions⟩)
            (rest.consumer (WFTy.arrow param answer).weaken))) ha.weakenType)

theorem applyConsumerTyping {s : SubtypingContext} (interface : Interface s.typeDepth)
    {context : TypingContext s.typeDepth} {client argument : Term}
    {param answer : WFTy s.typeDepth}
    (hc : Recursive.HasType s context client (interface.consumer (WFTy.arrow param answer)))
    (ha : Recursive.HasType s context argument param) :
    Recursive.HasType s context (applyConsumer client argument) (interface.consumer answer) :=
  interface.applyConsumerTypingAux hc ha

theorem bindArrow {s : SubtypingContext} (interface : Interface s.typeDepth)
    {context : TypingContext s.typeDepth} {input client : Term}
    {param answer : WFTy s.typeDepth}
    (hi : Recursive.HasType s context input (interface.package answer))
    (hc : Recursive.HasType s context client (interface.consumer (WFTy.arrow param answer))) :
    Recursive.HasType s context (bindObservation input client) (WFTy.arrow param answer) :=
  .abstraction (.application (hi.weakenFront param)
    (interface.applyConsumerTyping (hc.weakenFront param) (.native (.var _ 0 _ .here))))

private theorem bindAnswerViewAux {n : Nat} {answer type : WFTy n}
    (shape : AnswerView answer type) (interface : Interface n)
    {assumptions : List (WFConstraint n)} {context : TypingContext n}
    {input client : Term}
    (hi : Recursive.HasType ⟨n, assumptions⟩ context input (interface.package answer))
    (hc : Recursive.HasType ⟨n, assumptions⟩ context client (interface.consumer type)) :
    Recursive.HasType ⟨n, assumptions⟩ context (bindObservation input client) type :=
  match shape with
  | .arrow _ _ => interface.bindArrow hi hc
  | .both (left := leftType) (right := rightType) left right =>
      .intersection
        (bindAnswerViewAux left interface hi (hc.subsumption
          (interface.consumerMono (s := ⟨n, assumptions⟩)
            (first := WFTy.intersection leftType rightType)
            (second := leftType) .interLeft)))
        (bindAnswerViewAux right interface hi (hc.subsumption
          (interface.consumerMono (s := ⟨n, assumptions⟩)
            (first := WFTy.intersection leftType rightType)
            (second := rightType) .interRight)))
  | .all (body := bodyType) body =>
      .forall _ _ _ (.value (.abs _)) ((bindObservation_liftTy input client).symm ▸
        bindAnswerViewAux body interface.weaken
          ((interface.package_weaken answer) ▸ hi.weakenType)
          (((interface.consumer_weaken (WFTy.all bodyType)) ▸ hc.weakenType).subsumption
            (interface.weaken.consumerMono (openUniversal (s := ⟨n, assumptions⟩) bodyType))))
  | .guarded (body := bodyType) constraint body =>
      .constrained _ _ _ _ (.value (.abs _))
        (bindAnswerViewAux body interface (assumptions := constraint :: assumptions)
          (hi.weakenAssumption constraint)
          ((hc.weakenAssumption constraint).subsumption
            (interface.consumerMono (s := ⟨n, constraint :: assumptions⟩)
              (@Subtype.constrainedLeft ⟨n, constraint :: assumptions⟩ constraint bodyType
                (@Subtype.hyp ⟨n, constraint :: assumptions⟩ constraint List.mem_cons_self)))))

theorem bindAnswerView {s : SubtypingContext} (interface : Interface s.typeDepth)
    {context : TypingContext s.typeDepth} {answer type : WFTy s.typeDepth}
    (shape : AnswerView answer type) {input client : Term}
    (hi : Recursive.HasType s context input (interface.package answer))
    (hc : Recursive.HasType s context client (interface.consumer type)) :
    Recursive.HasType s context (bindObservation input client) type :=
  bindAnswerViewAux shape interface hi hc

theorem bindPackage {s : SubtypingContext} (source target : Interface s.typeDepth)
    {context : TypingContext s.typeDepth} {answer : WFTy s.typeDepth}
    {input client : Term}
    (hi : Recursive.HasType s context input (source.package answer))
    (hc : Recursive.HasType s context client (source.consumer (target.package answer))) :
    Recursive.HasType s context (bindObservation input client) (target.package answer) :=
  source.bindAnswerView (packageAnswerView target answer) hi hc

/-- The payload stays unchanged; implicit instantiations reuse the witnesses just opened. -/
def repacker : Term := .abs (.abs (.app (.var 0) (.var 1)))

private theorem repackerTypingAux {n : Nat} (interface : Interface n)
    (assumptions : List (WFConstraint n)) (context : TypingContext n) (answer : WFTy n) :
    HasType ⟨n, assumptions⟩ context repacker (interface.consumer (interface.package answer)) :=
  match interface with
  | .payload _ => .abstraction (.abstraction (.application
      (.var _ 0 _ .here) (.var _ 1 _ (.there .here))))
  | .guard constraint rest =>
      .constrained _ _ _ _ (.value (.abs _))
        ((rest.repackerTypingAux (constraint :: assumptions) context answer).subsumption
          (rest.consumerMono (s := ⟨n, constraint :: assumptions⟩)
            (show Subtype ⟨n, constraint :: assumptions⟩ (rest.package answer)
                ((Interface.guard constraint rest).package answer) from
              .arrow (@Subtype.constrainedLeft ⟨n, constraint :: assumptions⟩ constraint _
                (@Subtype.hyp ⟨n, constraint :: assumptions⟩ constraint List.mem_cons_self))
                .refl)))
  | .bind rest =>
      .forall _ _ _ (.value (.abs _))
        ((rest.repackerTypingAux (assumptions.map WFConstraint.weaken)
          context.bindType answer.weaken).subsumption
            (rest.consumerMono (s := (⟨n, assumptions⟩ : SubtypingContext).bindType)
              (show Subtype (⟨n, assumptions⟩ : SubtypingContext).bindType
                  (rest.package answer.weaken) ((Interface.bind rest).package answer).weaken from
                .arrow (openUniversal (s := ⟨n, assumptions⟩)
                  (rest.consumer answer.weaken)) .refl)))

/-- No packing instance is supplied: the consumer reuses all of its own witnesses and guards. -/
theorem repackerTyping {s : SubtypingContext} (interface : Interface s.typeDepth)
    (context : TypingContext s.typeDepth) (answer : WFTy s.typeDepth) :
    HasType s context repacker (interface.consumer (interface.package answer)) :=
  interface.repackerTypingAux s.assumptions context answer

/-- Interface weakening changes only the proof of the repacked payload's view. -/
theorem Map.repackerTyping {s : SubtypingContext} {source target : Interface s.typeDepth}
    (map : Map s source target) (context : TypingContext s.typeDepth) (answer : WFTy s.typeDepth) :
    HasType s context repacker (source.consumer (target.package answer)) :=
  (source.repackerTyping context answer).subsumption
    (source.consumerMono (map.packageSubtype answer))

def repack (input : Term) : Term := bindObservation input repacker

theorem repackTyping {s : SubtypingContext} (interface : Interface s.typeDepth)
    {context : TypingContext s.typeDepth} {input : Term} {answer : WFTy s.typeDepth}
    (hi : Recursive.HasType s context input (interface.package answer)) :
    Recursive.HasType s context (repack input) (interface.package answer) :=
  interface.bindPackage interface hi (.native (interface.repackerTyping context answer))

theorem Map.repackTyping {s : SubtypingContext} {source target : Interface s.typeDepth}
    (map : Map s source target) {context : TypingContext s.typeDepth} {input : Term}
    {answer : WFTy s.typeDepth}
    (hi : Recursive.HasType s context input (source.package answer)) :
    Recursive.HasType s context (repack input) (target.package answer) :=
  source.bindPackage target hi (.native (map.repackerTyping context answer))

theorem repackerReturns {value : Term} (hv : Value value) :
    Returns (.app repacker value) value :=
  fun _ hk => identitySteps hv hk

/-- Repacking uses the same payload even after changing the exported interface. -/
theorem repackReturns {input value : Term} (hi : Returns input value) (hv : Value value) :
    Returns (repack input) value :=
  hi.bindObservation hv (repackerReturns hv)

end CDotFCCT.CTML.Interface
