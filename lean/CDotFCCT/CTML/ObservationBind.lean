import CDotFCCT.CTML.ObservationViews
import CDotFCCT.CTML.Interfaces

/-!
# Sequencing computations without reopening observation witnesses

A client may return an intersection of observations, including universally
quantified and constrained views of a shared carrier. Sequencing its input does
not require choosing a witness or introducing another existential package.

The same target term is checked at every view. Native records may occur as the
payload of an observation; this construction does not encode records as functions.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Coercion

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

/-- Views ending in the same answer, including existential-package consumers. -/
inductive AnswerView : {n : Nat} → WFTy n → WFTy n → Type where
  | arrow {n : Nat} (param answer : WFTy n) :
      AnswerView answer (WFTy.arrow param answer)
  | both {n : Nat} {answer left right : WFTy n} :
      AnswerView answer left → AnswerView answer right →
      AnswerView answer (WFTy.intersection left right)
  | all {n : Nat} {answer : WFTy n} {body : WFTy (n + 1)} :
      AnswerView answer.weaken body → AnswerView answer (WFTy.all body)
  | guarded {n : Nat} {answer body : WFTy n} (guard : WFConstraint n) :
      AnswerView answer body → AnswerView answer (WFTy.constrained guard body)

def Observation.answerView {n : Nat} {answer type : WFTy n}
    (shape : Observation answer type) : AnswerView answer type :=
  match shape with
  | .result payload answer => .arrow (WFTy.arrow payload answer) answer
  | .both left right => .both left.answerView right.answerView
  | .all body => .all body.answerView
  | .guarded guard body => .guarded guard body.answerView

def packageAnswerView {n : Nat} (interface : Interface n) (answer : WFTy n) :
    AnswerView answer (interface.package answer) :=
  .arrow (interface.consumer answer) answer

/-- `λk. input (λv. client v k)`, with both operands in the outer context. -/
def bindObservation (input client : Term) : Term :=
  .abs (.app (input.lift 1)
    (.abs (.app (.app ((client.lift 1).lift 1) (.var 0)) (.var 1))))

theorem bindObservation_liftTy (input client : Term) :
    (bindObservation input client).liftTy 1 =
      bindObservation (input.liftTy 1) (client.liftTy 1) := by
  change Term.abs (.app ((input.lift 1).liftTy 1)
    (.abs (.app (.app (((client.lift 1).lift 1).liftTy 1) (.var 0)) (.var 1)))) = _
  rw [← Term.liftTy_liftAt_comm input 0 1 1,
    ← Term.liftTy_liftAt_comm (client.lift 1) 0 1 1,
    ← Term.liftTy_liftAt_comm client 0 1 1]
  rfl

theorem bindObservation_arrow {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {input client : Term}
    {source param answer : WFTy s.typeDepth}
    (hi : HasType s context input (observation source answer))
    (hc : HasType s context client (WFTy.arrow source (WFTy.arrow param answer))) :
    HasType s context (bindObservation input client) (WFTy.arrow param answer) :=
  .abstraction (.application (hi.weakenFront param)
    (.abstraction (.application
      (.application ((hc.weakenFront param).weakenFront source) (.var _ 0 _ .here))
      (.var _ 1 _ (.there .here)))))

private theorem AnswerView.bindAux {n : Nat} {answer type : WFTy n}
    (shape : AnswerView answer type) {assumptions : List (WFConstraint n)}
    {context : TypingContext n} {input client : Term} {source : WFTy n}
    (hi : HasType ⟨n, assumptions⟩ context input (observation source answer))
    (hc : HasType ⟨n, assumptions⟩ context client (WFTy.arrow source type)) :
    HasType ⟨n, assumptions⟩ context (bindObservation input client) type :=
  match shape with
  | .arrow _ _ => bindObservation_arrow hi hc
  | .both left right =>
      .intersection (left.bindAux hi (hc.subsumption (.arrow .refl .interLeft)))
        (right.bindAux hi (hc.subsumption (.arrow .refl .interRight)))
  | .all (body := bodyType) body =>
      .forall _ _ _ (.value (.abs _)) ((bindObservation_liftTy input client).symm ▸
        body.bindAux (source := source.weaken) hi.weakenType
          (hc.weakenType.subsumption
            (show Subtype (⟨n, assumptions⟩ : SubtypingContext).bindType
                (WFTy.arrow source.weaken (WFTy.all bodyType).weaken)
                (WFTy.arrow source.weaken bodyType) from
              .arrow .refl (openUniversal (s := ⟨n, assumptions⟩) bodyType))))
  | .guarded guard body =>
      .constrained _ _ _ _ (.value (.abs _))
        (body.bindAux (assumptions := guard :: assumptions) (hi.weakenAssumption guard)
          ((hc.weakenAssumption guard).subsumption (.arrow .refl
            (@Subtype.constrainedLeft ⟨n, guard :: assumptions⟩ guard _
              (@Subtype.hyp ⟨n, guard :: assumptions⟩ guard List.mem_cons_self)))))

theorem AnswerView.bind {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {answer type : WFTy s.typeDepth} (shape : AnswerView answer type)
    {input client : Term} {source : WFTy s.typeDepth}
    (hi : HasType s context input (observation source answer))
    (hc : HasType s context client (WFTy.arrow source type)) :
    HasType s context (bindObservation input client) type :=
  shape.bindAux hi hc

theorem bindObservation_arrowRecursive {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {input client : Term}
    {source param answer : WFTy s.typeDepth}
    (hi : Recursive.HasType s context input (observation source answer))
    (hc : Recursive.HasType s context client (WFTy.arrow source (WFTy.arrow param answer))) :
    Recursive.HasType s context (bindObservation input client) (WFTy.arrow param answer) :=
  .abstraction (.application (hi.weakenFront param)
    (.abstraction (.application
      (.application ((hc.weakenFront param).weakenFront source) (.native (.var _ 0 _ .here)))
      (.native (.var _ 1 _ (.there .here))))))

private theorem AnswerView.bindRecursiveAux {n : Nat} {answer type : WFTy n}
    (shape : AnswerView answer type) {assumptions : List (WFConstraint n)}
    {context : TypingContext n} {input client : Term} {source : WFTy n}
    (hi : Recursive.HasType ⟨n, assumptions⟩ context input (observation source answer))
    (hc : Recursive.HasType ⟨n, assumptions⟩ context client (WFTy.arrow source type)) :
    Recursive.HasType ⟨n, assumptions⟩ context (bindObservation input client) type :=
  match shape with
  | .arrow _ _ => bindObservation_arrowRecursive hi hc
  | .both left right =>
      .intersection (left.bindRecursiveAux hi (hc.subsumption (.arrow .refl .interLeft)))
        (right.bindRecursiveAux hi (hc.subsumption (.arrow .refl .interRight)))
  | .all (body := bodyType) body =>
      .forall _ _ _ (.value (.abs _)) ((bindObservation_liftTy input client).symm ▸
        body.bindRecursiveAux (source := source.weaken) hi.weakenType
          (hc.weakenType.subsumption
            (show Subtype (⟨n, assumptions⟩ : SubtypingContext).bindType
                (WFTy.arrow source.weaken (WFTy.all bodyType).weaken)
                (WFTy.arrow source.weaken bodyType) from
              .arrow .refl (openUniversal (s := ⟨n, assumptions⟩) bodyType))))
  | .guarded guard body =>
      .constrained _ _ _ _ (.value (.abs _))
        (body.bindRecursiveAux (assumptions := guard :: assumptions)
          (hi.weakenAssumption guard)
          ((hc.weakenAssumption guard).subsumption (.arrow .refl
            (@Subtype.constrainedLeft ⟨n, guard :: assumptions⟩ guard _
              (@Subtype.hyp ⟨n, guard :: assumptions⟩ guard List.mem_cons_self)))))

theorem AnswerView.bindRecursive {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {answer type : WFTy s.typeDepth}
    (shape : AnswerView answer type) {input client : Term} {source : WFTy s.typeDepth}
    (hi : Recursive.HasType s context input (observation source answer))
    (hc : Recursive.HasType s context client (WFTy.arrow source type)) :
    Recursive.HasType s context (bindObservation input client) type :=
  shape.bindRecursiveAux hi hc

/-- Eliminate a CPS layer around an existing interface. -/
def flattenObservation (input : Term) : Term :=
  bindObservation input (.abs (.var 0))

theorem AnswerView.flatten {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {answer type : WFTy s.typeDepth} (shape : AnswerView answer type) {input : Term}
    (hi : HasType s context input (observation type answer)) :
    HasType s context (flattenObservation input) type :=
  shape.bind hi (.abstraction (.var _ 0 _ .here))

theorem AnswerView.flattenRecursive {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {answer type : WFTy s.typeDepth}
    (shape : AnswerView answer type) {input : Term}
    (hi : Recursive.HasType s context input (observation type answer)) :
    Recursive.HasType s context (flattenObservation input) type :=
  shape.bindRecursive hi (.abstraction (.native (.var _ 0 _ .here)))

theorem bindObservation_beta (input client : Term) {continuation : Term}
    (hk : Value continuation) :
    Steps (.app (bindObservation input client) continuation)
      (.app input (.abs (.app (.app (client.lift 1) (.var 0)) (continuation.lift 1)))) := by
  refine .trans (.appBeta _ _ hk) ?_
  change Steps (.app ((input.lift 1).substAt 0 continuation)
    ((Term.abs (.app (.app ((client.lift 1).lift 1) (.var 0)) (.var 1))).substAt 0
      continuation)) _
  rw [Term.lift_substAt_cancel, Term.substAt_abs]
  change Steps (.app input (.abs (.app (.app
    (((client.lift 1).lift 1).substAt 1 (continuation.lift 1)) (.var 0))
      (continuation.lift 1)))) _
  simpa only [Term.lift_lift_substAt_one] using
    (Steps.refl (term := .app input
      (.abs (.app (.app (client.lift 1) (.var 0)) (continuation.lift 1)))))

/-- Sequencing preserves the client's computation, even when that computation diverges. -/
theorem bindObservation_steps {input value : Term} (client : Term)
    (hi : Returns input value) (hv : Value value) {continuation : Term}
    (hk : Value continuation) :
    Steps (.app (bindObservation input client) continuation)
      (.app (.app client value) continuation) := by
  refine (bindObservation_beta input client hk).trans'
    ((hi _ (.abs _)).trans' (.trans (.appBeta _ _ hv) ?_))
  change Steps (.app (.app ((client.lift 1).substAt 0 value) value)
    ((continuation.lift 1).substAt 0 value)) _
  simpa only [Term.lift_substAt_cancel] using
    (Steps.refl (term := .app (.app client value) continuation))

theorem Returns.bindObservation {input value client result : Term}
    (hi : Returns input value) (hv : Value value)
    (hc : Returns (.app client value) result) :
    Returns (bindObservation input client) result :=
  fun _ hk => (bindObservation_steps client hi hv hk).trans' (hc _ hk)

/-- The extra CPS layer disappears without observing or choosing an existential witness. -/
theorem flattenObservation_steps {input value : Term} (hi : Returns input value)
    (hv : Value value) {continuation : Term} (hk : Value continuation) :
    Steps (.app (flattenObservation input) continuation) (.app value continuation) :=
  (bindObservation_steps (.abs (.var 0)) hi hv hk).trans'
    (.single (.appHead _ (.appBeta _ _ hv)))

theorem Returns.flattenObservation {input observed value : Term}
    (hi : Returns input observed) (ho : Value observed) (hr : Returns observed value) :
    Returns (flattenObservation input) value :=
  fun _ hk => (flattenObservation_steps hi ho hk).trans' (hr _ hk)

end CDotFCCT.CTML.Coercion
