import CDotFCCT.CTML.ObservationBind

/-!
# Lower bounds at negative type-member witnesses

An existential package is an arrow ending in the program's answer type. The same
is true of its negative views, up to native subtyping equivalence. Keeping that
fact when a witness is abstracted lets a lower-bound conversion return the witness
itself, rather than another CPS layer around it. The answer need not equal the
witness.

These rules require a checked representation of the witness. They do not infer
that representation from an arbitrary type variable or turn a typed conversion
into a native subtyping proof.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Coercion

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

structure NegativeWitness (s : SubtypingContext) (answer witness : WFTy s.typeDepth) where
  body : WFTy s.typeDepth
  shape : AnswerView answer body
  unfold : Subtype s witness body
  fold : Subtype s body witness

def NegativeWitness.ofView {s : SubtypingContext} {answer witness : WFTy s.typeDepth}
    (shape : AnswerView answer witness) : NegativeWitness s answer witness :=
  ⟨witness, shape, .refl, .refl⟩

def NegativeWitness.package (s : SubtypingContext) (interface : Interface s.typeDepth)
    (answer : WFTy s.typeDepth) : NegativeWitness s answer (interface.package answer) :=
  .ofView (packageAnswerView interface answer)

/-- The package arrow guards every self reference, including references in its constraints. -/
def recursivePackageDefinition {n : Nat} (interface : Interface (n + 1))
    (answer : WFTy n) : RecursiveType n :=
  .arrow (interface.consumer answer.weaken) answer.weaken

def NegativeWitness.recursive (s : SubtypingContext) (definition : RecursiveType s.typeDepth)
    (answer : WFTy s.typeDepth) (shape : AnswerView answer.weaken definition.body) :
    NegativeWitness (definition.openContext s) answer.weaken definition.name :=
  ⟨definition.body, shape, definition.unfold s, definition.fold s⟩

def NegativeWitness.recursivePackage (s : SubtypingContext)
    (interface : Interface (s.typeDepth + 1)) (answer : WFTy s.typeDepth) :
    NegativeWitness ((recursivePackageDefinition interface answer).openContext s)
      answer.weaken (recursivePackageDefinition interface answer).name :=
  .recursive s (recursivePackageDefinition interface answer) answer
    (packageAnswerView interface answer.weaken)

def NegativeWitness.intersection {s : SubtypingContext}
    {answer left right : WFTy s.typeDepth}
    (first : NegativeWitness s answer left) (second : NegativeWitness s answer right) :
    NegativeWitness s answer (WFTy.intersection left right) :=
  ⟨WFTy.intersection first.body second.body, .both first.shape second.shape,
    .interMono first.unfold second.unfold, .interMono first.fold second.fold⟩

theorem observationMono {s : SubtypingContext} {source target answer : WFTy s.typeDepth}
    (sub : Subtype s source target) :
    Subtype s (observation source answer) (observation target answer) :=
  .arrow (.arrow sub .refl) .refl

def lowerWitness (payload input : Term) : Term :=
  flattenObservation (.app (.app memberLower payload) input)

theorem lowerWitnessTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {data witness lower upper answer : WFTy s.typeDepth}
    (negative : NegativeWitness s answer witness)
    (bound : Subtype s (preciseMember data witness answer) (memberView lower upper answer))
    {payload input : Term} (hd : HasType s context payload data)
    (hi : HasType s context input lower) :
    HasType s context (lowerWitness payload input) witness :=
  (negative.shape.flatten
    ((HasType.application (.application (memberLowerTyping _ bound) hd) hi).subsumption
      (observationMono negative.unfold))).subsumption negative.fold

theorem lowerWitnessTypingRecursive {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {data witness lower upper answer : WFTy s.typeDepth}
    (negative : NegativeWitness s answer witness)
    (bound : Subtype s (preciseMember data witness answer) (memberView lower upper answer))
    {payload input : Term} (hd : Recursive.HasType s context payload data)
    (hi : Recursive.HasType s context input lower) :
    Recursive.HasType s context (lowerWitness payload input) witness :=
  (negative.shape.flattenRecursive
    ((Recursive.HasType.application (.application (.native (memberLowerTyping _ bound)) hd)
      hi).subsumption (observationMono negative.unfold))).subsumption negative.fold

theorem lowerWitnessRetains {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {data answer original : WFTy s.typeDepth} (negative : NegativeWitness s answer original)
    {payload input : Term} (hd : HasType s context payload data)
    (hi : HasType s context input original) :
    HasType s context (lowerWitness payload input) original :=
  lowerWitnessTyping negative (preciseMemberOwnView s data original answer) hd hi

theorem lowerWitnessRefinement {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {data witness lower upper answer original : WFTy s.typeDepth}
    (old : NegativeWitness s answer original) (selected : NegativeWitness s answer witness)
    (bound : Subtype s (preciseMember data witness answer) (memberView lower upper answer))
    {payload input : Term} (hd : HasType s context payload data)
    (hi : HasType s context input original) (hl : HasType s context input lower) :
    HasType s context (lowerWitness payload input) (WFTy.intersection original witness) :=
  .intersection (lowerWitnessRetains old hd hi) (lowerWitnessTyping selected bound hd hl)

theorem lowerWitnessRetainsRecursive {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {data answer original : WFTy s.typeDepth}
    (negative : NegativeWitness s answer original) {payload input : Term}
    (hd : Recursive.HasType s context payload data)
    (hi : Recursive.HasType s context input original) :
    Recursive.HasType s context (lowerWitness payload input) original :=
  lowerWitnessTypingRecursive negative (preciseMemberOwnView s data original answer) hd hi

theorem lowerWitnessRefinementRecursive {s : SubtypingContext}
    {context : TypingContext s.typeDepth}
    {data witness lower upper answer original : WFTy s.typeDepth}
    (old : NegativeWitness s answer original) (selected : NegativeWitness s answer witness)
    (bound : Subtype s (preciseMember data witness answer) (memberView lower upper answer))
    {payload input : Term} (hd : Recursive.HasType s context payload data)
    (hi : Recursive.HasType s context input original)
    (hl : Recursive.HasType s context input lower) :
    Recursive.HasType s context (lowerWitness payload input) (WFTy.intersection original witness) :=
  .intersection (lowerWitnessRetainsRecursive old hd hi)
    (lowerWitnessTypingRecursive selected bound hd hl)

theorem memberLowerStepsOfInput {payload input value continuation : Term}
    (hd : Value payload) (inputSteps : Steps input value) (hv : Value value)
    (hk : Value continuation) :
    Steps (.app (.app (.app memberLower payload) input) continuation)
      (.app continuation value) := by
  refine .trans (.appHead _ (.appHead _ (.appBeta _ _ hd))) ?_
  refine ((inputSteps.appArg (.abs _)).appHead continuation).trans' ?_
  refine .trans (.appHead _ (.appBeta _ _ hv)) (.trans (.appBeta _ _ hk) ?_)
  change Steps (.app (.proj (markerRecord _ continuation unusedFunction) "lower")
    ((value.lift 1).substAt 0 continuation)) _
  refine .trans (.appHead _ (.proj
    (.record _ _ (.cons ((((hd.renameWith _).renameWith _).substWith _).substWith _)
      (.cons hk (.cons (.abs _) .nil)))) (.there .here))) ?_
  simpa only [Term.lift_substAt_cancel] using (Steps.refl (term := .app continuation value))

/-- Applying the converted view runs exactly the input's original computation. -/
theorem lowerWitness_steps {payload input continuation : Term}
    (hd : Value payload) (hi : Value input) (hk : Value continuation) :
    Steps (.app (lowerWitness payload input) continuation) (.app input continuation) :=
  flattenObservation_steps (fun _ next => memberLowerSteps hd hi next) hi hk

theorem lowerWitness_stepsOfInput {payload input value continuation : Term}
    (hd : Value payload) (inputSteps : Steps input value) (hv : Value value)
    (hk : Value continuation) :
    Steps (.app (lowerWitness payload input) continuation) (.app value continuation) :=
  flattenObservation_steps (fun _ next => memberLowerStepsOfInput hd inputSteps hv next) hv hk

theorem Returns.lowerWitness {payload input value : Term} (returns : Returns input value)
    (hd : Value payload) (hi : Value input) : Returns (lowerWitness payload input) value :=
  fun _ hk => (lowerWitness_steps hd hi hk).trans' (returns _ hk)

end CDotFCCT.CTML.Coercion
