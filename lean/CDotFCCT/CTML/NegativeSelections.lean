import CDotFCCT.CTML.NegativeWitnesses
import CDotFCCT.CTML.CoercionRefinement

/-!
# Abstract selections retaining a negative witness representation

Quantifying a package consumer `K` keeps its witness `K → R` negative even when
the precise member row is abstract. A lower bound constructs this view without
choosing `K`; elimination instantiates it at the carrier's existing consumer.
Records and the constraints relating their views remain native CTML types.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Coercion

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

def negativeSelectorGuard {n : Nat} (data carrier answer : WFTy n) : WFConstraint (n + 1) :=
  WFConstraint.constr
    (preciseMember data.weaken
      (WFTy.arrow (WFTy.var 0 (Nat.zero_lt_succ n)) answer.weaken) answer.weaken)
    carrier.weaken

def negativeSelectorBody {n : Nat} (data carrier answer : WFTy n) : WFTy (n + 1) :=
  WFTy.constrained (negativeSelectorGuard data carrier answer)
    (WFTy.arrow (WFTy.var 0 (Nat.zero_lt_succ n)) answer.weaken)

/-- A selected package at every consumer whose precise member row lies below the carrier. -/
def negativeSelector {n : Nat} (data carrier answer : WFTy n) : WFTy n :=
  WFTy.all (negativeSelectorBody data carrier answer)

def negativeSelectorView {n : Nat} (data carrier answer : WFTy n) :
    AnswerView answer (negativeSelector data carrier answer) :=
  .all (.guarded _ (.arrow _ _))

theorem negativeSelectorHyp (s : SubtypingContext) (data carrier answer : WFTy s.typeDepth) :
    Subtype (s.bindType.assume (negativeSelectorGuard data carrier answer))
      (preciseMember data.weaken
        (WFTy.arrow (WFTy.var 0 (Nat.zero_lt_succ s.typeDepth)) answer.weaken) answer.weaken)
      carrier.weaken :=
  @Subtype.hyp (s.bindType.assume (negativeSelectorGuard data carrier answer))
    (negativeSelectorGuard data carrier answer) List.mem_cons_self

theorem lowerWitness_liftTy (payload input : Term) :
    (lowerWitness payload input).liftTy 1 =
      lowerWitness (payload.liftTy 1) (input.liftTy 1) := by
  exact bindObservation_liftTy _ _

theorem lowerWitness_select {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {payload input : Term} {data carrier lower upper answer : WFTy s.typeDepth}
    (bound : Subtype s carrier (memberView lower upper answer))
    (hd : HasType s context payload data) (hi : HasType s context input lower) :
    HasType s context (lowerWitness payload input) (negativeSelector data carrier answer) := by
  refine .forall _ _ _ (.value (.abs _)) ?_
  rw [lowerWitness_liftTy]
  refine .constrained _ _ _ _ (.value (.abs _)) ?_
  exact lowerWitnessTyping (upper := upper.weaken) (.ofView (.arrow _ _))
    (.trans (negativeSelectorHyp s data carrier answer) (bound.weakenType.weakenAssumption _))
    (hd.weakenType.weakenAssumption _) (hi.weakenType.weakenAssumption _)

theorem negativeSelectorBody_instantiate {n : Nat}
    (data carrier answer consumer : WFTy n) :
    (negativeSelectorBody data carrier answer).instantiate consumer =
      WFTy.constrained
        (WFConstraint.constr (preciseMember data (WFTy.arrow consumer answer) answer) carrier)
        (WFTy.arrow consumer answer) := by
  change WFTy.constrained
    (WFConstraint.constr (preciseMember (data.weaken.instantiate consumer)
      (WFTy.arrow consumer (answer.weaken.instantiate consumer))
      (answer.weaken.instantiate consumer)) (carrier.weaken.instantiate consumer))
    (WFTy.arrow consumer (answer.weaken.instantiate consumer)) = _
  simp only [WFTy.weaken_instantiate_cancel]

/-- Observation chooses the consumer already associated with this carrier. -/
theorem negativeSelectorInstance {s : SubtypingContext}
    {data carrier answer consumer : WFTy s.typeDepth}
    (precise : Subtype s (preciseMember data (WFTy.arrow consumer answer) answer) carrier) :
    Subtype s (negativeSelector data carrier answer) (WFTy.arrow consumer answer) :=
  .trans (Subtype.forallLeft (argument := consumer))
    ((negativeSelectorBody_instantiate data carrier answer consumer).symm ▸
      Subtype.constrainedLeft _ _ precise)

theorem negativeSelectorCarrier {s : SubtypingContext}
    {data first second answer : WFTy s.typeDepth} (sub : Subtype s first second) :
    Subtype s (negativeSelector data second answer) (negativeSelector data first answer) :=
  .forallCovariant _ _ (.trans (.constrainedRight (negativeSelectorGuard data first answer) _)
    (.constrainedCovariant _ _ _ (.constrainedLeft _ _
      (.trans (negativeSelectorHyp s data first answer) (sub.weakenType.weakenAssumption _)))))

theorem preciseMemberEquivalent {s : SubtypingContext}
    {data first second answer : WFTy s.typeDepth}
    (forward : Subtype s first second) (backward : Subtype s second first) :
    Subtype s (preciseMember data first answer) (preciseMember data second answer) :=
  .interMono (.interMono .refl (.record (.arrow backward .refl)))
    (.record (.arrow .refl forward))

/-- An opaque recursive package uses its existing name and the two native equations. -/
theorem negativeSelectorWitness {s : SubtypingContext}
    {data carrier answer consumer witness : WFTy s.typeDepth}
    (unfold : Subtype s witness (WFTy.arrow consumer answer))
    (fold : Subtype s (WFTy.arrow consumer answer) witness)
    (precise : Subtype s (preciseMember data witness answer) carrier) :
    Subtype s (negativeSelector data carrier answer) witness :=
  .trans (negativeSelectorInstance (.trans (preciseMemberEquivalent fold unfold) precise)) fold

theorem lowerWitness_selectRecursive {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {payload input : Term}
    {data carrier lower upper answer : WFTy s.typeDepth}
    (bound : Subtype s carrier (memberView lower upper answer))
    (hd : Recursive.HasType s context payload data)
    (hi : Recursive.HasType s context input lower) :
    Recursive.HasType s context (lowerWitness payload input)
      (negativeSelector data carrier answer) :=
  .forall _ _ _ (.value (.abs _)) ((lowerWitness_liftTy payload input).symm ▸
    Recursive.HasType.constrained _ _ _ _ (.value (.abs _))
      (lowerWitnessTypingRecursive (upper := upper.weaken) (.ofView (.arrow _ _))
        (.trans (negativeSelectorHyp s data carrier answer) (bound.weakenType.weakenAssumption _))
        (hd.weakenType.weakenAssumption _) (hi.weakenType.weakenAssumption _)))

theorem lowerWitness_selectRefinement {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {payload input : Term}
    {data carrier lower upper answer original : WFTy s.typeDepth}
    (negative : NegativeWitness s answer original)
    (bound : Subtype s carrier (memberView lower upper answer))
    (hd : HasType s context payload data) (hi : HasType s context input original)
    (hl : HasType s context input lower) :
    HasType s context (lowerWitness payload input)
      (WFTy.intersection original (negativeSelector data carrier answer)) :=
  .intersection (lowerWitnessRetains negative hd hi) (lowerWitness_select bound hd hl)

theorem lowerWitness_selectRefinementRecursive {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {payload input : Term}
    {data carrier lower upper answer original : WFTy s.typeDepth}
    (negative : NegativeWitness s answer original)
    (bound : Subtype s carrier (memberView lower upper answer))
    (hd : Recursive.HasType s context payload data)
    (hi : Recursive.HasType s context input original)
    (hl : Recursive.HasType s context input lower) :
    Recursive.HasType s context (lowerWitness payload input)
      (WFTy.intersection original (negativeSelector data carrier answer)) :=
  .intersection (lowerWitnessRetainsRecursive negative hd hi)
    (lowerWitness_selectRecursive bound hd hl)

def throughNegativeSelector (payload input : Term) : Term :=
  .app (.app memberUpperDirect payload) (lowerWitness payload input)

/-- The lower and upper bounds may come from different views of one carrier. -/
theorem throughNegativeSelectorTyping {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {payload input : Term}
    {data carrier witness consumer lower upper otherLower otherUpper answer : WFTy s.typeDepth}
    (unfold : Subtype s witness (WFTy.arrow consumer answer))
    (fold : Subtype s (WFTy.arrow consumer answer) witness)
    (precise : Subtype s (preciseMember data witness answer) carrier)
    (lowerBound : Subtype s carrier (memberView lower otherUpper answer))
    (upperBound : Subtype s carrier (memberView otherLower upper answer))
    (hd : HasType s context payload data) (hi : HasType s context input lower) :
    HasType s context (throughNegativeSelector payload input) upper :=
  .application (.application (memberUpperDirectTyping _ (.trans precise upperBound)) hd)
    ((lowerWitness_select lowerBound hd hi).subsumption
      (negativeSelectorWitness unfold fold precise))

theorem throughNegativeSelectorTypingRecursive {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {payload input : Term}
    {data carrier witness consumer lower upper otherLower otherUpper answer : WFTy s.typeDepth}
    (unfold : Subtype s witness (WFTy.arrow consumer answer))
    (fold : Subtype s (WFTy.arrow consumer answer) witness)
    (precise : Subtype s (preciseMember data witness answer) carrier)
    (lowerBound : Subtype s carrier (memberView lower otherUpper answer))
    (upperBound : Subtype s carrier (memberView otherLower upper answer))
    (hd : Recursive.HasType s context payload data)
    (hi : Recursive.HasType s context input lower) :
    Recursive.HasType s context (throughNegativeSelector payload input) upper :=
  .application
    (.application (.native (memberUpperDirectTyping _ (.trans precise upperBound))) hd)
    ((lowerWitness_selectRecursive lowerBound hd hi).subsumption
      (negativeSelectorWitness unfold fold precise))

theorem throughNegativeSelector_steps {payload input continuation : Term}
    (hd : Value payload) (hi : Value input) (hk : Value continuation) :
    Steps (.app (throughNegativeSelector payload input) continuation) (.app input continuation) :=
  ((memberUpperDirectSteps hd (.abs _)).appHead continuation).trans'
    (lowerWitness_steps hd hi hk)

theorem Returns.throughNegativeSelector {payload input value : Term}
    (returns : Returns input value) (hd : Value payload) (hi : Value input) :
    Returns (throughNegativeSelector payload input) value :=
  fun _ hk => (throughNegativeSelector_steps hd hi hk).trans' (returns _ hk)

end CDotFCCT.CTML.Coercion
