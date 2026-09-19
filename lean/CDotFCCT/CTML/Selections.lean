import CDotFCCT.CTML.Coercions

/-!
# Constraint-abstracted observations of one stable member carrier

A selector mentions a shared carrier rather than choosing another existential witness.
It accepts every precise row below that carrier. A lower bound constructs the selector
by constraint abstraction; a known precise row later chooses a witness for observation.

These are derived CTML rules for one member. They do not yet provide the general
DOT type translation or the invariant maintaining carriers across paths and calls.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Coercion

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

def selectorGuard {n : Nat} (data carrier answer : WFTy n) : WFConstraint (n + 1) :=
  WFConstraint.constr (preciseMember data.weaken (WFTy.var 0 (Nat.zero_lt_succ n))
    answer.weaken) carrier.weaken

def selectorBody {n : Nat} (data carrier answer : WFTy n) : WFTy (n + 1) :=
  WFTy.constrained (selectorGuard data carrier answer)
    (WFTy.arrow (WFTy.arrow (WFTy.var 0 (Nat.zero_lt_succ n)) answer.weaken) answer.weaken)

/-- A CPS observation at every witness whose precise row lies below this carrier. -/
def selector {n : Nat} (data carrier answer : WFTy n) : WFTy n :=
  WFTy.all (selectorBody data carrier answer)

theorem preciseMember_weaken {n : Nat} (data witness answer : WFTy n) :
    (preciseMember data witness answer).weaken =
      preciseMember data.weaken witness.weaken answer.weaken := rfl

theorem memberView_weaken {n : Nat} (lower upper answer : WFTy n) :
    (memberView lower upper answer).weaken =
      memberView lower.weaken upper.weaken answer.weaken := rfl

/-- Both operands precede the fresh member witness and are independent of it. -/
def selectLower : Term :=
  .abs (.abs (.abs (.app (.app (.app memberLower (.var 2)) (.var 1)) (.var 0))))

theorem selectorHyp (s : SubtypingContext) (data carrier answer : WFTy s.typeDepth) :
    Subtype (s.bindType.assume (selectorGuard data carrier answer))
      (preciseMember data.weaken (WFTy.var 0 (Nat.zero_lt_succ s.typeDepth)) answer.weaken)
      carrier.weaken :=
  @Subtype.hyp (s.bindType.assume (selectorGuard data carrier answer))
    (selectorGuard data carrier answer) List.mem_cons_self

theorem selectLowerTyping {s : SubtypingContext} (context : TypingContext s.typeDepth)
    {data carrier lower upper answer : WFTy s.typeDepth}
    (bound : Subtype s carrier (memberView lower upper answer)) :
    HasType s context selectLower
      (WFTy.arrow data (WFTy.arrow lower (selector data carrier answer))) := by
  refine .abstraction (.abstraction (.forall _ _ _ (.value (.abs _)) ?_))
  refine .constrained _ _ _ _ (.value (.abs _)) (.abstraction ?_)
  exact .application (.application (.application
    (memberLowerTyping _ (upper := upper.weaken) (.trans (selectorHyp s data carrier answer)
      (bound.weakenType.weakenAssumption _)))
    (.var _ 2 _ (.there (.there .here)))) (.var _ 1 _ (.there .here))) (.var _ 0 _ .here)

theorem selectorBody_instantiate {n : Nat} (data carrier answer witness : WFTy n) :
    (selectorBody data carrier answer).instantiate witness =
      WFTy.constrained (WFConstraint.constr (preciseMember data witness answer) carrier)
        (WFTy.arrow (WFTy.arrow witness answer) answer) := by
  change WFTy.constrained
    (WFConstraint.constr (preciseMember (data.weaken.instantiate witness) witness
      (answer.weaken.instantiate witness)) (carrier.weaken.instantiate witness))
    (WFTy.arrow (WFTy.arrow witness (answer.weaken.instantiate witness))
      (answer.weaken.instantiate witness)) = _
  simp only [WFTy.weaken_instantiate_cancel]

/-- Observation chooses an existing precise witness; it does not allocate a new one. -/
theorem selectorInstance {s : SubtypingContext} {data carrier answer witness : WFTy s.typeDepth}
    (precise : Subtype s (preciseMember data witness answer) carrier) :
    Subtype s (selector data carrier answer) (WFTy.arrow (WFTy.arrow witness answer) answer) :=
  .trans (Subtype.forallLeft (argument := witness))
    ((selectorBody_instantiate data carrier answer witness).symm ▸
      Subtype.constrainedLeft _ _ precise)

/-- Widening the carrier enlarges the quantified set of rows, hence narrows its selector. -/
theorem selectorCarrier {s : SubtypingContext} {data first second answer : WFTy s.typeDepth}
    (sub : Subtype s first second) :
    Subtype s (selector data second answer) (selector data first answer) :=
  .forallCovariant _ _ (.trans (.constrainedRight (selectorGuard data first answer) _)
    (.constrainedCovariant _ _ _ (.constrainedLeft _ _
      (.trans (selectorHyp s data first answer) (sub.weakenType.weakenAssumption _)))))

def selectUpper : Term :=
  .abs (.abs (.abs (.app (.var 1)
    (.abs (.app (.app (.app memberUpper (.var 3)) (.var 0)) (.var 1))))))

theorem selectUpperTyping {s : SubtypingContext} (context : TypingContext s.typeDepth)
    {data carrier witness lower upper answer : WFTy s.typeDepth}
    (precise : Subtype s (preciseMember data witness answer) carrier)
    (bound : Subtype s carrier (memberView lower upper answer)) :
    HasType s context selectUpper (WFTy.arrow data
      (WFTy.arrow (selector data carrier answer) (WFTy.arrow (WFTy.arrow upper answer) answer))) :=
  .abstraction (.abstraction (.abstraction (.application
    ((HasType.var _ 1 _ (.there .here)).subsumption (selectorInstance precise))
    (.abstraction (.application (.application (.application
      (memberUpperTyping _ (.trans precise bound))
      (.var _ 3 _ (.there (.there (.there .here))))) (.var _ 0 _ .here))
      (.var _ 1 _ (.there .here)))))))

theorem selectLowerSteps {payload value continuation : Term}
    (hd : Value payload) (hv : Value value) (hk : Value continuation) :
    Steps (.app (.app (.app selectLower payload) value) continuation)
      (.app continuation value) := by
  refine .trans (.appHead _ (.appHead _ (.appBeta _ _ hd)))
    (.trans (.appHead _ (.appBeta _ _ hv)) (.trans (.appBeta _ _ hk) ?_))
  change Steps (.app (.app (.app memberLower _)
    ((value.lift 1).substAt 0 continuation)) continuation) _
  rw [Term.lift_substAt_cancel]
  exact memberLowerSteps ((((hd.renameWith _).renameWith _).substWith _).substWith _) hv hk

/-- Construct using one upper view of the carrier, then observe using another.
Only the observation phase needs the carrier's existing precise witness. -/
def throughSelector (payload value continuation : Term) : Term :=
  .app (.app (.app selectLower payload) value)
    (.abs (.app (continuation.lift 1)
      (.app (.app memberUpperDirect (payload.lift 1)) (.var 0))))

theorem throughSelectorTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {payload value continuation : Term}
    {data carrier witness lower upper otherLower otherUpper answer : WFTy s.typeDepth}
    (lowerBound : Subtype s carrier (memberView lower otherUpper answer))
    (upperBound : Subtype s carrier (memberView otherLower upper answer))
    (precise : Subtype s (preciseMember data witness answer) carrier)
    (hd : HasType s context payload data) (hv : HasType s context value lower)
    (hk : HasType s context continuation (WFTy.arrow upper answer)) :
    HasType s context (throughSelector payload value continuation) answer :=
  .application
    ((HasType.application (.application (selectLowerTyping _ lowerBound) hd) hv).subsumption
      (selectorInstance precise))
    (.abstraction (.application (hk.weakenFront witness)
      (.application (.application (memberUpperDirectTyping _ (.trans precise upperBound))
        (hd.weakenFront witness)) (.var _ 0 _ .here))))

theorem throughSelectorSteps {payload value continuation : Term}
    (hd : Value payload) (hv : Value value) (hk : Value continuation) :
    Steps (throughSelector payload value continuation) (.app continuation value) := by
  refine (selectLowerSteps hd hv (.abs _)).trans' (.trans (.appBeta _ _ hv) ?_)
  change Steps (.app ((continuation.lift 1).substAt 0 value)
    (.app (.app memberUpperDirect ((payload.lift 1).substAt 0 value)) value)) _
  simpa only [Term.lift_substAt_cancel] using (memberUpperDirectSteps hd hv).appArg hk

end CDotFCCT.CTML.Coercion
