import CDotFCCT.CTML.MixedBinding

/-!
# A pure recursive ghost row solved by finite term structure

This experiment solves `P = leaf ∪ {minus : ¬P} ∪ {plus : P}`. Both field labels
are reflective, and the leaf candidate is independent of this recursive name.
The solver traverses proper record-field subterms at the current step index.
It does not extend the recursion guard or any typing rule.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.GhostRowRecursion

open CTMLCore CTMLCore.Syntax CTMLCore.Indexed

variable (minus plus : FieldName)

mutual
  /-- Both polarities are computed together; a negative recursive slot swaps them. -/
  def evaluate (leaf : Candidate) (n : Nat) : Term → Prop × Prop
    | .record className fields =>
        ((leaf n).1 (.record className fields) ∨ (evaluateFields leaf n fields).1,
         (leaf n).2 (.record className fields) ∧ (evaluateFields leaf n fields).2)
    | term => ((leaf n).1 term, (leaf n).2 term)

  def evaluateFields (leaf : Candidate) (n : Nat) :
      {names : List FieldName} → TermFields names → Prop × Prop
    | _, .nil => (False, True)
    | _, .cons name value tail _ =>
        ((name = minus ∧ (evaluate leaf n value).2) ∨
          (name = plus ∧ (evaluate leaf n value).1) ∨ (evaluateFields leaf n tail).1,
         (name = minus → (evaluate leaf n value).1) ∧
          (name = plus → (evaluate leaf n value).2) ∧ (evaluateFields leaf n tail).2)
end

def solution (leaf : Candidate) : Candidate := fun n =>
  (fun term => (evaluate minus plus leaf n term).1,
   fun term => (evaluate minus plus leaf n term).2)

def operator (leaf self : Candidate) : Candidate :=
  joint .union leaf
    (joint .union (TransparentRecord.record minus (negative self))
      (TransparentRecord.record plus self))

private theorem lookup_cons {names : List FieldName} {name field : FieldName}
    {head value : Term} {tail : TermFields names} {fresh : name ∉ names} :
    TermFields.Lookup (.cons name head tail fresh) field value ↔
      (name = field ∧ head = value) ∨ TermFields.Lookup tail field value :=
  ⟨fun lookup => match lookup with
    | .here => .inl ⟨rfl, rfl⟩
    | .there rest => .inr rest,
   fun found => found.elim (fun ⟨rfl, rfl⟩ => .here) TermFields.Lookup.there⟩

private theorem lookup_nil {field : FieldName} {value : Term} :
    ¬ TermFields.Lookup .nil field value := fun lookup => nomatch lookup

private theorem positive_fields (leaf : Candidate) (n : Nat) {names : List FieldName}
    (fields : TermFields names) :
    (evaluateFields minus plus leaf n fields).1 ↔
      (∃ value, TermFields.Lookup fields minus value ∧ (evaluate minus plus leaf n value).2) ∨
      (∃ value, TermFields.Lookup fields plus value ∧
        (evaluate minus plus leaf n value).1) := by
  cases fields with
  | nil => simp [evaluateFields, lookup_nil]
  | cons name value tail fresh =>
      simp [evaluateFields, lookup_cons, positive_fields leaf n tail,
        or_and_right, exists_or, or_assoc, or_left_comm, or_comm]

private theorem negative_fields (leaf : Candidate) (n : Nat) {names : List FieldName}
    (fields : TermFields names) :
    (evaluateFields minus plus leaf n fields).2 ↔
      (∀ value, TermFields.Lookup fields minus value → (evaluate minus plus leaf n value).1) ∧
      (∀ value, TermFields.Lookup fields plus value →
        (evaluate minus plus leaf n value).2) := by
  cases fields with
  | nil => simp [evaluateFields, lookup_nil]
  | cons name value tail fresh =>
      simp [evaluateFields, lookup_cons, negative_fields leaf n tail,
        or_imp, forall_and, and_assoc, and_left_comm]

private theorem observes_record (field : FieldName) (payload : Term → Prop)
    (className : ClassName) {names : List FieldName} (fields : TermFields names) :
    TransparentRecord.observes field payload (.record className fields) ↔
      ∃ value, TermFields.Lookup fields field value ∧ payload value := by
  constructor
  · rintro ⟨_, _, _, value, equal, lookup, observed⟩
    cases equal
    exact ⟨value, lookup, observed⟩
  · rintro ⟨value, lookup, observed⟩
    exact ⟨className, names, fields, value, rfl, lookup, observed⟩

private theorem observesAll_record (field : FieldName) (payload : Term → Prop)
    (className : ClassName) {names : List FieldName} (fields : TermFields names) :
    TransparentRecord.observesAll field payload (.record className fields) ↔
      ∀ value, TermFields.Lookup fields field value → payload value := by
  constructor
  · exact fun all value lookup => all className names fields value rfl lookup
  · intro all otherClass otherNames otherFields value equal lookup
    cases equal
    exact all value lookup

theorem solution_fixedPoint (leaf : Candidate) :
    solution minus plus leaf = operator minus plus leaf (solution minus plus leaf) := by
  funext n
  apply Prod.ext <;> funext term <;> apply propext <;> cases term <;>
    simp only [solution, operator, joint, negative, TransparentRecord.record, evaluate,
      observes_record, observesAll_record, positive_fields, negative_fields]
  all_goals simp [TransparentRecord.observes, TransparentRecord.observesAll]

private abbrev Transfers (left right : Prop × Prop) : Prop :=
  (left.1 → right.1) ∧ (left.2 → right.2)

mutual
  private theorem evaluate_transfer {left right : Candidate} {n m : Nat}
      (included : ∀ term, Transfers ((left n).1 term, (left n).2 term)
        ((right m).1 term, (right m).2 term)) (term : Term) :
      Transfers (evaluate minus plus left n term) (evaluate minus plus right m term) := by
    cases term with
    | record className fields =>
        exact ⟨Or.imp (included _).1 (evaluateFields_transfer included fields).1,
          And.imp (included _).2 (evaluateFields_transfer included fields).2⟩
    | var | abs | app | proj | ifIs | ascribe | fix => exact included _

  private theorem evaluateFields_transfer {left right : Candidate} {n m : Nat}
      (included : ∀ term, Transfers ((left n).1 term, (left n).2 term)
        ((right m).1 term, (right m).2 term)) {names : List FieldName}
      (fields : TermFields names) :
      Transfers (evaluateFields minus plus left n fields)
        (evaluateFields minus plus right m fields) := by
    cases fields with
    | nil => exact ⟨id, id⟩
    | cons name value tail fresh =>
        have child := evaluate_transfer included value
        have rest := evaluateFields_transfer included tail
        exact ⟨Or.imp (And.imp id child.2) (Or.imp (And.imp id child.1) rest.1),
          And.imp (fun observed equal => child.1 (observed equal))
            (And.imp (fun observed equal => child.2 (observed equal)) rest.2)⟩
end

theorem solution_downward {leaf : Candidate} (closed : Downward leaf) :
    Downward (solution minus plus leaf) :=
  fun m n within term => evaluate_transfer minus plus (fun value => closed m n within value) term

/-- Solving a ghost row inspects its independent leaf only at the current index. -/
theorem solution_congr {left right : Candidate} {n : Nat} (agree : left n = right n) :
    solution minus plus left n = solution minus plus right n := by
  have forward (term : Term) := evaluate_transfer minus plus
    (left := left) (right := right) (n := n) (m := n)
    (fun _ => ⟨fun observed => agree ▸ observed, fun observed => agree ▸ observed⟩) term
  have backward (term : Term) := evaluate_transfer minus plus
    (left := right) (right := left) (n := n) (m := n)
    (fun _ => ⟨fun observed => agree.symm ▸ observed,
      fun observed => agree.symm ▸ observed⟩) term
  exact Prod.ext
    (funext fun term => propext ⟨(forward term).1, (backward term).1⟩)
    (funext fun term => propext ⟨(forward term).2, (backward term).2⟩)

theorem solution_agree {left right : Candidate} {n : Nat} (agree : Agree n left right) :
    Agree n (solution minus plus left) (solution minus plus right) :=
  fun k within => solution_congr minus plus (agree k within)

/-- A separate ordinary guard remains contractive after solving this pure ghost row. -/
theorem solution_contractive {leaf : Candidate → Candidate} (guarded : Contractive leaf) :
    Contractive (fun self => solution minus plus (leaf self)) :=
  fun n left right agree => solution_congr minus plus (guarded n left right agree)

/-- Outer feedback uses the usual step index; the inner ghost row uses finite term structure. -/
def coupled (leaf : Candidate → Candidate) : Candidate :=
  fixedPoint (fun self => solution minus plus (leaf self)) (fun _ => False, fun _ => False)

theorem coupled_unfold {leaf : Candidate → Candidate} (guarded : Contractive leaf) :
    coupled minus plus leaf = solution minus plus (leaf (coupled minus plus leaf)) :=
  funext (fixedPoint_unfold (solution_contractive minus plus guarded) _)

/-- Guarded runtime feedback and both unguarded ghost polarities satisfy one exact equation. -/
theorem coupled_equation {leaf : Candidate → Candidate} (guarded : Contractive leaf) :
    coupled minus plus leaf =
      operator minus plus (leaf (coupled minus plus leaf)) (coupled minus plus leaf) := by
  have outer := coupled_unfold minus plus guarded
  exact outer.trans ((solution_fixedPoint minus plus _).trans
    (congrArg (operator minus plus (leaf (coupled minus plus leaf))) outer.symm))

theorem coupled_downward {leaf : Candidate → Candidate} (guarded : Contractive leaf)
    (closed : ∀ self, Downward (leaf self)) : Downward (coupled minus plus leaf) :=
  Eq.mp (congrArg Downward (coupled_unfold minus plus guarded).symm)
    (solution_downward minus plus (closed _))

def body {depth : Nat} (leaf : WFTy depth) : WFTy (depth + 1) :=
  WFTy.union leaf.weaken
    (WFTy.union (WFTy.record minus (WFTy.neg (WFTy.var 0 (by omega))))
      (WFTy.record plus (WFTy.var 0 (by omega))))

def interpretation (ghost : FieldName → Bool) (env : Environment) {depth : Nat}
    (leaf : WFTy depth) : Candidate := solution minus plus (interpret ghost env leaf.raw)

/-- The actual mixed interpretation satisfies the recursive equation, including prefix closure. -/
theorem interpretation_equation (ghost : FieldName → Bool)
    (minusGhost : ghost minus = true) (plusGhost : ghost plus = true)
    (env : Environment) {depth : Nat} (leaf : WFTy depth) :
    interpret ghost (env.cons (interpretation minus plus ghost env leaf))
      (body minus plus leaf).raw =
      interpretation minus plus ghost env leaf := by
  change joint .union (interpret ghost (env.cons (interpretation minus plus ghost env leaf))
    (leaf.raw.lift 1))
    (joint .union
      (record ghost minus (negative (prefixClosure (interpretation minus plus ghost env leaf))))
      (record ghost plus (prefixClosure (interpretation minus plus ghost env leaf)))) = _
  simp only [interpretation]
  rw [interpret_lift, prefixClosure_eq
    (solution_downward minus plus (interpret_downward ghost leaf.raw env))]
  simpa only [record, minusGhost, plusGhost, ↓reduceIte, operator] using
    (solution_fixedPoint minus plus (interpret ghost env leaf.raw)).symm

end CDotFCCT.CTML.Mixed.GhostRowRecursion
