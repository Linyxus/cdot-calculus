import CDotFCCT.CTML.MixedInterpretation
import CDotFCCT.CTML.TransparentRuntime
import CTMLCore.Declarative.IndexedElimination
import CTMLCore.Declarative.Typing

/-! # Evaluation of native record fields in the indexed model -/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTMLCore.Indexed

inductive FieldsComputation (ghost : FieldName → Bool) {depth : Nat} (env : Environment) (n : Nat) :
    {names : List FieldName} → TermFields names → List (FieldName × WFTy depth) → Prop where
  | nil : FieldsComputation ghost env n .nil []
  | cons {names : List FieldName} {name : FieldName} {value : Term}
      {tail : TermFields names} {fresh : name ∉ names} {type : WFTy depth}
      {types : List (FieldName × WFTy depth)} :
      Computation (fun k => (interpret ghost env type.raw k).1) n value →
      FieldsComputation ghost env n tail types →
      FieldsComputation ghost env n (.cons name value tail fresh) ((name, type) :: types)

variable {ghost : FieldName → Bool}

theorem FieldsComputation.downward {depth m n : Nat} {env : Environment}
    {names : List FieldName} {fields : TermFields names} {types : List (FieldName × WFTy depth)}
    (typing : FieldsComputation ghost env n fields types) (within : m ≤ n) :
    FieldsComputation ghost env m fields types :=
  match typing with
  | .nil => .nil
  | .cons head tail =>
      .cons (head.downward (interpret_downward ghost _ env) within) (tail.downward within)

/-- Select one legal field step, retaining observations with one less unit of budget. -/
theorem FieldsComputation.advance {depth n : Nat} {env : Environment}
    {names : List FieldName} {fields : TermFields names} {types : List (FieldName × WFTy depth)}
    (typing : FieldsComputation ghost env (n + 1) fields types) :
    TermFields.AllValues fields ∨ ∃ next,
      TermFields.Step fields next ∧ FieldsComputation ghost env n next types :=
  match typing with
  | .nil => .inl .nil
  | .cons head tail =>
      match head.progress with
      | .inl value =>
          match tail.advance with
          | .inl values => .inl (.cons value values)
          | .inr ⟨_next, step, rest⟩ => .inr ⟨_, .tail value step,
              .cons (head.downward (interpret_downward ghost _ env) (Nat.le_succ n)) rest⟩
      | .inr ⟨_next, step⟩ => .inr ⟨_, .head step,
          .cons (head.afterStep step) (tail.downward (Nat.le_succ n))⟩

theorem FieldsComputation.lookup {depth n : Nat} {env : Environment}
    {names : List FieldName} {fields : TermFields names} {types : List (FieldName × WFTy depth)}
    (typing : FieldsComputation ghost env n fields types) {entry : FieldName × WFTy depth}
    (member : entry ∈ types) :
    ∃ value, TermFields.Lookup fields entry.1 value ∧
      Computation (fun k => (interpret ghost env entry.2.raw k).1) n value := by
  induction typing with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, .here, head⟩
    · exact (ih member).elim fun value related => ⟨value, .there related.1, related.2⟩

private theorem recordFold_observed {depth n : Nat} {env : Environment} {term : Term}
    (types : List (FieldName × WFTy depth)) (start : WFTy depth)
    (initial : (interpret ghost env start.raw n).1 term)
    (entries : ∀ entry ∈ types,
      (Mixed.record ghost entry.1 (interpret ghost env entry.2.raw) n).1 term) :
    (interpret ghost env
      (types.foldl (fun result entry => WFTy.intersection result (WFTy.record entry.1 entry.2))
        start).raw n).1 term := by
  induction types generalizing start with
  | nil => exact initial
  | cons entry tail ih =>
    exact ih _ ⟨initial, entries entry List.mem_cons_self⟩
      (fun found member => entries found (List.mem_cons_of_mem entry member))

theorem FieldsComputation.observed {depth n : Nat} {env : Environment}
    {names : List FieldName} {fields : TermFields names} {types : List (FieldName × WFTy depth)}
    (typing : FieldsComputation ghost env n fields types) (className : ClassName)
    (values : TermFields.AllValues fields) :
    (interpret ghost env (recordResultType className types).raw n).1
      (.record className fields) := by
  apply recordFold_observed types (WFTy.cls className) ⟨names, fields, rfl⟩
  intro entry member
  obtain ⟨value, lookup, computation⟩ := typing.lookup member
  cases marked : ghost entry.1 with
  | false =>
      simp only [Mixed.record, marked, Bool.false_eq_true, ↓reduceIte]
      exact ⟨className, names, fields, value, rfl, lookup, fun k smaller =>
        (interpret_downward ghost entry.2.raw env k n (Nat.le_of_lt smaller) value).1
          (computation.atValue (values.lookup lookup))⟩
  | true =>
      simp only [Mixed.record, marked, ↓reduceIte]
      exact ⟨className, names, fields, value, rfl, lookup,
        computation.atValue (values.lookup lookup)⟩

theorem FieldsComputation.record {depth n : Nat} {env : Environment}
    {names : List FieldName} {fields : TermFields names} {types : List (FieldName × WFTy depth)}
    (typing : FieldsComputation ghost env n fields types) (className : ClassName) :
    Computation (fun k => (interpret ghost env (recordResultType className types).raw k).1)
      n (.record className fields) := by
  induction n generalizing fields with
  | zero =>
    exact .zero fun value => match value with
      | .record _ _ all => typing.observed className all
  | succ n ih =>
    exact typing.advance.elim
      (fun all => .ofValue (.record className fields all) (typing.observed className all))
      (fun ⟨next, step, rest⟩ => .ofStep (.recordField step) (ih rest))

/-- Projection spends a reduction step; the field was already observable at the current index. -/
theorem projection {payload : Candidate} (downward : Downward payload)
    {field : FieldName} {n : Nat} {term : Term}
    (recordTyping : Computation (fun k => (Mixed.record ghost field payload k).1) n term) :
    Computation (fun k => (payload k).1) n (.proj term field) := by
  cases marked : ghost field with
  | false =>
      apply Computation.projection
      simpa only [Mixed.record, marked, Bool.false_eq_true, ↓reduceIte] using recordTyping
  | true =>
      apply Transparent.projection downward
      simpa only [Mixed.record, marked, ↓reduceIte] using recordTyping

end CDotFCCT.CTML.Mixed
