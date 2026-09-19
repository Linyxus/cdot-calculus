import CDotFCCT.CTML.TransparentInterpretation
import CTMLCore.Declarative.IndexedElimination
import CTMLCore.Declarative.Typing

/-! # Evaluation of native record fields in the indexed model -/

set_option autoImplicit false

namespace CDotFCCT.CTML.Transparent

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTMLCore.Indexed

inductive FieldsComputation {depth : Nat} (env : Environment) (n : Nat) :
    {names : List FieldName} → TermFields names → List (FieldName × WFTy depth) → Prop where
  | nil : FieldsComputation env n .nil []
  | cons {names : List FieldName} {name : FieldName} {value : Term}
      {tail : TermFields names} {fresh : name ∉ names} {type : WFTy depth}
      {types : List (FieldName × WFTy depth)} :
      Computation (fun k => (interpret env type.raw k).1) n value →
      FieldsComputation env n tail types →
      FieldsComputation env n (.cons name value tail fresh) ((name, type) :: types)

theorem FieldsComputation.downward {depth m n : Nat} {env : Environment}
    {names : List FieldName} {fields : TermFields names} {types : List (FieldName × WFTy depth)}
    (typing : FieldsComputation env n fields types) (within : m ≤ n) :
    FieldsComputation env m fields types :=
  match typing with
  | .nil => .nil
  | .cons head tail =>
      .cons (head.downward (interpret_downward _ env) within) (tail.downward within)

/-- Select one legal field step, retaining observations with one less unit of budget. -/
theorem FieldsComputation.advance {depth n : Nat} {env : Environment}
    {names : List FieldName} {fields : TermFields names} {types : List (FieldName × WFTy depth)}
    (typing : FieldsComputation env (n + 1) fields types) :
    TermFields.AllValues fields ∨ ∃ next,
      TermFields.Step fields next ∧ FieldsComputation env n next types :=
  match typing with
  | .nil => .inl .nil
  | .cons head tail =>
      match head.progress with
      | .inl value =>
          match tail.advance with
          | .inl values => .inl (.cons value values)
          | .inr ⟨_next, step, rest⟩ => .inr ⟨_, .tail value step,
              .cons (head.downward (interpret_downward _ env) (Nat.le_succ n)) rest⟩
      | .inr ⟨_next, step⟩ => .inr ⟨_, .head step,
          .cons (head.afterStep step) (tail.downward (Nat.le_succ n))⟩

theorem FieldsComputation.lookup {depth n : Nat} {env : Environment}
    {names : List FieldName} {fields : TermFields names} {types : List (FieldName × WFTy depth)}
    (typing : FieldsComputation env n fields types) {entry : FieldName × WFTy depth}
    (member : entry ∈ types) :
    ∃ value, TermFields.Lookup fields entry.1 value ∧
      Computation (fun k => (interpret env entry.2.raw k).1) n value := by
  induction typing with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, .here, head⟩
    · exact (ih member).elim fun value related => ⟨value, .there related.1, related.2⟩

private theorem recordFold_observed {depth n : Nat} {env : Environment} {term : Term}
    (types : List (FieldName × WFTy depth)) (start : WFTy depth)
    (initial : (interpret env start.raw n).1 term)
    (entries : ∀ entry ∈ types,
      (TransparentRecord.record entry.1 (interpret env entry.2.raw) n).1 term) :
    (interpret env
      (types.foldl (fun result entry => WFTy.intersection result (WFTy.record entry.1 entry.2))
        start).raw n).1 term := by
  induction types generalizing start with
  | nil => exact initial
  | cons entry tail ih =>
    exact ih _ ⟨initial, entries entry List.mem_cons_self⟩
      (fun found member => entries found (List.mem_cons_of_mem entry member))

theorem FieldsComputation.observed {depth n : Nat} {env : Environment}
    {names : List FieldName} {fields : TermFields names} {types : List (FieldName × WFTy depth)}
    (typing : FieldsComputation env n fields types) (className : ClassName)
    (values : TermFields.AllValues fields) :
    (interpret env (recordResultType className types).raw n).1 (.record className fields) := by
  apply recordFold_observed types (WFTy.cls className) ⟨names, fields, rfl⟩
  exact fun entry member => (typing.lookup member).elim fun value related =>
    ⟨className, names, fields, value, rfl, related.1,
      related.2.atValue (values.lookup related.1)⟩

theorem FieldsComputation.record {depth n : Nat} {env : Environment}
    {names : List FieldName} {fields : TermFields names} {types : List (FieldName × WFTy depth)}
    (typing : FieldsComputation env n fields types) (className : ClassName) :
    Computation (fun k => (interpret env (recordResultType className types).raw k).1)
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
    (recordTyping : Computation (fun k => (TransparentRecord.record field payload k).1) n term) :
    Computation (fun k => (payload k).1) n (.proj term field) := by
  apply recordTyping.eliminate (Term.proj · field) (fun _ value => nomatch value)
    (Step.projHead field)
  rintro k within value isValue ⟨className, names, fields, selected, rfl, lookup, content⟩
  exact match isValue with
    | .record _ _ all => ⟨selected, .proj isValue lookup,
        .ofValue (all.lookup lookup) ((downward k (k + 1) (Nat.le_succ k) selected).1 content)⟩

end CDotFCCT.CTML.Transparent
