import CTMLCore.Declarative.IndexedDownward

/-!
# Testing a record interpretation that reflects subtyping

The current recursive target observes a record's fields at smaller indices and
discards their negative observations. That interpretation cannot justify native
record-subtyping inversion. Here both observations of a field are retained at the
current index. Negative observations also hold of terms without the selected
field. This is a model component, not a change to CTML's typing rules.

The inverse law is proved for the model's two-sided inclusion relation. Its cost
is that records no longer make a recursive occurrence contractive; function
boundaries would have to provide the recursion guard.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.TransparentRecord

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTMLCore.Indexed

def observes (field : FieldName) (payload : Term → Prop) (term : Term) : Prop :=
  ∃ (className : ClassName) (names : List FieldName) (fields : TermFields names) (value : Term),
    term = .record className fields ∧ TermFields.Lookup fields field value ∧ payload value

/-- A negative field observation is vacuous when the term has no such field. -/
def observesAll (field : FieldName) (payload : Term → Prop) (term : Term) : Prop :=
  ∀ (className : ClassName) (names : List FieldName) (fields : TermFields names) (value : Term),
    term = .record className fields → TermFields.Lookup fields field value → payload value

theorem observesAll_at {field : FieldName} {payload : Term → Prop} {className : ClassName}
    {names : List FieldName} {fields : TermFields names} {value : Term}
    (lookup : TermFields.Lookup fields field value) :
    observesAll field payload (.record className fields) ↔ payload value := by
  constructor
  · exact fun all => all _ _ _ _ rfl lookup
  · intro related otherClass otherNames otherFields otherValue equal otherLookup
    cases equal
    exact lookup.deterministic otherLookup ▸ related

theorem observesAll_mono {field : FieldName} {sub sup : Term → Prop}
    (included : ∀ term, sub term → sup term) {term : Term}
    (observed : observesAll field sub term) : observesAll field sup term :=
  fun className names fields value equal lookup =>
    included value (observed className names fields value equal lookup)

theorem observesAll_and {field : FieldName} {left right : Term → Prop} {term : Term} :
    observesAll field (fun value => left value ∧ right value) term ↔
      observesAll field left term ∧ observesAll field right term :=
  ⟨fun all => ⟨observesAll_mono (fun _ => And.left) all,
    observesAll_mono (fun _ => And.right) all⟩,
   fun both className names fields value equal lookup =>
    ⟨both.1 className names fields value equal lookup,
     both.2 className names fields value equal lookup⟩⟩

theorem observesAll_or {field : FieldName} {left right : Term → Prop} {term : Term} :
    observesAll field (fun value => left value ∨ right value) term ↔
      observesAll field left term ∨ observesAll field right term :=
  ⟨fun all => (Classical.em (observes field (fun _ => True) term)).elim
    (fun ⟨_, _, _, _, equal, lookup, _⟩ =>
      ((observesAll_at lookup).mp (equal ▸ all)).elim
        (fun related => .inl (equal.symm ▸ (observesAll_at lookup).mpr related))
        (fun related => .inr (equal.symm ▸ (observesAll_at lookup).mpr related)))
    (fun absent => .inl (fun className names fields value equal lookup =>
      False.elim (absent ⟨className, names, fields, value, equal, lookup, trivial⟩))),
   fun either => either.elim (observesAll_mono (fun _ => Or.inl))
    (observesAll_mono (fun _ => Or.inr))⟩

def record (field : FieldName) (payload : Candidate) : Candidate := fun n =>
  (observes field (payload n).1, observesAll field (payload n).2)

def singleton (field : FieldName) (value : Term) : Term :=
  .record "Record" (.cons field value .nil (by simp))

theorem observes_singleton {field : FieldName} {payload : Term → Prop} {value : Term} :
    observes field payload (singleton field value) ↔ payload value := by
  constructor
  · rintro ⟨className, names, fields, found, equal, lookup, observed⟩
    cases equal
    exact lookup.deterministic .here ▸ observed
  · exact fun observed => ⟨_, _, _, value, rfl, .here, observed⟩

theorem observesAll_singleton {field : FieldName} {payload : Term → Prop} {value : Term} :
    observesAll field payload (singleton field value) ↔ payload value := observesAll_at .here

theorem observes_mono {field : FieldName} {sub sup : Term → Prop}
    (included : ∀ term, sub term → sup term) {term : Term}
    (observed : observes field sub term) : observes field sup term :=
  let ⟨className, names, fields, value, equal, lookup, payload⟩ := observed
  ⟨className, names, fields, value, equal, lookup, included value payload⟩

theorem monotone {sub sup : Candidate} {n : Nat} (included : Includes sub sup n)
    (field : FieldName) : Includes (record field sub) (record field sup) n :=
  fun k within _ => ⟨observes_mono (fun value => (included k within value).1),
    observesAll_mono (fun value => (included k within value).2)⟩

/-- Reflect both positive and negative inclusions, without assuming inhabitants of the field. -/
theorem inverse {field : FieldName} {sub sup : Candidate} {n : Nat}
    (included : Includes (record field sub) (record field sup) n) : Includes sub sup n := by
  intro k within value
  exact ⟨fun observed => observes_singleton.mp
      ((included k within (singleton field value)).1 (observes_singleton.mpr observed)),
    fun observed => observesAll_singleton.mp
      ((included k within (singleton field value)).2 (observesAll_singleton.mpr observed))⟩

theorem faithful {field : FieldName} {sub sup : Candidate} {n : Nat} :
    Includes (record field sub) (record field sup) n ↔ Includes sub sup n :=
  ⟨inverse, fun included => monotone included field⟩

theorem downward {payload : Candidate} (closed : Downward payload) (field : FieldName) :
    Downward (record field payload) :=
  fun m n within _ => ⟨observes_mono (fun value => (closed m n within value).1),
    observesAll_mono (fun value => (closed m n within value).2)⟩

theorem congr {field : FieldName} {left right : Candidate} {n : Nat}
    (agree : left n = right n) : record field left n = record field right n :=
  congrArg (fun observation : Observation =>
    (observes field observation.1, observesAll field observation.2)) agree

theorem observes_or {field : FieldName} {left right : Term → Prop} {term : Term} :
    observes field (fun value => left value ∨ right value) term ↔
      observes field left term ∨ observes field right term := by
  constructor
  · rintro ⟨className, names, fields, value, equal, lookup, alternatives⟩
    exact alternatives.elim
      (fun observed => .inl ⟨className, names, fields, value, equal, lookup, observed⟩)
      (fun observed => .inr ⟨className, names, fields, value, equal, lookup, observed⟩)
  · exact fun alternatives => alternatives.elim
      (observes_mono (fun _ => Or.inl)) (observes_mono (fun _ => Or.inr))

theorem observes_and {field : FieldName} {left right : Term → Prop} {term : Term} :
    observes field (fun value => left value ∧ right value) term ↔
      observes field left term ∧ observes field right term := by
  constructor
  · exact fun observed => ⟨observes_mono (fun _ => And.left) observed,
      observes_mono (fun _ => And.right) observed⟩
  · rintro ⟨⟨className, names, fields, value, rfl, lookup, content⟩,
      ⟨className', names', fields', value', equal, lookup', content'⟩⟩
    cases equal
    exact ⟨className, names, fields, value, rfl, lookup,
      content, lookup.deterministic lookup' ▸ content'⟩

theorem joint_distribution (kind : Joint) (field : FieldName) (left right : Candidate) (n : Nat) :
    record field (joint kind left right) n =
      joint kind (record field left) (record field right) n :=
  match kind with
  | .union => Prod.ext (funext fun _ => propext observes_or)
      (funext fun _ => propext observesAll_and)
  | .intersection => Prod.ext (funext fun _ => propext observes_and)
      (funext fun _ => propext observesAll_or)

/-- Adding a record outside an already guarded body preserves its contractiveness. -/
theorem guarded {body : Candidate → Candidate} (contractive : Contractive body)
    (field : FieldName) : Contractive (fun self => record field (body self)) :=
  fun n left right agree => congr (contractive n left right agree)

theorem guarded_thunk (field : FieldName) (param : Candidate) :
    Contractive (fun self => record field (arrow param self)) :=
  guarded (body := fun self => arrow param self)
    (fun _ _ _ agree => arrow_congr (fun _ _ => rfl) agree) field

theorem guarded_negative (field : FieldName) (result : Candidate) :
    Contractive (fun self => record field (arrow self result)) :=
  guarded (body := fun self => arrow self result)
    (fun _ _ _ agree => arrow_congr agree (fun _ _ => rfl)) field

theorem not_contractive (field : FieldName) : ¬ Contractive (record field) := by
  intro contractive
  have same := contractive 0 (fun _ => (fun _ => False, fun _ => False))
    (fun _ => (fun _ => True, fun _ => False))
    (fun k smaller => False.elim (Nat.not_lt_zero k smaller))
  exact observes_singleton.mp (Eq.mpr
    (congrArg (fun observation : Observation => observation.1 (singleton field (.var 0))) same)
    (observes_singleton.mpr trivial))

end CDotFCCT.CTML.TransparentRecord
