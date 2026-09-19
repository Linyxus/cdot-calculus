import CDotFCCT.CTML.TransparentInterpretation
import CTMLCore.Declarative.Lattice

/-!
# Labelled unions as faithful carriers of several type components

A singleton record at label `a` observes exactly the `a` alternative of a union
of labelled record types. This holds in both polarities because a missing field
satisfies the negative record observation. Empty components need no inhabitants.

These are ghost type carriers; runtime object records still use intersections.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.TransparentRecord

open CTMLCore CTMLCore.Syntax CTMLCore.Indexed

theorem observes_singleton_label {field selected : FieldName} {payload : Term → Prop}
    {value : Term} : observes field payload (singleton selected value) ↔
      field = selected ∧ payload value := by
  constructor
  · rintro ⟨className, names, fields, found, equal, lookup, related⟩
    cases equal
    have same := List.mem_singleton.mp lookup.mem_names
    subst field
    exact ⟨rfl, lookup.deterministic .here ▸ related⟩
  · rintro ⟨rfl, related⟩
    exact observes_singleton.mpr related

theorem observesAll_singleton_label {field selected : FieldName} {payload : Term → Prop}
    {value : Term} : observesAll field payload (singleton selected value) ↔
      (field = selected → payload value) := by
  constructor
  · rintro all rfl
    exact observesAll_singleton.mp all
  · intro related className names fields found equal lookup
    cases equal
    have same := List.mem_singleton.mp lookup.mem_names
    subst field
    exact lookup.deterministic .here ▸ related rfl

end CDotFCCT.CTML.TransparentRecord

namespace CDotFCCT.CTML.Transparent

open CTMLCore CTMLCore.Syntax CTMLCore.Indexed

def row {depth : Nat} (labels : List FieldName) (types : FieldName → WFTy depth) : WFTy depth :=
  match labels with
  | [] => WFTy.bottom
  | field :: rest => WFTy.union (WFTy.record field (types field)) (row rest types)

theorem row_positive {depth : Nat} (labels : List FieldName) (types : FieldName → WFTy depth)
    (env : Environment) (n : Nat) (field : FieldName) (value : Term) :
    (interpret env (row labels types).raw n).1 (TransparentRecord.singleton field value) ↔
      field ∈ labels ∧ (interpret env (types field).raw n).1 value := by
  induction labels with
  | nil => exact ⟨False.elim, fun impossible => (List.not_mem_nil impossible.1).elim⟩
  | cons head rest ih =>
      change TransparentRecord.observes head _ (TransparentRecord.singleton field value) ∨ _ ↔ _
      rw [TransparentRecord.observes_singleton_label, ih, List.mem_cons]
      by_cases same : head = field
      · simp [same]
      · simp [same, Ne.symm same]

theorem row_negative {depth : Nat} (labels : List FieldName) (types : FieldName → WFTy depth)
    (env : Environment) (n : Nat) (field : FieldName) (value : Term) :
    (interpret env (row labels types).raw n).2 (TransparentRecord.singleton field value) ↔
      (field ∈ labels → (interpret env (types field).raw n).2 value) := by
  induction labels with
  | nil => exact ⟨fun _ member => (List.not_mem_nil member).elim, fun _ => trivial⟩
  | cons head rest ih =>
      change TransparentRecord.observesAll head _ (TransparentRecord.singleton field value) ∧ _ ↔ _
      rw [TransparentRecord.observesAll_singleton_label, ih, List.mem_cons]
      by_cases same : head = field
      · simp [same]
        exact fun related _ => related
      · simp [same, Ne.symm same]

theorem row_inverse {depth : Nat} {labels : List FieldName}
    {sub sup : FieldName → WFTy depth} {env : Environment} {n : Nat} {field : FieldName}
    (member : field ∈ labels)
    (included : Includes (interpret env (row labels sub).raw)
      (interpret env (row labels sup).raw) n) :
    Includes (interpret env (sub field).raw) (interpret env (sup field).raw) n :=
  fun k within value =>
    ⟨fun observed => ((row_positive labels sup env k field value).mp
      ((included k within (TransparentRecord.singleton field value)).1
        ((row_positive labels sub env k field value).mpr ⟨member, observed⟩))).2,
     fun observed => (row_negative labels sub env k field value).mp
      ((included k within (TransparentRecord.singleton field value)).2
        ((row_negative labels sup env k field value).mpr (fun _ => observed))) member⟩

theorem row_mono {s : SubtypingContext} (labels : List FieldName)
    {sub sup : FieldName → WFTy s.typeDepth}
    (included : ∀ field ∈ labels, CTMLCore.Subtype s (sub field) (sup field)) :
    CTMLCore.Subtype s (row labels sub) (row labels sup) := by
  induction labels with
  | nil => exact .refl
  | cons field rest ih =>
      exact CTMLCore.Subtype.unionMono (.record (included field List.mem_cons_self))
        (ih (fun found member => included found (List.mem_cons_of_mem field member)))

end CDotFCCT.CTML.Transparent
