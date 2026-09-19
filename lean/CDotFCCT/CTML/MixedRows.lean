import CDotFCCT.CTML.MixedInterpretation
import CDotFCCT.CTML.TransparentRows

/-!
# Shared type carriers at designated ghost labels

The native labelled-union syntax still reflects each component, provided all its
labels are designated ghost labels. Payload types may contain ordinary recursive
records. Reflection does not require inhabitants of those payload types.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Indexed

abbrev row := @Transparent.row

variable (ghost : FieldName → Bool)

theorem row_positive {depth : Nat} (labels : List FieldName) (types : FieldName → WFTy depth)
    (reflective : ∀ field ∈ labels, ghost field = true)
    (env : Environment) (n : Nat) (field : FieldName) (value : Term) :
    (interpret ghost env (row labels types).raw n).1 (TransparentRecord.singleton field value) ↔
      field ∈ labels ∧ (interpret ghost env (types field).raw n).1 value := by
  induction labels with
  | nil => exact ⟨False.elim, fun impossible => (List.not_mem_nil impossible.1).elim⟩
  | cons head rest ih =>
      change ((record ghost head (interpret ghost env (types head).raw) n).1
        (TransparentRecord.singleton field value)) ∨ _ ↔ _
      simp only [record, reflective head List.mem_cons_self, ↓reduceIte,
        TransparentRecord.record]
      rw [TransparentRecord.observes_singleton_label,
        ih (fun found member => reflective found (List.mem_cons_of_mem head member)), List.mem_cons]
      by_cases same : head = field
      · simp [same]
      · simp [same, Ne.symm same]

theorem row_negative {depth : Nat} (labels : List FieldName) (types : FieldName → WFTy depth)
    (reflective : ∀ field ∈ labels, ghost field = true)
    (env : Environment) (n : Nat) (field : FieldName) (value : Term) :
    (interpret ghost env (row labels types).raw n).2 (TransparentRecord.singleton field value) ↔
      (field ∈ labels → (interpret ghost env (types field).raw n).2 value) := by
  induction labels with
  | nil => exact ⟨fun _ member => (List.not_mem_nil member).elim, fun _ => trivial⟩
  | cons head rest ih =>
      change ((record ghost head (interpret ghost env (types head).raw) n).2
        (TransparentRecord.singleton field value)) ∧ _ ↔ _
      simp only [record, reflective head List.mem_cons_self, ↓reduceIte,
        TransparentRecord.record]
      rw [TransparentRecord.observesAll_singleton_label,
        ih (fun found member => reflective found (List.mem_cons_of_mem head member)), List.mem_cons]
      by_cases same : head = field
      · simp [same]
        exact fun related _ => related
      · simp [same, Ne.symm same]

/-- Carrier views recover one shared component through arbitrary intermediate constraints. -/
theorem row_inverse {depth : Nat} {labels : List FieldName}
    (reflective : ∀ field ∈ labels, ghost field = true)
    {sub sup : FieldName → WFTy depth} {env : Environment} {n : Nat} {field : FieldName}
    (member : field ∈ labels)
    (included : Includes (interpret ghost env (row labels sub).raw)
      (interpret ghost env (row labels sup).raw) n) :
    Includes (interpret ghost env (sub field).raw) (interpret ghost env (sup field).raw) n :=
  fun k within value =>
    ⟨fun observed => ((row_positive ghost labels sup reflective env k field value).mp
      ((included k within (TransparentRecord.singleton field value)).1
        ((row_positive ghost labels sub reflective env k field value).mpr ⟨member, observed⟩))).2,
     fun observed => (row_negative ghost labels sub reflective env k field value).mp
      ((included k within (TransparentRecord.singleton field value)).2
        ((row_negative ghost labels sup reflective env k field value).mpr
          (fun _ => observed))) member⟩

theorem row_mono {s : SubtypingContext} (labels : List FieldName)
    {sub sup : FieldName → WFTy s.typeDepth}
    (included : ∀ field ∈ labels, CTMLCore.Subtype s (sub field) (sup field)) :
    CTMLCore.Subtype s (row labels sub) (row labels sup) :=
  Transparent.row_mono labels included

end CDotFCCT.CTML.Mixed
