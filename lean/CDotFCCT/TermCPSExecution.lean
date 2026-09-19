import CDotFCCT.TermCPSRecords
import CTMLCore.Language.EvaluationTheory

/-! # The runtime object constructor reaches a native record -/

set_option autoImplicit false

namespace CDotFCCT.TermCPS

open CTMLCore.Syntax CTMLCore.Evaluation

/-- Forcing the Z-based constructor reaches a native record with the same field
names. The existential result hides only the explicit substitution expression
that ties the field bodies to the recursive self thunk. -/
theorem force_record {names : List String} (contents : TermFields names)
    (values : TermFields.AllValues contents) :
    ∃ result : TermFields names,
      Steps (.app (.fix (.abs (.abs (.record "DOT" contents)))) unit)
        (.record "DOT" result) ∧ TermFields.AllValues result := by
  exact ⟨_, .trans (.appHead _ (.fixUnfold (.abs _)))
    (.trans (.appBeta _ _ (.record _ _ .nil))
      (.trans (.appHead _ (.appBeta _ _ (.abs _)))
        (.trans (.appBeta _ _ (.record _ _ .nil)) .refl))),
    (((values.renameWith _).substWith _).substWith _).substWith _⟩

variable [CDot.Signature]

/-- This execution property concerns the actual output of the general compiler. -/
theorem compiled_object_forces (env : Env) (tag : CDot.Path)
    (tagMember : CDot.Signature.TypLabel) (type : CDot.Typ) (definitions : CDot.Defs)
    (allowed : Core.definitionsTestFree definitions = true) :
    ∃ compiled : Term, ∃ names : List String, ∃ contents : TermFields names,
      value env (.new tag tagMember type definitions) = some compiled ∧
      Steps (.app compiled unit) (.record "DOT" contents) ∧
      Value (.record "DOT" contents) := by
  obtain ⟨entries, equal⟩ := fields_total (env.bind.weaken 1) definitions allowed
  obtain ⟨result, steps, values⟩ := force_record (recordFields entries).2
    (recordFields_values entries (fields_suspended (env.bind.weaken 1) definitions equal))
  refine ⟨_, _, result, ?_, steps, .record _ _ values⟩
  simp [value, equal]

end CDotFCCT.TermCPS
