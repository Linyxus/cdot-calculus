import CDotFCCT.TermCPSExecution
import CTMLCore.Language.TermSubstitutionAlgebra
import CTMLCore.Language.FixpointReduction

/-!
# Execution of compiled field lookup

The object constructor substitutes its delayed self reference into every field.
Lookup must commute with those substitutions before a source field can be related
to the computation selected from the forced native record.
-/

set_option autoImplicit false

namespace CDotFCCT.TermCPS

open CTMLCore.Syntax CTMLCore.Evaluation

/-- The self thunk supplied by the first application of the unfolded fixpoint. -/
def objectSelf {names : List String} (contents : TermFields names) : Term :=
  (Term.abs (.app (.fix
    (((.abs (.abs (.record "DOT" contents)) : Term).lift 1).lift 1)) (.var 0))).substAt 0 unit

/-- The constructor's substituted self is precisely the native Z primitive's delayed self. -/
theorem objectSelf_eq_delayedFix {names : List String} (contents : TermFields names) :
    objectSelf contents = delayedFix (.abs (.abs (.record "DOT" contents))) :=
  delayedFix_lift_subst (.abs (.abs (.record "DOT" contents))) unit

/-- Substitute the delayed self thunk and the unit argument into a field. -/
def closeObjectField {names : List String} (contents : TermFields names) (field : Term) : Term :=
  (field.substAt 1 ((objectSelf contents).lift 1)).substAt 0 unit

def closeObjectFields {names : List String} (contents : TermFields names) : TermFields names :=
  (contents.substAt 1 ((objectSelf contents).lift 1)).substAt 0 unit

theorem force_record_exact {names : List String} (contents : TermFields names) :
    Steps (.app (.fix (.abs (.abs (.record "DOT" contents)))) unit)
      (.record "DOT" (closeObjectFields contents)) := by
  refine .trans (.appHead _ (.fixUnfold (.abs _))) ?_
  refine .trans (.appBeta _ _ (.record _ _ .nil)) ?_
  change Steps (.app (.app
    (((.abs (.abs (.record "DOT" contents)) : Term).lift 1).substAt 0 unit)
      (objectSelf contents)) unit) _
  rw [Term.lift_substAt_cancel]
  refine .trans (.appHead _ (.appBeta _ _ (.abs _))) ?_
  rw [Term.substAt_abs]
  exact .trans (.appBeta _ _ (.record _ _ .nil)) .refl

/-- A runtime self reference returns the same record, with one extra administrative beta step. -/
theorem self_force_record_exact {names : List String} (contents : TermFields names) :
    Steps (.app (objectSelf contents) unit) (.record "DOT" (closeObjectFields contents)) := by
  rw [objectSelf_eq_delayedFix]
  exact .trans (.delayedFix_beta (.record _ _ .nil)) (force_record_exact contents)

theorem closeObjectFields_values {names : List String} {contents : TermFields names}
    (values : TermFields.AllValues contents) :
    TermFields.AllValues (closeObjectFields contents) :=
  (values.substWith _).substWith _

theorem closeObjectFields_lookup {names : List String} {contents : TermFields names}
    {name : String} {field : Term} (lookup : TermFields.Lookup contents name field) :
    TermFields.Lookup (closeObjectFields contents) name (closeObjectField contents field) :=
  (lookup.substAt 1 ((objectSelf contents).lift 1)).substAt 0 unit

/-- Projection selects precisely the source field with its recursive self substituted. -/
theorem force_projection {names : List String} {contents : TermFields names}
    (values : TermFields.AllValues contents) {name : String} {field : Term}
    (lookup : TermFields.Lookup contents name field) :
    Steps (.proj (.app (.fix (.abs (.abs (.record "DOT" contents)))) unit) name)
      (closeObjectField contents field) :=
  ((force_record_exact contents).projHead name).trans'
    (.single (.proj (.record _ _ (closeObjectFields_values values))
      (closeObjectFields_lookup lookup)))

/-- The same substitutions underneath a field's continuation binder. -/
def closeObjectFieldBody {names : List String} (contents : TermFields names)
    (body : Term) : Term :=
  (body.substAt 2 (((objectSelf contents).lift 1).lift 1)).substAt 1 (unit.lift 1)

theorem closeObjectField_abs {names : List String} (contents : TermFields names) (body : Term) :
    closeObjectField contents (.abs body) = .abs (closeObjectFieldBody contents body) := by
  simp only [closeObjectField, closeObjectFieldBody, Term.substAt_abs]

/-- After selecting the suspended field, the caller supplies its continuation. -/
theorem force_field_call {names : List String} {contents : TermFields names}
    (values : TermFields.AllValues contents) {name : String} {body continuation : Term}
    (lookup : TermFields.Lookup contents name (.abs body)) (hk : Value continuation) :
    Steps (.app (.proj (.app (.fix (.abs (.abs (.record "DOT" contents)))) unit) name)
      continuation) ((closeObjectFieldBody contents body).substAt 0 continuation) := by
  refine ((force_projection values lookup).appHead continuation).trans' ?_
  rw [closeObjectField_abs]
  exact .single (.appBeta _ _ hk)

theorem self_force_field_call {names : List String} {contents : TermFields names}
    (values : TermFields.AllValues contents) {name : String} {body continuation : Term}
    (lookup : TermFields.Lookup contents name (.abs body)) (hk : Value continuation) :
    Steps (.app (.proj (.app (objectSelf contents) unit) name) continuation)
      ((closeObjectFieldBody contents body).substAt 0 continuation) := by
  rw [objectSelf_eq_delayedFix]
  exact .trans (.appHead continuation (.projHead name (.delayedFix_beta (.record _ _ .nil))))
    (force_field_call values lookup hk)

variable [CDot.Signature]

theorem fields_cons_iff (env : Env) (rest : CDot.Defs) (name : CDot.Signature.TrmLabel)
    (rhs : CDot.DefRhs) (entries : List (String × Term)) :
    fields env (.cons rest (.trm name rhs)) = some entries ↔
      ∃ earlier code, fields env rest = some earlier ∧ field env rhs = some code ∧
        earlier ++ [(env.fieldName name, code)] = entries := by
  simp [fields, Option.bind_eq_some_iff]

theorem fields_lookup (env : Env) (definitions : CDot.Defs)
    {entries : List (String × Term)} (compiled : fields env definitions = some entries)
    {name : CDot.Signature.TrmLabel} {rhs : CDot.DefRhs}
    (lookup : definitions.Has (.trm name rhs)) :
    ∃ code, field env rhs = some code ∧ (env.fieldName name, code) ∈ entries := by
  cases definitions with
  | nil => simp [CDot.Defs.Has, CDot.Defs.get] at lookup
  | cons rest definition =>
      cases definition with
      | typ member type =>
          exact fields_lookup env rest compiled (by
            simpa [CDot.Defs.Has, CDot.Defs.get, CDot.Def.label] using lookup)
      | trm label body =>
          obtain ⟨earlier, code, restEqual, bodyEqual, rfl⟩ :=
            (fields_cons_iff env rest label body entries).mp compiled
          by_cases same : label = name
          · have rhsEqual : body = rhs := by
              simpa [CDot.Defs.Has, CDot.Defs.get, CDot.Def.label, same] using lookup
            exact ⟨code, rhsEqual ▸ bodyEqual, same ▸ List.mem_append_right _ List.mem_cons_self⟩
          · obtain ⟨found, fieldEqual, membership⟩ := fields_lookup env rest restEqual (by
              simpa [CDot.Defs.Has, CDot.Defs.get, CDot.Def.label, same] using lookup)
            exact ⟨found, fieldEqual, List.mem_append_left _ membership⟩

theorem definitionNames_openRec (definitions : CDot.Defs) (index : Nat) (x : CDot.Var) :
    definitionNames (definitions.openRec index x) = definitionNames definitions :=
  match definitions with
  | .nil => rfl
  | .cons rest (.typ ..) => definitionNames_openRec rest index x
  | .cons rest (.trm name _) => congrArg (name :: ·) (definitionNames_openRec rest index x)

/-- This applies to arbitrary object typing derivations, including subsumption. -/
theorem typed_object_names_distinct {context : CDot.Ctx} {tag : CDot.Path}
    {member : CDot.Signature.TypLabel} {selfType type : CDot.Typ} {definitions : CDot.Defs}
    (typing : Core.Typing context (.val (.new tag member selfType definitions)) type) :
    (definitionNames definitions).Nodup :=
  match typing with
  | .newIntro excluded fields _ => by
      simpa only [CDot.Defs.open, definitionNames_openRec] using
        definitionNames_distinct (fields (Core.fresh excluded) (Core.fresh_not_mem excluded))
  | .sub term _ => typed_object_names_distinct term

theorem compiled_fields_distinct (env : Env) (definitions : CDot.Defs)
    (distinct : (definitionNames definitions).Nodup)
    (injective : ∀ left ∈ definitionNames definitions, ∀ right ∈ definitionNames definitions,
      env.fieldName left = env.fieldName right → left = right)
    {entries : List (String × Term)} (compiled : fields env definitions = some entries) :
    (entries.map Prod.fst).Nodup := by
  rw [fields_names env definitions compiled]
  exact List.Nodup.map_on
    (fun left hl right hr => injective left (List.mem_reverse.mp hl)
      right (List.mem_reverse.mp hr)) (List.nodup_reverse.mpr distinct)

/-- For any typed core object, selecting an existing field executes its compiled
right-hand side with the object's own delayed self and the caller's continuation.
The result retains the exact substitution expression, including open outer variables. -/
theorem compiled_object_field_call (env : Env) {context : CDot.Ctx} {tag : CDot.Path}
    {member : CDot.Signature.TypLabel} {selfType type : CDot.Typ} {definitions : CDot.Defs}
    (typing : Core.Typing context (.val (.new tag member selfType definitions)) type)
    (injective : ∀ left ∈ definitionNames definitions, ∀ right ∈ definitionNames definitions,
      env.fieldName left = env.fieldName right → left = right)
    {name : CDot.Signature.TrmLabel} {rhs : CDot.DefRhs}
    (lookup : definitions.Has (.trm name rhs)) {continuation : Term} (hk : Value continuation) :
    ∃ compiled entries body,
      value env (.new tag member selfType definitions) = some compiled ∧
      fields (env.bind.weaken 1) definitions = some entries ∧
      field (env.bind.weaken 1) rhs = some (.abs body) ∧
      Steps (.app (.proj (.app compiled unit) (env.fieldName name)) continuation)
        ((closeObjectFieldBody (recordFields entries).2 body).substAt 0 continuation) := by
  obtain ⟨entries, entriesEqual⟩ :=
    fields_total (env.bind.weaken 1) definitions typing.testFree
  obtain ⟨code, codeEqual, membership⟩ :=
    fields_lookup (env.bind.weaken 1) definitions entriesEqual lookup
  obtain ⟨body, rfl⟩ := field_suspended (env.bind.weaken 1) rhs codeEqual
  have distinct := compiled_fields_distinct (env.bind.weaken 1) definitions
    (typed_object_names_distinct typing) injective entriesEqual
  refine ⟨.fix (.abs (.abs (.record "DOT" (recordFields entries).2))), entries, body,
    ?_, entriesEqual, codeEqual, ?_⟩
  · simp [value, entriesEqual]
  · exact force_field_call
      (recordFields_values entries (fields_suspended (env.bind.weaken 1) definitions entriesEqual))
      (recordFields_lookup distinct membership) hk

end CDotFCCT.TermCPS
