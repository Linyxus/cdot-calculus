import CDotFCCT.TermCPS
import CTMLCore.Language.Evaluation
import Mathlib.Data.List.Nodup

/-! # Native field properties of the runtime translation -/

set_option autoImplicit false

namespace CDotFCCT.TermCPS

open CTMLCore.Syntax CTMLCore.Evaluation

variable [CDot.Signature]

/-- Every source field is suspended, even if its right-hand side is a recursive path. -/
theorem field_suspended (env : Env) (rhs : CDot.DefRhs) {result : Term}
    (compiled : field env rhs = some result) : ∃ body, result = .abs body := by
  cases rhs with
  | path p =>
      cases compiled
      exact ⟨_, rfl⟩
  | val v =>
      cases equal : value (env.weaken 1) v with
      | none => simp [field, equal] at compiled
      | some result =>
          simp only [field, equal, bind, Option.bind, pure] at compiled
          cases compiled
          exact ⟨_, rfl⟩

theorem fields_suspended (env : Env) (definitions : CDot.Defs)
    {entries : List (String × Term)} (compiled : fields env definitions = some entries) :
    ∀ entry ∈ entries, Value entry.2 := by
  cases definitions with
  | nil =>
      cases compiled
      exact fun _ membership => False.elim (List.not_mem_nil membership)
  | cons rest definition =>
      cases definition with
      | typ _ _ => exact fields_suspended env rest compiled
      | trm label rhs =>
          cases earlierEqual : fields env rest with
          | none => simp [fields, earlierEqual] at compiled
          | some earlier =>
              cases resultEqual : field env rhs with
              | none => simp [fields, earlierEqual, resultEqual] at compiled
              | some result =>
                  simp only [fields, earlierEqual, resultEqual, bind, Option.bind, pure,
                    Option.some.injEq] at compiled
                  subst entries
                  intro entry membership
                  rcases List.mem_append.mp membership with before | last
                  · exact fields_suspended env rest earlierEqual entry before
                  · have equal : entry = (env.fieldName label, result) := by simpa using last
                    subst entry
                    obtain ⟨body, equal⟩ := field_suspended env rhs resultEqual
                    exact equal.symm ▸ Value.abs body

omit [CDot.Signature] in
/-- Package the dependent field predicate before rewriting a choice of name lists. -/
private def FieldsValues (pair : (names : List String) × TermFields names) : Prop :=
  match pair with
  | ⟨_, fields⟩ => TermFields.AllValues fields

omit [CDot.Signature] in
/-- Building the native field list preserves the field values; construction does
not execute a field computation. -/
theorem recordFields_values (entries : List (String × Term))
    (values : ∀ entry ∈ entries, Value entry.2) :
    TermFields.AllValues (recordFields entries).2 := by
  induction entries with
  | nil => exact .nil
  | cons entry rest ih =>
      obtain ⟨name, term⟩ := entry
      have tail := ih (fun entry member => values entry (List.mem_cons_of_mem _ member))
      simp only [recordFields]
      generalize recordFields rest = pair at tail ⊢
      rcases pair with ⟨names, fields⟩
      dsimp only at tail ⊢
      change FieldsValues (if duplicate : name ∈ names then ⟨names, fields⟩
        else ⟨name :: names, .cons name term fields duplicate⟩)
      by_cases duplicate : name ∈ names
      · rw [dite_eq_left duplicate]
        exact tail
      · rw [dite_eq_right duplicate]
        exact TermFields.AllValues.cons (fresh := duplicate) (values _ List.mem_cons_self) tail

/-- A compiled object returns an actual native record value before any field is forced. -/
theorem record_value (env : Env) (definitions : CDot.Defs)
    {entries : List (String × Term)} (compiled : fields env definitions = some entries) :
    Value (.record "DOT" (recordFields entries).2) :=
  .record _ _ (recordFields_values entries (fields_suspended env definitions compiled))

omit [CDot.Signature] in
theorem recordFields_names {entries : List (String × Term)}
    (distinct : (entries.map Prod.fst).Nodup) :
    (recordFields entries).1 = entries.map Prod.fst := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨name, term⟩ := entry
      have properties := List.nodup_cons.mp distinct
      have tail := ih properties.2
      simp only [recordFields, tail, properties.1, dite_false, List.map_cons]

omit [CDot.Signature] in
private def FieldsLookup (pair : (names : List String) × TermFields names)
    (name : String) (value : Term) : Prop :=
  match pair with
  | ⟨_, fields⟩ => TermFields.Lookup fields name value

omit [CDot.Signature] in
/-- Every distinct source entry is found with its unchanged compiled field body. -/
theorem recordFields_lookup {entries : List (String × Term)}
    (distinct : (entries.map Prod.fst).Nodup) {name : String} {value : Term}
    (membership : (name, value) ∈ entries) :
    TermFields.Lookup (recordFields entries).2 name value := by
  induction entries with
  | nil => exact False.elim (List.not_mem_nil membership)
  | cons entry rest ih =>
      obtain ⟨firstName, firstValue⟩ := entry
      have properties := List.nodup_cons.mp distinct
      have fresh : firstName ∉ (recordFields rest).1 :=
        (recordFields_names properties.2).symm ▸ properties.1
      change FieldsLookup (recordFields ((firstName, firstValue) :: rest)) name value
      rw [recordFields]
      generalize recordFields rest = pair at fresh ih ⊢
      rcases pair with ⟨names, fields⟩
      dsimp only at fresh ih ⊢
      rw [dite_eq_right fresh]
      rcases List.mem_cons.mp membership with equal | earlier
      · cases equal
        exact .here
      · exact .there (ih properties.2 earlier)

/-- Runtime field labels, in source lookup order (the most recent declaration first). -/
def definitionNames : CDot.Defs → CDot.Fields
  | .nil => []
  | .cons rest (.typ ..) => definitionNames rest
  | .cons rest (.trm label _) => label :: definitionNames rest

theorem hasnt_not_mem (definitions : CDot.Defs) (label : CDot.Signature.TrmLabel)
    (fresh : definitions.Hasnt (.trm label)) : label ∉ definitionNames definitions := by
  cases definitions with
  | nil => exact List.not_mem_nil
  | cons rest definition =>
      cases definition with
      | typ name type =>
          exact hasnt_not_mem rest label (by
            simpa [CDot.Defs.Hasnt, CDot.Defs.get, CDot.Def.label] using fresh)
      | trm name rhs =>
          by_cases equal : name = label
          · subst name
            simp [CDot.Defs.Hasnt, CDot.Defs.get, CDot.Def.label] at fresh
          · have restFresh : rest.Hasnt (.trm label) := by
              simpa only [CDot.Defs.Hasnt, CDot.Defs.get, CDot.Def.label,
                CDot.Label.trm.injEq, equal, ite_false] using fresh
            intro member
            rcases List.mem_cons.mp member with same | earlier
            · exact equal same.symm
            · exact hasnt_not_mem rest label restFresh earlier

theorem definitionNames_distinct {x : CDot.Var} {path : CDot.Fields} {context : CDot.Ctx}
    {definitions : CDot.Defs} {type : CDot.Typ}
    (typing : Core.DefinitionsTyping x path context definitions type) :
    (definitionNames definitions).Nodup :=
  match typing with
  | .one (d := definition) _ => by
      cases definition <;> simp [definitionNames]
  | .cons (d := definition) rest _ fresh => by
      have previous := definitionNames_distinct rest
      cases definition with
      | typ _ _ => exact previous
      | trm _ _ => exact List.nodup_cons.mpr ⟨hasnt_not_mem _ _ fresh, previous⟩

theorem fields_names (env : Env) (definitions : CDot.Defs)
    {entries : List (String × Term)} (compiled : fields env definitions = some entries) :
    entries.map Prod.fst = ((definitionNames definitions).reverse.map env.fieldName) := by
  cases definitions with
  | nil =>
      cases compiled
      rfl
  | cons rest definition =>
      cases definition with
      | typ _ _ => exact fields_names env rest compiled
      | trm label rhs =>
          cases earlierEqual : fields env rest with
          | none => simp [fields, earlierEqual] at compiled
          | some earlier =>
              cases resultEqual : field env rhs with
              | none => simp [fields, earlierEqual, resultEqual] at compiled
              | some result =>
                  simp only [fields, earlierEqual, resultEqual, bind, Option.bind, pure,
                    Option.some.injEq] at compiled
                  subst entries
                  simpa only [definitionNames, List.reverse_cons, List.map_append,
                    List.map_cons, List.map_nil] using
                    congrArg (· ++ [env.fieldName label]) (fields_names env rest earlierEqual)

/-- No definition is discarded when compiling a typed object with distinct label names. -/
theorem typed_recordFields_names (env : Env) {x : CDot.Var} {path : CDot.Fields}
    {context : CDot.Ctx} {definitions : CDot.Defs} {type : CDot.Typ}
    (typing : Core.DefinitionsTyping x path context definitions type)
    (injective : ∀ left ∈ definitionNames definitions, ∀ right ∈ definitionNames definitions,
      env.fieldName left = env.fieldName right → left = right)
    {entries : List (String × Term)} (compiled : fields env definitions = some entries) :
    (recordFields entries).1 = (definitionNames definitions).reverse.map env.fieldName := by
  have distinct : (entries.map Prod.fst).Nodup := by
    rw [fields_names env definitions compiled]
    exact List.Nodup.map_on
      (fun left hl right hr => injective left (List.mem_reverse.mp hl)
        right (List.mem_reverse.mp hr)) (List.nodup_reverse.mpr (definitionNames_distinct typing))
  exact (recordFields_names distinct).trans (fields_names env definitions compiled)

end CDotFCCT.TermCPS
