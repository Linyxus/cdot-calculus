import CDotFCCT.TermCPSRecords
import CDotFCCT.CTML.RecursiveInterfaces
import CDotFCCT.CTML.MixedInterfaces
import CDotFCCT.CTML.MixedFieldNames

/-!
# The native recursive object step of the CPS typing proof

The recursive self equation is generated from the native record's field types.
Every recursive occurrence is guarded by a record, regardless of the field type's
internal shape. The constructor lemma consumes the translated field derivations,
which are induction hypotheses for a complete compiler; it does not claim to
generate those derivations from arbitrary source definitions yet.
-/

set_option autoImplicit false

namespace CDotFCCT.TermCPS

open CTMLCore CTMLCore.Syntax

private theorem recordFold_guarded {depth : Nat} (index : Nat)
    (entries : List (String × WFTy depth)) (start : WFTy depth)
    (guarded : start.raw.GuardedAt index) :
    (entries.foldl (fun row entry => WFTy.intersection row
      (WFTy.record entry.1 entry.2)) start).raw.GuardedAt index :=
  match entries with
  | [] => guarded
  | entry :: rest => recordFold_guarded index rest
      (WFTy.intersection start (WFTy.record entry.1 entry.2)) ⟨guarded, trivial⟩

/-- The native record itself guards the self equation; no arrow test is imposed. -/
def objectDefinition {depth : Nat} (entries : List (String × WFTy (depth + 1))) :
    RecursiveType depth :=
  ⟨recordResultType "DOT" entries, recordFold_guarded 0 entries (WFTy.cls "DOT") trivial⟩

def nativeObjectThunk {names : List String} (contents : TermFields names) : Term :=
  .fix (.abs (.abs (.record "DOT" contents)))

/-- Tie the self thunk using the actual field proofs and a native row bound. -/
theorem nativeObjectThunkTyping {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {self : WFTy s.typeDepth}
    {names : List String} {contents : TermFields names}
    {types : List (String × WFTy s.typeDepth)}
    (typing : Recursive.FieldsHaveType s
      ((context.bind (WFTy.arrow WFTy.top self)).bind WFTy.top) contents types)
    (fold : Subtype s (recordResultType "DOT" types) self) :
    Recursive.HasType s context (nativeObjectThunk contents) (WFTy.arrow WFTy.top self) :=
  .fixpoint (.abstraction (.abstraction
    ((Recursive.HasType.record typing).subsumption fold)))

/-- The generated record equation discharges the constructor's row bound. -/
theorem recursiveObjectThunkTyping {s : SubtypingContext}
    {context : TypingContext (s.typeDepth + 1)}
    {names : List String} {contents : TermFields names}
    (types : List (String × WFTy (s.typeDepth + 1)))
    (typing : Recursive.FieldsHaveType ((objectDefinition types).openContext s)
      ((context.bind (WFTy.arrow WFTy.top (objectDefinition types).name)).bind WFTy.top)
      contents types) :
    Recursive.HasType ((objectDefinition types).openContext s) context
      (nativeObjectThunk contents) (WFTy.arrow WFTy.top (objectDefinition types).name) :=
  nativeObjectThunkTyping typing ((objectDefinition types).fold s)

variable {ghost : FieldName → Bool}

private theorem mixedRecordFold_guarded {depth : Nat} (index : Nat)
    (entries : List (String × WFTy depth)) (start : WFTy depth)
    (guarded : CTML.Mixed.GuardedAt ghost index start.raw)
    (ordinary : ∀ entry ∈ entries, ghost entry.1 = false) :
    CTML.Mixed.GuardedAt ghost index
      (entries.foldl (fun row entry => WFTy.intersection row
        (WFTy.record entry.1 entry.2)) start).raw :=
  match entries with
  | [] => guarded
  | entry :: rest => mixedRecordFold_guarded index rest
      (WFTy.intersection start (WFTy.record entry.1 entry.2))
      ⟨guarded, by
        change CTML.Mixed.GuardedAt ghost index (.record entry.1 entry.2.raw)
        simp only [CTML.Mixed.GuardedAt, ordinary entry List.mem_cons_self,
          Bool.false_eq_true, ↓reduceIte]⟩
      (fun found member => ordinary found (List.mem_cons_of_mem entry member))

/-- The same generated self equation is valid when its runtime field labels are ordinary. -/
def mixedObjectDefinition {depth : Nat} (entries : List (String × WFTy (depth + 1)))
    (ordinary : ∀ entry ∈ entries, ghost entry.1 = false) : CTML.Mixed.Definition ghost depth :=
  ⟨recordResultType "DOT" entries,
    mixedRecordFold_guarded 0 entries (WFTy.cls "DOT") trivial ordinary⟩

theorem mixedObjectDefinition_native {depth : Nat}
    (entries : List (String × WFTy (depth + 1)))
    (ordinary : ∀ entry ∈ entries, ghost entry.1 = false) :
    (mixedObjectDefinition entries ordinary).native = objectDefinition entries := rfl

/-- Mixed field proofs tie the exact same runtime self thunk. -/
theorem mixedNativeObjectThunkTyping {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {self : WFTy s.typeDepth}
    {names : List String} {contents : TermFields names}
    {types : List (String × WFTy s.typeDepth)}
    (typing : CTML.Mixed.FieldsHaveType ghost s
      ((context.bind (WFTy.arrow WFTy.top self)).bind WFTy.top) contents types)
    (fold : CTML.Mixed.InvertingSubtype ghost s (recordResultType "DOT" types) self) :
    CTML.Mixed.HasType ghost s context (nativeObjectThunk contents)
      (WFTy.arrow WFTy.top self) :=
  .fixpoint (.abstraction (.abstraction
    ((CTML.Mixed.HasType.record typing).subsumption fold)))

/-- Ordinary record fields discharge the fold bound, with no restriction on payload types. -/
theorem mixedRecursiveObjectThunkTyping {s : SubtypingContext}
    {context : TypingContext (s.typeDepth + 1)}
    {names : List String} {contents : TermFields names}
    (types : List (String × WFTy (s.typeDepth + 1)))
    (ordinary : ∀ entry ∈ types, ghost entry.1 = false)
    (typing : CTML.Mixed.FieldsHaveType ghost
      ((mixedObjectDefinition types ordinary).native.openContext s)
      ((context.bind (WFTy.arrow WFTy.top (objectDefinition types).name)).bind WFTy.top)
      contents types) :
    CTML.Mixed.HasType ghost ((mixedObjectDefinition types ordinary).native.openContext s)
      context (nativeObjectThunk contents)
      (WFTy.arrow WFTy.top (objectDefinition types).name) :=
  mixedNativeObjectThunkTyping typing (.native ((objectDefinition types).fold s))

private theorem mixedFields_names {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {names : List String} {contents : TermFields names}
    {types : List (String × WFTy s.typeDepth)}
    (typing : CTML.Mixed.FieldsHaveType ghost s context contents types) :
    types.map Prod.fst = names :=
  match typing with
  | .nil => rfl
  | .cons _ rest => congrArg (_ :: ·) (mixedFields_names rest)

private theorem recordFields_ordinary (entries : List (String × Term))
    (ordinary : ∀ entry ∈ entries, ghost entry.1 = false) :
    ∀ name ∈ (recordFields entries).1, ghost name = false := by
  induction entries with
  | nil => exact fun _ member => False.elim (List.not_mem_nil member)
  | cons entry rest ih =>
      have tail := ih (fun found member => ordinary found (List.mem_cons_of_mem entry member))
      simp only [recordFields]
      generalize recordFields rest = pair at tail ⊢
      rcases pair with ⟨names, contents⟩
      dsimp only at tail ⊢
      by_cases duplicate : entry.1 ∈ names
      · rw [dite_eq_left duplicate]
        exact tail
      · rw [dite_eq_right duplicate]
        intro name member
        rcases List.mem_cons.mp member with rfl | later
        · exact ordinary entry List.mem_cons_self
        · exact tail name later

variable [CDot.Signature]

/-- The field induction hypotheses recover their own ordinary labels from the compiled code. -/
theorem compiledFieldTypes_ordinary {env : Env} {definitions : CDot.Defs}
    {entries : List (String × Term)} (compiled : fields env definitions = some entries)
    (ordinary : ∀ label, ghost (env.fieldName label) = false)
    {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {types : List (String × WFTy s.typeDepth)}
    (typing : CTML.Mixed.FieldsHaveType ghost s context (recordFields entries).2 types) :
    ∀ entry ∈ types, ghost entry.1 = false := by
  have runtimeOrdinary : ∀ entry ∈ entries, ghost entry.1 = false := by
    intro entry member
    have present : entry.1 ∈ entries.map Prod.fst := List.mem_map_of_mem member
    rw [fields_names env definitions compiled] at present
    obtain ⟨source, _, equal⟩ := List.mem_map.mp present
    exact equal ▸ ordinary source
  intro entry member
  exact recordFields_ordinary entries runtimeOrdinary entry.1
    (mixedFields_names typing ▸ List.mem_map_of_mem member)

/-- The actual default program environment discharges the constructor's label condition. -/
theorem programCompiledFieldTypes_ordinary (free : CDot.Var → Nat) (term : CDot.Trm)
    {definitions : CDot.Defs} {entries : List (String × Term)}
    (compiled : fields (((programEnv free term).weaken 1).bind.weaken 1) definitions = some entries)
    {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {types : List (String × WFTy s.typeDepth)}
    (typing : CTML.Mixed.FieldsHaveType CTML.Mixed.carrierPolicy s context
      (recordFields entries).2 types) :
    ∀ entry ∈ types, CTML.Mixed.carrierPolicy entry.1 = false :=
  compiledFieldTypes_ordinary compiled (programEnv_ordinary free term) typing

/-- The default runtime allocation supplies the constructor's ordinary-label proof. -/
theorem allocatedFieldTypes_ordinary {depth : Nat} (labels : CDot.Fields)
    (types : List (CDot.Signature.TrmLabel × WFTy depth)) :
    ∀ entry ∈ types.map (fun entry => (fieldName labels entry.1, entry.2)),
      CTML.Mixed.carrierPolicy entry.1 = false := by
  intro entry member
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
  exact fieldName_ordinary labels source.1

def allocatedMixedObjectDefinition {depth : Nat} (labels : CDot.Fields)
    (types : List (CDot.Signature.TrmLabel × WFTy (depth + 1))) :
    CTML.Mixed.Definition CTML.Mixed.carrierPolicy depth :=
  mixedObjectDefinition (types.map (fun entry => (fieldName labels entry.1, entry.2)))
    (allocatedFieldTypes_ordinary labels types)

theorem computation_object {env : Env} {tag : CDot.Path}
    {label : CDot.Signature.TypLabel} {body : CDot.Typ} {definitions : CDot.Defs}
    {entries : List (String × Term)}
    (compiled : fields ((env.weaken 1).bind.weaken 1) definitions = some entries) :
    computation env (.val (.new tag label body definitions)) =
      some (.abs (.app (.var 0) (nativeObjectThunk (recordFields entries).2))) := by
  simp [computation, run, value, compiled, nativeObjectThunk]

theorem compile_object_eq {env : Env} {sourceContext : CDot.Ctx} {tag : CDot.Path}
    {label : CDot.Signature.TypLabel} {body result : CDot.Typ} {definitions : CDot.Defs}
    {entries : List (String × Term)}
    (compiled : fields ((env.weaken 1).bind.weaken 1) definitions = some entries)
    (derivation : Core.Typing sourceContext
      (.val (.new tag label body definitions)) result) :
    compile env derivation =
      .abs (.app (.var 0) (nativeObjectThunk (recordFields entries).2)) := by
  simp [compile, computation_object compiled]

/-- The object case needs field induction hypotheses and generated package evidence,
not a different runtime compiler. Both inputs remain obligations of the general proof. -/
theorem compileObjectTyping {env : Env} {sourceContext : CDot.Ctx} {tag : CDot.Path}
    {label : CDot.Signature.TypLabel} {body result : CDot.Typ} {definitions : CDot.Defs}
    {entries : List (String × Term)}
    (compiled : fields ((env.weaken 1).bind.weaken 1) definitions = some entries)
    (derivation : Core.Typing sourceContext
      (.val (.new tag label body definitions)) result)
    {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {self answer : WFTy s.typeDepth} {interface : CTML.Interface s.typeDepth}
    {types : List (String × WFTy s.typeDepth)}
    (typing : Recursive.FieldsHaveType s
      (((context.bind (interface.consumer answer)).bind
        (WFTy.arrow WFTy.top self)).bind WFTy.top) (recordFields entries).2 types)
    (fold : Subtype s (recordResultType "DOT" types) self)
    (inst : CTML.Interface.Instance s interface (WFTy.arrow WFTy.top self)) :
    Recursive.HasType s context (compile env derivation) (interface.package answer) :=
  (compile_object_eq compiled derivation).symm ▸
    Recursive.HasType.abstraction (.application
      ((Recursive.HasType.native (.var _ 0 _ .here)).subsumption
        (inst.consumerSubtype answer)) (nativeObjectThunkTyping typing fold))

/-- The object induction step now targets the calculus used by the carrier compiler. -/
theorem compileObjectMixedTyping {env : Env} {sourceContext : CDot.Ctx} {tag : CDot.Path}
    {label : CDot.Signature.TypLabel} {body result : CDot.Typ} {definitions : CDot.Defs}
    {entries : List (String × Term)}
    (compiled : fields ((env.weaken 1).bind.weaken 1) definitions = some entries)
    (derivation : Core.Typing sourceContext
      (.val (.new tag label body definitions)) result)
    {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {self answer : WFTy s.typeDepth} {interface : CTML.Interface s.typeDepth}
    {types : List (String × WFTy s.typeDepth)}
    (typing : CTML.Mixed.FieldsHaveType ghost s
      (((context.bind (interface.consumer answer)).bind
        (WFTy.arrow WFTy.top self)).bind WFTy.top) (recordFields entries).2 types)
    (fold : CTML.Mixed.InvertingSubtype ghost s (recordResultType "DOT" types) self)
    (inst : CTML.Mixed.InterfaceInstance ghost s interface (WFTy.arrow WFTy.top self)) :
    CTML.Mixed.HasType ghost s context (compile env derivation) (interface.package answer) :=
  (compile_object_eq compiled derivation).symm ▸
    CTML.Mixed.HasType.abstraction (.application
      ((CTML.Mixed.HasType.native (.var _ 0 _ .here)).subsumption
        (inst.consumerSubtype answer)) (mixedNativeObjectThunkTyping typing fold))

/-- The generated record equation supplies the only fold bound in the constructor step. -/
theorem compileRecursiveObjectMixedTyping {env : Env} {sourceContext : CDot.Ctx}
    {tag : CDot.Path} {label : CDot.Signature.TypLabel} {body result : CDot.Typ}
    {definitions : CDot.Defs} {entries : List (String × Term)}
    (compiled : fields ((env.weaken 1).bind.weaken 1) definitions = some entries)
    (derivation : Core.Typing sourceContext
      (.val (.new tag label body definitions)) result)
    {s : SubtypingContext} {context : TypingContext (s.typeDepth + 1)}
    {answer : WFTy (s.typeDepth + 1)} {interface : CTML.Interface (s.typeDepth + 1)}
    (types : List (String × WFTy (s.typeDepth + 1)))
    (ordinary : ∀ entry ∈ types, ghost entry.1 = false)
    (typing : CTML.Mixed.FieldsHaveType ghost
      ((mixedObjectDefinition types ordinary).native.openContext s)
      (((context.bind (interface.consumer answer)).bind
        (WFTy.arrow WFTy.top (objectDefinition types).name)).bind WFTy.top)
      (recordFields entries).2 types)
    (inst : CTML.Mixed.InterfaceInstance ghost
      ((mixedObjectDefinition types ordinary).native.openContext s)
      interface (WFTy.arrow WFTy.top (objectDefinition types).name)) :
    CTML.Mixed.HasType ghost ((mixedObjectDefinition types ordinary).native.openContext s)
      context (compile env derivation) (interface.package answer) :=
  compileObjectMixedTyping compiled derivation typing
    (.native ((objectDefinition types).fold s)) inst

end CDotFCCT.TermCPS
