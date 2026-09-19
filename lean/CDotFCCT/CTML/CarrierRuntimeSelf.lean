import CDotFCCT.CTML.CarrierRuntimeScopes
import CDotFCCT.CTML.SelfFieldAnchor

/-!
# A whole-child carrier coupled to its self-aliasing runtime row

The carrier stores its own name in the child slot and an object thunk in the
payload slot. The thunk returns the ordinary row whose field package is anchored
to that same carrier. Both equations are generated and solved together.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierRuntimeSelf

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation
open CarrierLayout CarrierFieldInvariant

universe u
variable {Label : Type u} [DecidableEq Label]

/-- Before binding the carrier name, the sole fresh runtime name denotes its record row. -/
def parameters {depth : Nat} (payload : Label) (members : Label → WFTy depth) :
    Label → WFTy (depth + 1) := SelfFieldAnchor.witnesses payload members

/-- The child slot denotes the entire carrier, not an independently reopened member vector. -/
def witnesses {depth : Nat} (payload child : Label) (members : Label → WFTy depth) :
    Label → WFTy (depth + 2) :=
  fun label => if label = child then WFTy.var 0 (by omega)
    else (parameters payload members label).weakenBy 1

def carrierBody {depth : Nat} (support : List Label) (payload child : Label)
    (members : Label → WFTy depth) : CarrierEquation.Expr carrierPolicy (depth + 1) 1 :=
  .wholeChild support (carrierPolicy_names support) child ⟨0, by omega⟩
    (parameters payload members)

/-- The row guards all occurrences through the package's universals and constraints. -/
def system {depth : Nat} (support : List Label) (payload child : Label)
    (members : Label → WFTy depth) (field : FieldName) (ordinary : carrierPolicy field = false)
    (answer : WFTy depth) : CarrierRuntime.System carrierPolicy depth 1 1 where
  carriers := ⟨fun _ => carrierBody support payload child members,
    fun _ => CarrierEquation.Expr.wholeChild_guarded _ _ _ _ _⟩
  body := fun _ => WFTy.record field
    ((interface support payload (WFTy.var 0 (by omega))).package (answer.weakenBy 2))
  guarded := fun _ _ => by
    simp only [WFTy.record, GuardedAt, ordinary, Bool.false_eq_true, ↓reduceIte]

def carrierName {depth : Nat} : WFTy (depth + 2) := WFTy.var 0 (by omega)

def rowName {depth : Nat} : WFTy (depth + 2) := WFTy.var 1 (by omega)

def objectType {depth : Nat} : WFTy (depth + 2) :=
  SelfFieldAnchor.objectType rowName

theorem witnesses_child {depth : Nat} (payload child : Label)
    (members : Label → WFTy depth) : witnesses payload child members child = carrierName := by
  simp only [witnesses, ite_true, carrierName]

theorem witnesses_payload {depth : Nat} (payload child : Label) (different : payload ≠ child)
    (members : Label → WFTy depth) : witnesses payload child members payload = objectType := by
  simp only [witnesses, ite_eq_right different, parameters, SelfFieldAnchor.witnesses_payload]
  rfl

theorem carrier_body {depth : Nat} (support : List Label) (payload child : Label)
    (members : Label → WFTy depth) (field : FieldName) (ordinary : carrierPolicy field = false)
    (answer : WFTy depth) :
    (system support payload child members field ordinary answer).bodyAt
        ⟨0, by change 0 < 2; decide⟩ =
      precise support (witnesses payload child members) := by
  exact WFTy.eq_of_raw_eq (congrArg WFTy.raw
    (CarrierEquation.Expr.compile_wholeChild support (carrierPolicy_names support)
      child ⟨0, by omega⟩ (parameters payload members)))

theorem row_body {depth : Nat} (support : List Label) (payload child : Label)
    (members : Label → WFTy depth) (field : FieldName) (ordinary : carrierPolicy field = false)
    (answer : WFTy depth) :
    (system support payload child members field ordinary answer).bodyAt
        ⟨1, by change 1 < 2; decide⟩ =
      WFTy.record field ((interface support payload carrierName).package (answer.weakenBy 2)) := rfl

/-- The semantic carrier equation has the same precise layout used by package construction. -/
theorem carrier_equation {depth : Nat} (support : List Label) (payload child : Label)
    (members : Label → WFTy depth) (field : FieldName) (ordinary : carrierPolicy field = false)
    (answer : WFTy depth) (env : Indexed.Environment) :
    let extended := (system support payload child members field ordinary answer).environment env
    interpret carrierPolicy extended (carrierName (depth := depth)).raw =
      interpret carrierPolicy extended (precise support (witnesses payload child members)).raw := by
  simpa only [carrier_body, CarrierRuntime.System.name, carrierName, WFTy.var] using
    (system support payload child members field ordinary answer).equation env
      ⟨0, by change 0 < 2; decide⟩

theorem row_equation {depth : Nat} (support : List Label) (payload child : Label)
    (members : Label → WFTy depth) (field : FieldName) (ordinary : carrierPolicy field = false)
    (answer : WFTy depth) (env : Indexed.Environment) :
    let extended := (system support payload child members field ordinary answer).environment env
    interpret carrierPolicy extended (rowName (depth := depth)).raw =
      interpret carrierPolicy extended
        (WFTy.record field ((interface support payload carrierName).package
          (answer.weakenBy 2))).raw := by
  simpa only [row_body, CarrierRuntime.System.name, rowName, WFTy.var] using
    (system support payload child members field ordinary answer).equation env
      ⟨1, by change 1 < 2; decide⟩

set_option backward.isDefEq.respectTransparency false in
theorem carrierFold {s : SubtypingContext} (support : List Label) (payload child : Label)
    (members : Label → WFTy s.typeDepth) (field : FieldName)
    (ordinary : carrierPolicy field = false) (answer : WFTy s.typeDepth) :
    Subtype ((system support payload child members field ordinary answer).openContext s)
      (precise support (witnesses payload child members)) carrierName := by
  simpa only [carrier_body, CarrierRuntime.System.name, carrierName, WFTy.var] using
    (system support payload child members field ordinary answer).fold s
      ⟨0, by change 0 < 2; decide⟩

set_option backward.isDefEq.respectTransparency false in
theorem rowFold {s : SubtypingContext} (support : List Label) (payload child : Label)
    (members : Label → WFTy s.typeDepth) (field : FieldName)
    (ordinary : carrierPolicy field = false) (answer : WFTy s.typeDepth) :
    Subtype ((system support payload child members field ordinary answer).openContext s)
      (WFTy.record field ((interface support payload carrierName).package (answer.weakenBy 2)))
      rowName := by
  simpa only [row_body, CarrierRuntime.System.name, rowName, WFTy.var] using
    (system support payload child members field ordinary answer).fold s
      ⟨1, by change 1 < 2; decide⟩

set_option backward.isDefEq.respectTransparency false in
/-- The exact self object packs generated witnesses using the solved carrier fold equation. -/
theorem objectTyping (support : List Label) (payload child : Label)
    (present : payload ∈ support) (different : payload ≠ child) {s : SubtypingContext}
    (context : TypingContext (s.typeDepth + 2)) (members : Label → WFTy s.typeDepth)
    (field : FieldName) (ordinary : carrierPolicy field = false) (answer : WFTy s.typeDepth) :
    HasType carrierPolicy
      ((system support payload child members field ordinary answer).openContext s)
      context (SelfFieldAnchor.object field) objectType := by
  refine .fixpoint (.abstraction (.abstraction (.subsumption
    (.record (.cons ?_ .nil)) (.native (.trans .interRight
      (rowFold support payload child members field ordinary answer))))))
  apply interfacePackVariableTyping
    (packingInstance
      (s := (system support payload child members field ordinary answer).openContext s)
      support payload present (witnesses payload child members) carrierName
      (.native (carrierFold support payload child members field ordinary answer)))
  rw [witnesses_payload payload child different]
  exact .there .here

set_option backward.isDefEq.respectTransparency false in
theorem carrierUnfold {s : SubtypingContext} (support : List Label) (payload child : Label)
    (members : Label → WFTy s.typeDepth) (field : FieldName)
    (ordinary : carrierPolicy field = false) (answer : WFTy s.typeDepth) :
    Subtype ((system support payload child members field ordinary answer).openContext s)
      carrierName (precise support (witnesses payload child members)) := by
  simpa only [carrier_body, CarrierRuntime.System.name, carrierName, WFTy.var] using
    (system support payload child members field ordinary answer).unfold s
      ⟨0, by change 0 < 2; decide⟩

set_option backward.isDefEq.respectTransparency false in
theorem rowUnfold {s : SubtypingContext} (support : List Label) (payload child : Label)
    (members : Label → WFTy s.typeDepth) (field : FieldName)
    (ordinary : carrierPolicy field = false) (answer : WFTy s.typeDepth) :
    Subtype ((system support payload child members field ordinary answer).openContext s) rowName
      (WFTy.record field
        ((interface support payload carrierName).package (answer.weakenBy 2))) := by
  simpa only [row_body, CarrierRuntime.System.name, rowName, WFTy.var] using
    (system support payload child members field ordinary answer).unfold s
      ⟨1, by change 1 < 2; decide⟩

set_option backward.isDefEq.respectTransparency false in
/-- A field selected from any value of the solved object type returns the same fixed payload. -/
theorem fieldCallTyping (support : List Label) (payload child : Label)
    (present : payload ∈ support) (different : payload ≠ child) {s : SubtypingContext}
    {context : TypingContext (s.typeDepth + 2)} (members : Label → WFTy s.typeDepth)
    (field : FieldName) (ordinary : carrierPolicy field = false) (answer : WFTy s.typeDepth)
    {parent continuation : Term}
    (parentTyping : HasType carrierPolicy
      ((system support payload child members field ordinary answer).openContext s)
      context parent objectType)
    (continuationTyping : HasType carrierPolicy
      ((system support payload child members field ordinary answer).openContext s)
      context continuation (WFTy.arrow objectType (answer.weakenBy 2))) :
    HasType carrierPolicy
      ((system support payload child members field ordinary answer).openContext s)
      context (fieldCall parent field continuation) (answer.weakenBy 2) := by
  refine .application ((HasType.projection
    ((HasType.application parentTyping (.native (.record .nil))).subsumption
      (.native (rowUnfold support payload child members field ordinary answer)))).subsumption
        (.trans (packageSubtype support payload
          (.native (carrierUnfold support payload child members field ordinary answer))
          (answer.weakenBy 2))
          (anchoredPackageSubtype support payload present
            (s := (system support payload child members field ordinary answer).openContext s)
            (witnesses payload child members) (answer.weakenBy 2)))) ?_
  simpa only [witnesses_payload payload child different] using continuationTyping

/-- Both recursive names and all generated equations are hidden in one continuation package. -/
def exportedInterface {depth : Nat} (support : List Label) (payload child : Label)
    (members : Label → WFTy depth) (field : FieldName) (ordinary : carrierPolicy field = false)
    (answer : WFTy depth) : Interface depth :=
  Interface.closeGuards 2
    (system support payload child members field ordinary answer).equations objectType

set_option backward.isDefEq.respectTransparency false in
theorem consumerSubtype {s : SubtypingContext} (support : List Label) (payload child : Label)
    (members : Label → WFTy s.typeDepth) (field : FieldName)
    (ordinary : carrierPolicy field = false) (answer : WFTy s.typeDepth) :
    Subtype ((system support payload child members field ordinary answer).openContext s)
      ((exportedInterface support payload child members field ordinary answer).consumer answer
        |>.weakenBy 2)
      (WFTy.arrow objectType (answer.weakenBy 2)) := by
  have opened := (Interface.bindBlock_open s 2
    (Interface.guards (system support payload child members field ordinary answer).equations
      (.payload objectType)) answer).mapAssumptions
        (target :=
          ((system support payload child members field ordinary answer).openContext s).assumptions)
        (fun guard member => @Subtype.hyp
          ((system support payload child members field ordinary answer).openContext s) guard
          (List.mem_append_right _ member))
  exact opened.trans (Interface.guards_open _ _ _ (fun guard member =>
    @Subtype.hyp ((system support payload child members field ordinary answer).openContext s)
      guard (List.mem_append_left _ member)))

set_option backward.isDefEq.respectTransparency false in
/-- A present child slot contains the parent carrier itself, in both variance positions. -/
theorem wholeChildView {s : SubtypingContext} (support : List Label) (payload child : Label)
    (present : child ∈ support) (members : Label → WFTy s.typeDepth) (field : FieldName)
    (ordinary : carrierPolicy field = false) (answer : WFTy s.typeDepth) :
    Subtype ((system support payload child members field ordinary answer).openContext s)
      carrierName ((slot support child present).precise carrierName
        (components support support (witnesses payload child members))) := by
  have equal := precise_eq_slot present (witnesses payload child members)
  rw [witnesses_child] at equal
  exact equal ▸ carrierUnfold support payload child members field ordinary answer

set_option backward.isDefEq.respectTransparency false in
/-- The exported package obtains both equations from the solver, with no caller-supplied bound. -/
theorem packTyping (support : List Label) (payload child : Label)
    (present : payload ∈ support) (different : payload ≠ child) {s : SubtypingContext}
    (context : TypingContext s.typeDepth) (members : Label → WFTy s.typeDepth)
    (field : FieldName) (ordinary : carrierPolicy field = false) (answer : WFTy s.typeDepth) :
    HasType carrierPolicy s context (pack (SelfFieldAnchor.object field))
      ((exportedInterface support payload child members field ordinary answer).package answer) := by
  refine .recursiveCarrierRuntime (system support payload child members field ordinary answer) ?_
  refine .abstraction (.application
    ((HasType.native (.var _ 0 _ .here)).subsumption
      (.native (consumerSubtype support payload child members field ordinary answer))) ?_)
  exact objectTyping support payload child present different _ members field ordinary answer

/-- The checked object package is literally the output of the runtime compiler. -/
theorem compiledSelfTyping [CDot.Signature] (env : TermCPS.Env)
    (tag : CDot.Path) (tagLabel : CDot.Signature.TypLabel) (body : CDot.Typ)
    (sourceField : CDot.Signature.TrmLabel) (support : List Label) (payload child : Label)
    (present : payload ∈ support) (different : payload ≠ child) {s : SubtypingContext}
    (context : TypingContext s.typeDepth) (members : Label → WFTy s.typeDepth)
    (ordinary : carrierPolicy (env.fieldName sourceField) = false) (answer : WFTy s.typeDepth) :
    ∃ target,
      TermCPS.computation env (.val (.new tag tagLabel body
        (.cons .nil (.trm sourceField (.path (.select (.bound 0) [])))))) = some target ∧
      HasType carrierPolicy s context target
        ((exportedInterface support payload child members (env.fieldName sourceField)
          ordinary answer).package answer) :=
  ⟨pack (SelfFieldAnchor.object (env.fieldName sourceField)), rfl,
    packTyping support payload child present different context members _ ordinary answer⟩

/-- The closed regression includes distinct payload and self-child slots in the support. -/
theorem programTyping (field : FieldName) (ordinary : carrierPolicy field = false) :
    HasType carrierPolicy SubtypingContext.empty TypingContext.empty
      (SelfFieldAnchor.program field) (WFTy.cls "$Unit") := by
  refine .recursiveCarrierRuntime
    (system [false, true] false true (fun _ => WFTy.top) field ordinary (WFTy.cls "$Unit")) ?_
  exact fieldCallTyping [false, true] false true (by simp) (by decide)
    (s := SubtypingContext.empty) (fun _ => WFTy.top) field ordinary (WFTy.cls "$Unit")
    (objectTyping [false, true] false true (by simp) (by decide)
      (s := SubtypingContext.empty) TypingContext.empty (fun _ => WFTy.top)
      field ordinary (WFTy.cls "$Unit"))
    (.abstraction (.native (.record .nil)))

/-- Solving the additional ghost cycle changes no runtime execution. -/
theorem programSteps (field : FieldName) :
    Steps (SelfFieldAnchor.program field) SelfFieldAnchor.unit := SelfFieldAnchor.programSteps field

theorem programSafe (field : FieldName) (ordinary : carrierPolicy field = false)
    {reached : Term} (steps : Steps (SelfFieldAnchor.program field) reached) :
    Value reached ∨ ∃ next, Step reached next := (programTyping field ordinary).safe steps

end CDotFCCT.CTML.Mixed.CarrierRuntimeSelf
