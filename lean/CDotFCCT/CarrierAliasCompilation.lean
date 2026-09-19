import CDotFCCT.CarrierRuntime
import CDotFCCT.CTML.CarrierFieldInvariant
import CDotFCCT.CTML.MixedFieldNames

/-!
# Source field aliases with generated shared witnesses

This constructor pass handles one field aliasing a variable in the source context.
It obtains that variable's witnesses from the existing carrier compiler, then uses
them to anchor the suspended field package. The resulting derivation types the exact
runtime CPS output. Callers supply source derivations only, not target bounds.

`compile` exposes the native object payload and its anchored field. `compileProjected`
additionally handles a let-bound constructor followed by field selection, returning
the original child's standard carrier package after checking source result agreement.
Neither pass translates arbitrary recursive object types into general carrier views,
or handles a field aliasing the object's new self binder.
-/

set_option autoImplicit false

namespace CDotFCCT.CarrierAliasCompilation

open CDot CTMLCore CTMLCore.Syntax CTML.Mixed CarrierTranslation
open CTML.Mixed.CarrierFieldInvariant

variable [Signature]

/-- Recover an actual source binding; shadowed entries cannot be selected. -/
def findBinding (name : Var) : (context : Ctx) → Option {type // Env.Binds name type context}
  | [] => none
  | (first, type) :: rest =>
      if same : name = first then
        some ⟨type, same ▸ Env.Binds.here⟩
      else
        match findBinding name rest with
        | none => none
        | some ⟨type, found⟩ => some ⟨type, .there same found⟩

def sourceObject (tag : Path) (tagLabel : Signature.TypLabel) (body : Typ)
    (field : Signature.TrmLabel) (child : Var) : Trm :=
  .val (.new tag tagLabel body (.cons .nil (.trm field (.path (.var child)))))

/-- All field names come from the same ordinary-label allocator as the full runtime pass. -/
def environment (context : Ctx) (tag : Path) (tagLabel : Signature.TypLabel) (body : Typ)
    (field : Signature.TrmLabel) (child : Var) : TermCPS.Env :=
  TermCPS.programEnv (runtimeIndex context) (sourceObject tag tagLabel body field child)

structure Result (context : Ctx) (child : Var) where
  childType : Typ
  childCompilation : CompiledVariable context child childType

def Result.components {context : Ctx} {child : Var} (compiled : Result context child) :
    Slot → WFTy compiled.childCompilation.layout.depth :=
  fun slot =>
    (compiled.childCompilation.layout.component (.var child) slot).getD WFTy.top

def Result.payload {context : Ctx} {child : Var} (compiled : Result context child)
    (field : FieldName) (answer : WFTy compiled.childCompilation.layout.depth) :
    WFTy compiled.childCompilation.layout.depth :=
  objectPayload compiled.childCompilation.layout.slots Slot.payload compiled.components field answer

def Result.computationType {context : Ctx} {child : Var} (compiled : Result context child)
    (field : FieldName) (answer : WFTy compiled.childCompilation.layout.depth) :
    WFTy compiled.childCompilation.layout.depth :=
  WFTy.arrow (WFTy.arrow (compiled.payload field answer) answer) answer

theorem Result.lookup {context : Ctx} {child : Var} (compiled : Result context child) :
    (compiled.childCompilation.layout.runtimeContext context).Lookup
      (runtimeIndex context child) (compiled.components Slot.payload) := by
  simpa only [Result.components, Layout.component, compiled.childCompilation.found,
    Option.getD_some] using compiled.childCompilation.lookup

/-- The complete field computation, including its self and continuation binders, is unchanged. -/
theorem runtime_eq {context : Ctx} {tag : Path} {tagLabel : Signature.TypLabel}
    {body result : Typ} {field : Signature.TrmLabel} {child : Var}
    (derivation : Core.Typing context (sourceObject tag tagLabel body field child) result) :
    TermCPS.compile (environment context tag tagLabel body field child) derivation =
      .abs (.app (.var 0)
        (aliasObject
          ((environment context tag tagLabel body field child).fieldName field)
          (runtimeIndex context child + 1))) := by
  rfl

/-- The source constructor is checked using witnesses computed from its source environment. -/
theorem Result.typing {context : Ctx} {child : Var} (compiled : Result context child)
    {tag : Path} {tagLabel : Signature.TypLabel} {body result : Typ}
    {field : Signature.TrmLabel}
    (derivation : Core.Typing context (sourceObject tag tagLabel body field child) result)
    (answer : WFTy compiled.childCompilation.layout.depth) :
    CTML.Mixed.HasType carrierPolicy
      ⟨compiled.childCompilation.layout.depth, compiled.childCompilation.guards⟩
      (compiled.childCompilation.layout.runtimeContext context)
      (TermCPS.compile (environment context tag tagLabel body field child) derivation)
      (compiled.computationType
        ((environment context tag tagLabel body field child).fieldName field) answer) := by
  rw [runtime_eq derivation]
  exact .abstraction (.application (.native (.var _ _ _ .here))
    (aliasObjectTyping (s := ⟨compiled.childCompilation.layout.depth,
        compiled.childCompilation.guards⟩)
      compiled.childCompilation.layout.slots Slot.payload List.mem_cons_self
      compiled.components _ answer (.there compiled.lookup)))

/-- Field use returns the same payload type chosen for the original source variable. -/
theorem Result.fieldTyping {context : Ctx} {child : Var} (compiled : Result context child)
    (field : FieldName) (answer : WFTy compiled.childCompilation.layout.depth)
    {targetContext : TypingContext compiled.childCompilation.layout.depth}
    {parent continuation : Term}
    (parentTyping : CTML.Mixed.HasType carrierPolicy
      ⟨compiled.childCompilation.layout.depth, compiled.childCompilation.guards⟩ targetContext
      parent (compiled.payload field answer))
    (continuationTyping : CTML.Mixed.HasType carrierPolicy
      ⟨compiled.childCompilation.layout.depth, compiled.childCompilation.guards⟩ targetContext
      continuation (WFTy.arrow compiled.childCompilation.payload answer)) :
    CTML.Mixed.HasType carrierPolicy
      ⟨compiled.childCompilation.layout.depth, compiled.childCompilation.guards⟩ targetContext
      (fieldCall parent field continuation) answer := by
  apply fieldCallTyping (s := ⟨compiled.childCompilation.layout.depth,
      compiled.childCompilation.guards⟩)
    compiled.childCompilation.layout.slots Slot.payload List.mem_cons_self
    compiled.components field answer parentTyping
  simpa only [Result.components, Layout.component, compiled.childCompilation.found,
    Option.getD_some] using continuationTyping

/-- A failed child/context encoding remains an explicit unsupported case. -/
def compile {context : Ctx} {tag : Path} {tagLabel : Signature.TypLabel}
    {body result : Typ} {field : Signature.TrmLabel} {child : Var}
    (_derivation : Core.Typing context (sourceObject tag tagLabel body field child) result) :
    Option (Result context child) := do
  let ⟨type, binding⟩ ← findBinding child context
  let compiled ← compileVariable (Core.Typing.var binding)
  return ⟨type, compiled⟩

/-- Construct an alias field, bind its object, and return the selected field. -/
def projectedSource (tag : Path) (tagLabel : Signature.TypLabel) (body : Typ)
    (field : Signature.TrmLabel) (child : Var) : Trm :=
  .letE (sourceObject tag tagLabel body field child)
    (.path (.select (.bound 0) [field]))

def projectedEnvironment (context : Ctx) (tag : Path) (tagLabel : Signature.TypLabel)
    (body : Typ) (field : Signature.TrmLabel) (child : Var) : TermCPS.Env :=
  TermCPS.programEnv (runtimeIndex context) (projectedSource tag tagLabel body field child)

theorem projectedRuntime_eq {context : Ctx} {tag : Path} {tagLabel : Signature.TypLabel}
    {body result : Typ} {field : Signature.TrmLabel} {child : Var}
    (derivation : Core.Typing context (projectedSource tag tagLabel body field child) result) :
    TermCPS.compile (projectedEnvironment context tag tagLabel body field child) derivation =
      .abs (.app
        (.abs (.app (.abs (fieldCall (.var 0)
          ((projectedEnvironment context tag tagLabel body field child).fieldName field)
          (.var 2))) (.var 0)))
        (aliasObject
          ((projectedEnvironment context tag tagLabel body field child).fieldName field)
          (runtimeIndex context child + 1))) := by
  rfl

/-- Projection reuses the original variable's complete carrier package, not new witnesses. -/
theorem Result.projectedTyping {context : Ctx} {child : Var} (compiled : Result context child)
    {tag : Path} {tagLabel : Signature.TypLabel} {body result : Typ}
    {field : Signature.TrmLabel}
    (derivation : Core.Typing context (projectedSource tag tagLabel body field child) result)
    (answer : WFTy compiled.childCompilation.layout.depth) :
    CTML.Mixed.HasType carrierPolicy
      ⟨compiled.childCompilation.layout.depth, compiled.childCompilation.guards⟩
      (compiled.childCompilation.layout.runtimeContext context)
      (TermCPS.compile (projectedEnvironment context tag tagLabel body field child) derivation)
      (compiled.childCompilation.interface.package answer) := by
  rw [projectedRuntime_eq derivation]
  refine .abstraction (.application (.abstraction (.application (.abstraction ?_)
    (.native (.var _ _ _ .here))))
      (aliasObjectTyping (s := ⟨compiled.childCompilation.layout.depth,
        compiled.childCompilation.guards⟩)
        compiled.childCompilation.layout.slots Slot.payload List.mem_cons_self
        compiled.components _ answer (.there compiled.lookup)))
  apply compiled.fieldTyping _ answer (.native (.var _ _ _ .here))
  exact .subsumption (.native (.var _ _ _ (.there (.there .here))))
    (compiled.childCompilation.instance.consumerSubtype answer)

/-- The exported interface translates the source program's requested result type. -/
structure ProjectedResult (context : Ctx) (child : Var) (result : Typ) where
  childCompilation : CompiledVariable context child result

def ProjectedResult.constructor {context : Ctx} {child : Var} {result : Typ}
    (compiled : ProjectedResult context child result) : Result context child :=
  ⟨result, compiled.childCompilation⟩

theorem ProjectedResult.typing {context : Ctx} {child : Var} {result : Typ}
    (compiled : ProjectedResult context child result)
    {tag : Path} {tagLabel : Signature.TypLabel} {body : Typ} {field : Signature.TrmLabel}
    (derivation : Core.Typing context (projectedSource tag tagLabel body field child) result)
    (answer : WFTy compiled.childCompilation.layout.depth) :
    CTML.Mixed.HasType carrierPolicy
      ⟨compiled.childCompilation.layout.depth, compiled.childCompilation.guards⟩
      (compiled.childCompilation.layout.runtimeContext context)
      (TermCPS.compile (projectedEnvironment context tag tagLabel body field child) derivation)
      (compiled.childCompilation.interface.package answer) :=
  compiled.constructor.projectedTyping derivation answer

/-- This pass checks source result agreement before returning its target derivation. -/
def compileProjected {context : Ctx} {tag : Path} {tagLabel : Signature.TypLabel}
    {body result : Typ} {field : Signature.TrmLabel} {child : Var}
    (_derivation : Core.Typing context (projectedSource tag tagLabel body field child) result) :
    Option (ProjectedResult context child result) := do
  let ⟨type, binding⟩ ← findBinding child context
  if same : type = result then
    let compiled ← compileVariable (Core.Typing.var (same ▸ binding))
    return ⟨compiled⟩
  else none

end CDotFCCT.CarrierAliasCompilation
