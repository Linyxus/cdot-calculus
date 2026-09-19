import CDotFCCT.CarrierTranslation
import CDotFCCT.TermCPS
import CDotFCCT.CTML.MixedCarrierPackages

/-!
# Runtime values in an opened carrier environment

Every source variable has one target payload type in its precise carrier. The
runtime environment stores a value at that type. This pass computes a CPS term
and its record-guarded-target typing derivation from a supported source derivation
whose term is a variable. It uses the exact variable case of `TermCPS.compile`.

The result interface existentially binds every member witness and its payload
type. Its requested view can refer to the opened source environment, as required
for path-dependent result types. Translating constructors and field/function
elimination remain separate obligations. This is not the full core-DOT compiler.
-/

set_option autoImplicit false

namespace CDotFCCT.CarrierTranslation

open CDot CTMLCore CTML.Mixed

variable [Signature]

def runtimeIndex (context : Ctx) (name : Var) : Nat := (context.map Prod.fst).idxOf name

def runtimeEnvironment (context : Ctx) : TermCPS.Env where
  free := runtimeIndex context
  bound := id
  fieldName := fun _ => ""

def Layout.runtimeType (layout : Layout) (name : Var) : WFTy layout.depth :=
  (layout.payload (.var name)).getD WFTy.top

def Layout.runtimeContext (layout : Layout) (context : Ctx) : TypingContext layout.depth :=
  ⟨(context.map Prod.fst).map layout.runtimeType⟩

omit [Signature] in
theorem lookupMapped {depth : Nat} (types : Var → WFTy depth) {names : List Var} {name : Var}
    (present : name ∈ names) :
    TypingContext.Lookup ⟨names.map types⟩ (names.idxOf name) (types name) := by
  induction names with
  | nil => cases present
  | cons first rest ih =>
      by_cases same : name = first
      · simpa [same, TypingContext.bind] using
          (TypingContext.Lookup.here (context := ⟨rest.map types⟩) (type := types first))
      · simpa only [List.map_cons, TypingContext.bind,
          List.idxOf_cons_ne rest (Ne.symm same)] using
          (TypingContext.Lookup.there (skipped := types first)
            (ih (List.mem_of_ne_of_mem same present)))

structure CompiledVariable (context : Ctx) (name : Var) (source : Typ) where
  layout : Layout
  guards : List (WFConstraint layout.depth)
  contextCode : ContextCode layout context guards
  carrier : PathResult layout guards (.var name) source
  payload : WFTy layout.depth
  found : layout.payload (.var name) = some payload
  present : name ∈ context.map Prod.fst

def Layout.valueInterface (layout : Layout) (view : WFTy layout.depth) :
    CTML.Interface layout.depth := CarrierLayout.interface layout.slots none view

def CompiledVariable.interface {context : Ctx} {name : Var} {source : Typ}
    (compiled : CompiledVariable context name source) : CTML.Interface compiled.layout.depth :=
  compiled.layout.valueInterface compiled.carrier.type

def CompiledVariable.instance {context : Ctx} {name : Var} {source : Typ}
    (compiled : CompiledVariable context name source) :
    InterfaceInstance carrierPolicy ⟨compiled.layout.depth, compiled.guards⟩
      compiled.interface compiled.payload := by
  simpa only [CompiledVariable.interface, Layout.valueInterface, Layout.component,
    compiled.found, Option.getD_some] using
    CarrierLayout.packingInstance (s := ⟨compiled.layout.depth, compiled.guards⟩)
      compiled.layout.slots none List.mem_cons_self
      (fun slot => (compiled.layout.component (.var name) slot).getD WFTy.top)
      compiled.carrier.type compiled.carrier.proof

def CompiledVariable.term {context : Ctx} {name : Var} {source : Typ}
    (_compiled : CompiledVariable context name source) : CTMLCore.Syntax.Term :=
  CTML.pack (.var (runtimeIndex context name))

theorem CompiledVariable.lookup {context : Ctx} {name : Var} {source : Typ}
    (compiled : CompiledVariable context name source) :
    (compiled.layout.runtimeContext context).Lookup
      (runtimeIndex context name) compiled.payload := by
  simpa only [Layout.runtimeType, Layout.runtimeContext, runtimeIndex,
    compiled.found, Option.getD_some] using
    lookupMapped compiled.layout.runtimeType compiled.present

theorem CompiledVariable.typing {context : Ctx} {name : Var} {source : Typ}
    (compiled : CompiledVariable context name source) (answer : WFTy compiled.layout.depth) :
    CTML.Mixed.HasType carrierPolicy ⟨compiled.layout.depth, compiled.guards⟩
      (compiled.layout.runtimeContext context) compiled.term (compiled.interface.package answer) :=
  interfacePackVariableTyping compiled.instance compiled.lookup

/-- This is the existing runtime compiler's output, not a substitute diverging term. -/
theorem CompiledVariable.runtime_eq {context : Ctx} {name : Var} {source : Typ}
    (compiled : CompiledVariable context name source)
    (derivation : Core.Typing context (.var name) source) :
    compiled.term = TermCPS.compile (runtimeEnvironment context) derivation := rfl

/-- The input has no target proof obligations: context, witnesses and bounds are generated. -/
def compileVariable {context : Ctx} {name : Var} {source : Typ}
    (derivation : Core.Typing context (.var name) source) :
    Option (CompiledVariable context name source) :=
  if present : name ∈ context.map Prod.fst then do
    let layout := Layout.ofEvents
      (contextEvents context ++ MemberUses.typing derivation [] []) []
    let ⟨guards, contextCode⟩ ← encodeContext layout context
    let carrier ← pathTyping contextCode derivation
    match found : layout.payload (.var name) with
    | none => none
    | some payload => return ⟨layout, guards, contextCode, carrier, payload, found, present⟩
  else none

/-- A source subtyping result transports packages without reopening or rebuilding the value. -/
theorem SubtypingResult.packageSubtype {layout : Layout}
    {guards : List (WFConstraint layout.depth)} {sourceSub sourceSup : Typ}
    (result : SubtypingResult layout guards sourceSub sourceSup) (answer : WFTy layout.depth) :
    InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩
      ((layout.valueInterface result.sub).package answer)
      ((layout.valueInterface result.sup).package answer) :=
  CarrierLayout.packageSubtype layout.slots none result.proof answer

theorem SubtypingResult.packageIdentityTyping {layout : Layout}
    {guards : List (WFConstraint layout.depth)} {sourceSub sourceSup : Typ}
    (result : SubtypingResult layout guards sourceSub sourceSup) (answer : WFTy layout.depth) :
    CTML.Mixed.HasType carrierPolicy ⟨layout.depth, guards⟩ TypingContext.empty
      (.abs (.var 0)) (WFTy.arrow
        ((layout.valueInterface result.sub).package answer)
        ((layout.valueInterface result.sup).package answer)) :=
  .abstraction (.subsumption (.native (.var _ _ _ .here)) (result.packageSubtype answer))

def CompiledSubtyping.closedPackageType {context : Ctx} {sourceSub sourceSup : Typ}
    (compiled : CompiledSubtyping context sourceSub sourceSup)
    (answer : WFTy compiled.layout.depth) : WFTy 0 :=
  abstractTypes compiled.layout.depth (abstractGuards compiled.guards (WFTy.arrow
    ((compiled.layout.valueInterface compiled.result.sub).package answer)
    ((compiled.layout.valueInterface compiled.result.sup).package answer)))

/-- The source-derived bounds justify a closed coercion between whole result packages. -/
theorem CompiledSubtyping.closedPackageTyping {context : Ctx} {sourceSub sourceSup : Typ}
    (compiled : CompiledSubtyping context sourceSub sourceSup)
    (answer : WFTy compiled.layout.depth) :
    CTML.Mixed.HasType carrierPolicy SubtypingContext.empty TypingContext.empty (.abs (.var 0))
      (compiled.closedPackageType answer) :=
  abstractTypes_typing
    (abstractGuards_typing compiled.guards (compiled.result.packageIdentityTyping answer))

end CDotFCCT.CarrierTranslation
