import CDotFCCT.CarrierRuntime
import CDotFCCT.CTML.CarrierFieldInvariant
import CDotFCCT.CTML.CarrierFieldPresence
import CDotFCCT.CTML.MixedFieldNames
import CDotFCCT.CTML.MixedTermWeakening
import CDotFCCT.CTML.MixedAssumptions

/-!
# Exact CPS paths under generated runtime representation guards

Source and solved-equation guards establish path types and field presence. Each
visited edge additionally requires the input runtime representation to expose
the child's anchored package when its presence flag holds. These conditional
guards are generated separately; general source constructors must still discharge
them. No requested result bound is added as a runtime representation guard.
-/

set_option autoImplicit false

namespace CDotFCCT.CarrierPathRuntime

open CDot CTMLCore CTMLCore.Syntax CTML.Mixed CarrierTranslation

variable [Signature]

def payload (layout : Layout) (path : Path) : WFTy layout.depth :=
  (layout.payload path).getD WFTy.top

def components (layout : Layout) (path : Path) (slot : Slot) : WFTy layout.depth :=
  (layout.component path slot).getD WFTy.top

def edgesAt (root : AVar) : Fields → List (Path × Signature.TrmLabel)
  | [] => []
  | label :: rest => (.select root rest, label) :: edgesAt root rest

def edges : Path → List (Path × Signature.TrmLabel)
  | .select root fields => edgesAt root fields

theorem edges_select (path : Path) (label : Signature.TrmLabel) :
    edges (path.selectField label) = (path, label) :: edges path := by
  cases path
  rfl

def shape (layout : Layout) (fieldName : Signature.TrmLabel → FieldName)
    (answer : WFTy layout.depth) (path : Path) (label : Signature.TrmLabel) : WFTy layout.depth :=
  CarrierFieldInvariant.objectPayload layout.slots Slot.payload
    (components layout (path.selectField label)) (fieldName label) answer

def representationGuard (layout : Layout) (fieldName : Signature.TrmLabel → FieldName)
    (answer : WFTy layout.depth) (edge : Path × Signature.TrmLabel) : WFConstraint layout.depth :=
  WFConstraint.constr (payload layout edge.1)
    (CarrierFieldPresence.invariant ((layout.fieldPresence edge.1 edge.2).getD WFTy.top)
      (shape layout fieldName answer edge.1 edge.2))

def representationGuards (layout : Layout) (fieldName : Signature.TrmLabel → FieldName)
    (answer : WFTy layout.depth) (path : Path) : List (WFConstraint layout.depth) :=
  (edges path).map (representationGuard layout fieldName answer)

def RootLookup (layout : Layout) (env : TermCPS.Env) (context : TypingContext layout.depth) :
    Path → Prop
  | .select (.free name) _ => context.Lookup (env.free name) (payload layout (.var name))
  | .select (.bound _) _ => False

def RuntimeEvidence (layout : Layout) (guards : List (WFConstraint layout.depth))
    (fieldName : Signature.TrmLabel → FieldName) (answer : WFTy layout.depth)
    (path : Path) : Prop :=
  ∀ edge ∈ edges path, InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩
    (representationGuard layout fieldName answer edge).sub
    (representationGuard layout fieldName answer edge).sup

theorem path_select (env : TermCPS.Env) (path : Path) (label : Signature.TrmLabel)
    (continuation : Term) :
    TermCPS.path env (path.selectField label) continuation =
      TermCPS.path env path (.abs
        (CarrierFieldInvariant.fieldCall (.var 0)
          (env.fieldName label) (continuation.lift 1))) := by
  cases path
  rfl

/-- Every projection consumes the fixed child payload from its existing carrier anchor. -/
theorem pathTyping {layout : Layout} {guards : List (WFConstraint layout.depth)}
    {path : Path} (present : PathPresence layout guards path)
    {env : TermCPS.Env} {context : TypingContext layout.depth}
    {answer : WFTy layout.depth} {continuation : Term}
    (root : RootLookup layout env context path)
    (runtime : RuntimeEvidence layout guards env.fieldName answer path)
    (consumer : HasType carrierPolicy ⟨layout.depth, guards⟩ context continuation
      (WFTy.arrow (payload layout path) answer)) :
    HasType carrierPolicy ⟨layout.depth, guards⟩ context
      (TermCPS.path env path continuation) answer := by
  induction present generalizing env context continuation with
  | root name => exact .application consumer (.native (.var _ _ _ root))
  | @field parent label parentExists edge ih =>
      rw [path_select]
      have parentRoot : RootLookup layout env context parent := by
        cases parent with
        | select base fields => cases base <;> exact root
      have parentRuntime : RuntimeEvidence layout guards env.fieldName answer parent := by
        intro found member
        exact runtime found ((edges_select parent label) ▸ List.mem_cons_of_mem _ member)
      apply ih parentRoot parentRuntime
      apply CTML.Mixed.HasType.abstraction
      apply CarrierFieldInvariant.fieldCallTyping layout.slots Slot.payload List.mem_cons_self
        (s := ⟨layout.depth, guards⟩)
        (components layout (parent.selectField label)) (env.fieldName label) answer
      · apply CTML.Mixed.HasType.subsumption (.native (.var _ _ _ .here))
        apply CarrierFieldPresence.extract
          (runtime (parent, label) ((edges_select parent label) ▸ List.mem_cons_self))
        rw [edge.found]
        exact edge.proof
      · exact consumer.weakenFront (payload layout parent)

theorem addBounds {layout : Layout} {guards : List (WFConstraint layout.depth)}
    (extra : List (WFConstraint layout.depth)) {sub sup : WFTy layout.depth}
    (included : InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩ sub sup) :
    InvertingSubtype carrierPolicy ⟨layout.depth, extra ++ guards⟩ sub sup :=
  included.mapAssumptions (fun guard member =>
    @Subtype.hyp ⟨layout.depth, extra ++ guards⟩ guard (List.mem_append_right extra member))

def addPresence {layout : Layout} {guards : List (WFConstraint layout.depth)}
    (extra : List (WFConstraint layout.depth)) {path : Path}
    (present : PathPresence layout guards path) : PathPresence layout (extra ++ guards) path :=
  match present with
  | .root name => .root name
  | .field parent edge => .field (addPresence extra parent)
      ⟨edge.type, edge.found, addBounds extra edge.proof⟩

def addResult {layout : Layout} {guards : List (WFConstraint layout.depth)}
    (extra : List (WFConstraint layout.depth)) {path : Path} {source : Typ}
    (result : PathResult layout guards path source) :
    PathResult layout (extra ++ guards) path source :=
  ⟨result.type, result.code, addBounds extra result.proof, addPresence extra result.present⟩

/-- Runtime requirements are looked up only in the separately generated representation guards. -/
theorem representationEvidence (layout : Layout) (base : List (WFConstraint layout.depth))
    (fieldName : Signature.TrmLabel → FieldName) (answer : WFTy layout.depth) (path : Path) :
    RuntimeEvidence layout (representationGuards layout fieldName answer path ++ base)
      fieldName answer path :=
  fun edge member => .native
    (@Subtype.hyp ⟨layout.depth, representationGuards layout fieldName answer path ++ base⟩
      (representationGuard layout fieldName answer edge)
      (List.mem_append_left base (List.mem_map.mpr ⟨edge, member, rfl⟩)))

theorem RootLookup.weaken {layout : Layout} {env : TermCPS.Env}
    {context : TypingContext layout.depth} {path : Path}
    (root : RootLookup layout env context path) (extra : WFTy layout.depth) :
    RootLookup layout (env.weaken 1) (context.bind extra) path := by
  cases path with
  | select base fields =>
      cases base with
      | bound index => exact root.elim
      | free name => exact .there root

/-- The original continuation is instantiated at the existing path witness vector. -/
theorem computationTyping {layout : Layout} {guards : List (WFConstraint layout.depth)}
    {path : Path} {source : Typ} (result : PathResult layout guards path source)
    {env : TermCPS.Env} {context : TypingContext layout.depth} (answer : WFTy layout.depth)
    (root : RootLookup layout env context path)
    (runtime : RuntimeEvidence layout guards env.fieldName answer path) :
    HasType carrierPolicy ⟨layout.depth, guards⟩ context
      (.abs (TermCPS.path (env.weaken 1) path (.var 0)))
      ((layout.valueInterface result.type).package answer) := by
  have packing : InterfaceInstance carrierPolicy ⟨layout.depth, guards⟩
      (layout.valueInterface result.type) (payload layout path) :=
    CarrierLayout.packingInstance (s := ⟨layout.depth, guards⟩)
      layout.slots Slot.payload List.mem_cons_self (components layout path) result.type result.proof
  apply CTML.Mixed.HasType.abstraction
  apply pathTyping result.present (root.weaken _) runtime
  exact .subsumption (.native (.var _ 0 _ .here)) (packing.consumerSubtype answer)

theorem compile_path_eq (env : TermCPS.Env) {context : Ctx} {path : Path} {source : Typ}
    (derivation : Core.Typing context (.path path) source) :
    TermCPS.compile env derivation = .abs (TermCPS.path (env.weaken 1) path (.var 0)) := rfl

def environment (context : Ctx) (path : Path) : TermCPS.Env :=
  TermCPS.programEnv (runtimeIndex context) (.path path)

/-- The runtime requirements are computed after the source derivation and its graph equations. -/
structure CompiledPath (context : Ctx) (path : Path) (source : Typ) where
  allocation : Allocation
  sourceGuards : List (WFConstraint allocation.layout.depth)
  contextCode : ContextCode allocation.layout context sourceGuards
  carrier : PathResult allocation.layout (allocation.equations ++ sourceGuards) path source
  root : RootLookup allocation.layout (environment context path)
    (allocation.layout.runtimeContext context) path
  complete : allocation.layout.completeAt path = true

def CompiledPath.layout {context : Ctx} {path : Path} {source : Typ}
    (compiled : CompiledPath context path source) : Layout := compiled.allocation.layout

def CompiledPath.logicalGuards {context : Ctx} {path : Path} {source : Typ}
    (compiled : CompiledPath context path source) : List (WFConstraint compiled.layout.depth) :=
  compiled.allocation.equations ++ compiled.sourceGuards

def CompiledPath.runtimeGuards {context : Ctx} {path : Path} {source : Typ}
    (compiled : CompiledPath context path source) (answer : WFTy compiled.layout.depth) :
    List (WFConstraint compiled.layout.depth) :=
  representationGuards compiled.layout (environment context path).fieldName answer path

def CompiledPath.guards {context : Ctx} {path : Path} {source : Typ}
    (compiled : CompiledPath context path source) (answer : WFTy compiled.layout.depth) :
    List (WFConstraint compiled.layout.depth) :=
  compiled.runtimeGuards answer ++ compiled.logicalGuards

def CompiledPath.interface {context : Ctx} {path : Path} {source : Typ}
    (compiled : CompiledPath context path source) : CTML.Interface compiled.layout.depth :=
  compiled.layout.valueInterface compiled.carrier.type

def CompiledPath.term {context : Ctx} {path : Path} {source : Typ}
    (_compiled : CompiledPath context path source) : Term :=
  .abs (TermCPS.path ((environment context path).weaken 1) path (.var 0))

/-- The only additional assumptions describe the input values' runtime representation. -/
theorem CompiledPath.typing {context : Ctx} {path : Path} {source : Typ}
    (compiled : CompiledPath context path source) (answer : WFTy compiled.layout.depth) :
    HasType carrierPolicy ⟨compiled.layout.depth, compiled.guards answer⟩
      (compiled.layout.runtimeContext context) compiled.term (compiled.interface.package answer) :=
  computationTyping (addResult (compiled.runtimeGuards answer) compiled.carrier)
    answer compiled.root
    (representationEvidence compiled.layout compiled.logicalGuards
      (environment context path).fieldName answer path)

theorem CompiledPath.runtime_eq {context : Ctx} {path : Path} {source : Typ}
    (compiled : CompiledPath context path source)
    (derivation : Core.Typing context (.path path) source) :
    compiled.term = TermCPS.compile (environment context path) derivation := rfl

theorem CompiledPath.ordinaryFields {context : Ctx} {path : Path} {source : Typ}
    (_compiled : CompiledPath context path source) (label : Signature.TrmLabel) :
    carrierPolicy ((environment context path).fieldName label) = false :=
  TermCPS.programEnv_ordinary _ _ _

/-- This partial entry point accepts the actual source derivation and no target proof inputs. -/
def compilePath {context : Ctx} {path : Path} {source : Typ}
    (derivation : Core.Typing context (.path path) source) :
    Option (CompiledPath context path source) :=
  match path, derivation with
  | .select (.bound _) _, _ => none
  | .select (.free name) fields, derivation =>
      if member : name ∈ context.map Prod.fst then do
        let allocated : Allocation :=
          ⟨contextEvents context ++ MemberUses.typing derivation [] [], []⟩
        if complete : allocated.layout.completeAt (.select (.free name) fields) = true then do
          let ⟨guards, contextCode⟩ ← encodeContext allocated.layout context
          let carrier ← CarrierTranslation.pathTyping contextCode allocated.equations
            (allocated.children guards) derivation
          return ⟨allocated, guards, contextCode, carrier,
            lookupMapped allocated.layout.runtimeType member, complete⟩
        else none
      else none

end CDotFCCT.CarrierPathRuntime

namespace CDotFCCT.CarrierPathRuntime.Example

open CDot CTMLCore CTML.Mixed

local instance : Signature where
  TypLabel := String
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

def member : Typ := .rcd (.typ "A" .bot .top)
def context : Ctx := [(0, .rcd (.trm "a" (.rcd (.trm "b" member))))]
def path : Path := (.var 0 : Path).selectFields ["b", "a"]

def source : Core.Typing context (.path path) member :=
  .newElim (.newElim (.var .here))

/-- All witnesses, equation guards and runtime requirements are computed from this derivation. -/
def compiled : CompiledPath context path member := (compilePath source).get (by decide +kernel)

theorem oneSourceGuard : compiled.sourceGuards.length = 1 := compiled.contextCode.length

theorem twoRuntimeGuards (answer : WFTy compiled.layout.depth) :
    (compiled.runtimeGuards answer).length = 2 := rfl

/-- The actual two-projection CPS term receives its requested member-view package. -/
theorem typing (answer : WFTy compiled.layout.depth) :
    HasType carrierPolicy ⟨compiled.layout.depth, compiled.guards answer⟩
      (compiled.layout.runtimeContext context)
      (TermCPS.compile (environment context path) source) (compiled.interface.package answer) :=
  compiled.runtime_eq source ▸ compiled.typing answer

end CDotFCCT.CarrierPathRuntime.Example
