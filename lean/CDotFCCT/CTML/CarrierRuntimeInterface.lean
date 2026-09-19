import CDotFCCT.CTML.CarrierFieldPresence
import CDotFCCT.CTML.MixedInterfaceWeakening

/-!
# One existential interface for a finite graph of shared carriers

All demanded nodes share one witness telescope. The outer scope retains every
node's runtime invariant while a field package reopens a precise child anchor.
This avoids recursively expanding an interface parameterized by an arbitrary
carrier. Source-driven allocation and closure of the finite graph are separate.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierRuntimeInterface

open CTMLCore CTMLCore.Syntax
open CarrierLayout

universe u v
variable {Node : Type u} {Label : Type v} [DecidableEq Node] [DecidableEq Label]
variable {ghost : FieldName → Bool}

/-- An edge names the parent's two field components and its existing child node. -/
structure Field (Node : Type u) (Label : Type v) where
  parent : Node
  child : Node
  presenceLabel : Label
  childLabel : Label
  runtimeField : FieldName

/-- A finite demanded graph, with the same carrier support at every node. -/
structure Graph (Node : Type u) (Label : Type v) where
  support : List Label
  payload : Label
  payloadPresent : payload ∈ support
  root : Node
  fields : List (Field Node Label)

def Graph.nodes (graph : Graph Node Label) : List Node :=
  graph.root :: graph.fields.flatMap (fun field => [field.parent, field.child])

/-- Include the complete row and every component referenced by the generated guards. -/
def Graph.keys (graph : Graph Node Label) : List (Node × Label) :=
  (graph.root, graph.payload) ::
    (graph.nodes.flatMap (fun node => graph.support.map (node, ·)) ++
      graph.fields.flatMap (fun field =>
        [(field.parent, graph.payload), (field.parent, field.presenceLabel),
          (field.parent, field.childLabel)]))

def Graph.complete {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) : Node × Label → WFTy depth :=
  fun key => if key ∈ graph.keys then types key else WFTy.top

theorem Graph.complete_at {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) {key : Node × Label} (present : key ∈ graph.keys) :
    graph.complete types key = types key := ite_eq_left present

def Graph.carrier {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) (node : Node) : WFTy depth :=
  precise graph.support (fun label => types (node, label))

def Graph.fieldShape {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) (answer : WFTy depth)
    (field : Field Node Label) : WFTy depth :=
  CarrierFieldPresence.runtimeShape graph.support graph.payload
    (graph.carrier types field.child) field.runtimeField answer

/-- Child identity and runtime shape are exported together, for every demanded edge. -/
def Graph.fieldGuards {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) (answer : WFTy depth)
    (field : Field Node Label) : List (WFConstraint depth) :=
  [WFConstraint.constr (types (field.parent, field.childLabel))
      (graph.carrier types field.child),
    WFConstraint.constr (graph.carrier types field.child)
      (types (field.parent, field.childLabel)),
    WFConstraint.constr (types (field.parent, graph.payload))
      (CarrierFieldPresence.invariant (types (field.parent, field.presenceLabel))
        (graph.fieldShape types answer field))]

def Graph.guards {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) (view answer : WFTy depth) :
    List (WFConstraint depth) :=
  WFConstraint.constr (graph.carrier types graph.root) view ::
    graph.fields.flatMap (graph.fieldGuards types answer)

def withGuards {depth : Nat} (guards : List (WFConstraint depth))
    (rest : Interface depth) : Interface depth :=
  guards.foldr Interface.guard rest

def Graph.body {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) (view answer : WFTy depth) : Interface depth :=
  withGuards (graph.guards types view answer) (.payload (types (graph.root, graph.payload)))

def Graph.telescope (graph : Graph Node Label) :
    (remaining : List (Node × Label)) → {depth : Nat} →
      (Node × Label → WFTy depth) → WFTy depth → WFTy depth → Interface depth
  | [], _, types, view, answer => graph.body types view answer
  | key :: rest, _, types, view, answer =>
      .bind (graph.telescope rest (bindComponent types key) view.weaken answer.weaken)

def Graph.interface {depth : Nat} (graph : Graph Node Label) (view answer : WFTy depth) :
    Interface depth := graph.telescope graph.keys (fun _ => WFTy.top) view answer

private theorem carrierInterface_substAt {depth : Nat} (support : List Label) (payload : Label)
    (view : WFTy (depth + 1)) (index : Nat) (valid : index ≤ depth)
    (replacement : WFTy depth) :
    (CarrierLayout.interface support payload view).substAt index valid replacement =
      CarrierLayout.interface support payload (view.substAt index valid replacement) := by
  unfold Transparent.CarrierLayout.interface
  rw [telescope_substAt]
  rfl

private theorem runtimeShape_substAt {depth : Nat} (support : List Label) (payload : Label)
    (child : WFTy (depth + 1)) (field : FieldName) (answer : WFTy (depth + 1))
    (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (CarrierFieldPresence.runtimeShape support payload child field answer).substAt
        index valid replacement =
      CarrierFieldPresence.runtimeShape support payload (child.substAt index valid replacement)
        field (answer.substAt index valid replacement) := by
  simp only [CarrierFieldPresence.runtimeShape, Interface.package, WFTy.substAt_arrow,
    WFTy.substAt_record, Interface.consumer_substAt, carrierInterface_substAt]
  rfl

omit [DecidableEq Node] in
private theorem Graph.carrier_substAt {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy (depth + 1)) (node : Node) (index : Nat)
    (valid : index ≤ depth) (replacement : WFTy depth) :
    (graph.carrier types node).substAt index valid replacement =
      graph.carrier (fun key => (types key).substAt index valid replacement) node :=
  precise_substAt graph.support _ index valid replacement

omit [DecidableEq Node] in
private theorem Graph.fieldShape_substAt {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy (depth + 1)) (answer : WFTy (depth + 1))
    (field : Field Node Label) (index : Nat) (valid : index ≤ depth)
    (replacement : WFTy depth) :
    (graph.fieldShape types answer field).substAt index valid replacement =
      graph.fieldShape (fun key => (types key).substAt index valid replacement)
        (answer.substAt index valid replacement) field := by
  simp only [fieldShape, runtimeShape_substAt, carrier_substAt]

private theorem constraint_substAt {depth : Nat} (sub sup : WFTy (depth + 1))
    (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (WFConstraint.constr sub sup).substAt index valid replacement =
      WFConstraint.constr (sub.substAt index valid replacement)
        (sup.substAt index valid replacement) := rfl

private theorem invariant_substAt {depth : Nat} (presence shape : WFTy (depth + 1))
    (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (CarrierFieldPresence.invariant presence shape).substAt index valid replacement =
      CarrierFieldPresence.invariant (presence.substAt index valid replacement)
        (shape.substAt index valid replacement) := rfl

omit [DecidableEq Node] in
private theorem Graph.fieldGuards_substAt {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy (depth + 1)) (answer : WFTy (depth + 1))
    (field : Field Node Label) (index : Nat) (valid : index ≤ depth)
    (replacement : WFTy depth) :
    (graph.fieldGuards types answer field).map
        (fun guard => guard.substAt index valid replacement) =
      graph.fieldGuards (fun key => (types key).substAt index valid replacement)
        (answer.substAt index valid replacement) field := by
  simp only [fieldGuards, List.map_cons, List.map_nil, constraint_substAt,
    carrier_substAt, invariant_substAt, fieldShape_substAt]

omit [DecidableEq Node] in
private theorem Graph.guards_substAt {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy (depth + 1)) (view answer : WFTy (depth + 1))
    (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (graph.guards types view answer).map (fun guard => guard.substAt index valid replacement) =
      graph.guards (fun key => (types key).substAt index valid replacement)
        (view.substAt index valid replacement) (answer.substAt index valid replacement) := by
  simp only [guards, List.map_cons, constraint_substAt, carrier_substAt,
    List.map_flatMap, fieldGuards_substAt]

private theorem withGuards_substAt {depth : Nat} (guards : List (WFConstraint (depth + 1)))
    (rest : Interface (depth + 1)) (index : Nat) (valid : index ≤ depth)
    (replacement : WFTy depth) :
    (withGuards guards rest).substAt index valid replacement =
      withGuards (guards.map (fun guard => guard.substAt index valid replacement))
        (rest.substAt index valid replacement) := by
  induction guards with
  | nil => rfl
  | cons first remaining ih =>
      simpa only [withGuards, List.foldr_cons, Interface.substAt, List.map_cons] using
        congrArg (Interface.guard (first.substAt index valid replacement)) ih

omit [DecidableEq Node] in
private theorem Graph.body_substAt {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy (depth + 1)) (view answer : WFTy (depth + 1))
    (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (graph.body types view answer).substAt index valid replacement =
      graph.body (fun key => (types key).substAt index valid replacement)
        (view.substAt index valid replacement) (answer.substAt index valid replacement) := by
  simp only [body, withGuards_substAt, guards_substAt, Interface.substAt]

theorem Graph.telescope_substAt (graph : Graph Node Label) (remaining : List (Node × Label))
    {depth : Nat} (types : Node × Label → WFTy (depth + 1))
    (view answer : WFTy (depth + 1)) (index : Nat) (valid : index ≤ depth)
    (replacement : WFTy depth) :
    (graph.telescope remaining types view answer).substAt index valid replacement =
      graph.telescope remaining (fun key => (types key).substAt index valid replacement)
        (view.substAt index valid replacement) (answer.substAt index valid replacement) := by
  induction remaining generalizing depth index with
  | nil => exact graph.body_substAt types view answer index valid replacement
  | cons key rest ih =>
      simp only [telescope, Interface.substAt]
      rw [ih, bindComponent_substAt, WFTy.substAt_weaken, WFTy.substAt_weaken]

theorem Graph.telescope_instantiateCurrent (graph : Graph Node Label)
    (remaining : List (Node × Label)) {depth : Nat} (types : Node × Label → WFTy depth)
    (view answer : WFTy depth) (key : Node × Label) :
    (graph.telescope remaining (bindComponent types key) view.weaken answer.weaken).instantiate
        (types key) = graph.telescope remaining types view answer := by
  change (graph.telescope remaining _ _ _).substAt 0 (Nat.zero_le depth) _ = _
  rw [graph.telescope_substAt]
  change graph.telescope remaining
    (fun selected => (bindComponent types key selected).instantiate (types key))
    (view.weaken.instantiate (types key)) (answer.weaken.instantiate (types key)) = _
  rw [bindComponent_instantiate, WFTy.weaken_instantiate_cancel,
    WFTy.weaken_instantiate_cancel]

theorem Graph.telescope_congr (graph : Graph Node Label) (remaining : List (Node × Label))
    {depth : Nat} {left right : Node × Label → WFTy depth} (view answer : WFTy depth)
    (equal : ∀ key, key ∉ remaining → left key = right key) :
    graph.telescope remaining left view answer = graph.telescope remaining right view answer := by
  induction remaining generalizing depth with
  | nil =>
      exact congrArg (fun types => graph.body types view answer)
        (funext fun key => equal key (by simp))
  | cons key rest ih =>
      simp only [telescope]
      apply congrArg Interface.bind
      apply ih
      intro selected absent
      by_cases same : selected = key
      · simp only [bindComponent, same, ite_true]
      · simp only [bindComponent, same, ite_false]
        exact congrArg WFTy.weaken (equal selected (by simp [same, absent]))

private def withGuardsInstance {s : SubtypingContext} (guards : List (WFConstraint s.typeDepth))
    {rest : Interface s.typeDepth} {type : WFTy s.typeDepth}
    (evidence : ∀ guard ∈ guards, InvertingSubtype ghost s guard.sub guard.sup)
    (inst : InterfaceInstance ghost s rest type) :
    InterfaceInstance ghost s (withGuards guards rest) type := by
  induction guards with
  | nil => exact inst
  | cons first remaining ih =>
      exact .guard (evidence first List.mem_cons_self)
        (ih (fun guard member => evidence guard (List.mem_cons_of_mem first member)))

/-- The only target proof inputs are the explicit, computed graph constraints. -/
def Graph.telescopeInstance {s : SubtypingContext} (graph : Graph Node Label)
    (remaining : List (Node × Label)) (types : Node × Label → WFTy s.typeDepth)
    (view answer : WFTy s.typeDepth)
    (evidence : ∀ guard ∈ graph.guards types view answer,
      InvertingSubtype ghost s guard.sub guard.sup) :
    InterfaceInstance ghost s (graph.telescope remaining types view answer)
      (types (graph.root, graph.payload)) := by
  induction remaining with
  | nil => exact withGuardsInstance (graph.guards types view answer) evidence (.payload _)
  | cons key rest ih =>
      refine .bind (types key) ?_
      rw [graph.telescope_instantiateCurrent]
      exact ih

omit [DecidableEq Node] [DecidableEq Label] in
private theorem Graph.rowKey_member (graph : Graph Node Label) {node : Node}
    (nodePresent : node ∈ graph.nodes) {label : Label} (labelPresent : label ∈ graph.support) :
    (node, label) ∈ graph.keys :=
  List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨node, nodePresent, List.mem_map.mpr ⟨label, labelPresent, rfl⟩⟩))

omit [DecidableEq Node] [DecidableEq Label] in
private theorem Graph.childNode_member (graph : Graph Node Label) {field : Field Node Label}
    (present : field ∈ graph.fields) : field.child ∈ graph.nodes :=
  List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨field, present, by simp⟩)

omit [DecidableEq Node] [DecidableEq Label] in
private theorem Graph.fieldKey_member (graph : Graph Node Label) {field : Field Node Label}
    (present : field ∈ graph.fields) {key : Node × Label}
    (member : key ∈ [(field.parent, graph.payload), (field.parent, field.presenceLabel),
      (field.parent, field.childLabel)]) : key ∈ graph.keys :=
  List.mem_cons_of_mem _
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨field, present, member⟩))

private theorem Graph.carrier_complete {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) {node : Node} (present : node ∈ graph.nodes) :
    graph.carrier (graph.complete types) node = graph.carrier types node :=
  precise_congr graph.support (fun _ member =>
    graph.complete_at types (graph.rowKey_member present member))

private theorem Graph.fieldGuards_complete {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) (answer : WFTy depth) {field : Field Node Label}
    (present : field ∈ graph.fields) :
    graph.fieldGuards (graph.complete types) answer field =
      graph.fieldGuards types answer field := by
  have childKey := graph.complete_at types
    (graph.fieldKey_member present (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  have presenceKey := graph.complete_at types
    (graph.fieldKey_member present (List.mem_cons_of_mem _ List.mem_cons_self))
  have payloadKey := graph.complete_at types (graph.fieldKey_member present List.mem_cons_self)
  simp only [fieldGuards, fieldShape, childKey, presenceKey, payloadKey,
    graph.carrier_complete types (graph.childNode_member present)]

/-- The default outside the allocated keys never changes a generated constraint. -/
theorem Graph.guards_complete {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) (view answer : WFTy depth) :
    graph.guards (graph.complete types) view answer = graph.guards types view answer := by
  simp only [guards, graph.carrier_complete types List.mem_cons_self]
  exact congrArg (List.cons _) (List.flatMap_congr
    (fun field present => graph.fieldGuards_complete types answer present))

omit [DecidableEq Node] in
/-- Compose producer evidence in the same order as the generated graph guard list. -/
theorem Graph.guardEvidence {s : SubtypingContext} (graph : Graph Node Label)
    (types : Node × Label → WFTy s.typeDepth) (view answer : WFTy s.typeDepth)
    (source : InvertingSubtype ghost s (graph.carrier types graph.root) view)
    (children : ∀ field ∈ graph.fields,
      InvertingSubtype ghost s (types (field.parent, field.childLabel))
          (graph.carrier types field.child) ∧
        InvertingSubtype ghost s (graph.carrier types field.child)
          (types (field.parent, field.childLabel)))
    (runtime : ∀ field ∈ graph.fields,
      InvertingSubtype ghost s (types (field.parent, graph.payload))
        (CarrierFieldPresence.invariant (types (field.parent, field.presenceLabel))
          (graph.fieldShape types answer field))) :
    ∀ guard ∈ graph.guards types view answer, InvertingSubtype ghost s guard.sub guard.sup := by
  intro guard member
  rcases List.mem_cons.mp member with rfl | member
  · exact source
  · obtain ⟨field, present, member⟩ := List.mem_flatMap.mp member
    rcases List.mem_cons.mp member with rfl | member
    · exact (children field present).1
    · rcases List.mem_cons.mp member with rfl | member
      · exact (children field present).2
      · obtain rfl := List.mem_singleton.mp member
        exact runtime field present

/-- All graph witnesses are hidden by the same finite telescope. -/
def Graph.packingInstance {s : SubtypingContext} (graph : Graph Node Label)
    (types : Node × Label → WFTy s.typeDepth) (view answer : WFTy s.typeDepth)
    (evidence : ∀ guard ∈ graph.guards types view answer,
      InvertingSubtype ghost s guard.sub guard.sup) :
    InterfaceInstance ghost s (graph.interface view answer)
      (types (graph.root, graph.payload)) := by
  have equal := graph.telescope_congr graph.keys (left := fun _ => WFTy.top)
    (right := graph.complete types) view answer (fun key absent => by simp [complete, absent])
  unfold interface
  rw [equal]
  have inst := graph.telescopeInstance graph.keys (graph.complete types) view answer
    (fun guard member => evidence guard ((graph.guards_complete types view answer) ▸ member))
  simpa only [graph.complete_at types (key := (graph.root, graph.payload))
    List.mem_cons_self] using inst

/-- An arbitrary mixed payload derivation is packed without changing its runtime representation. -/
theorem Graph.packTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    (graph : Graph Node Label) (types : Node × Label → WFTy s.typeDepth)
    (view answer : WFTy s.typeDepth)
    (evidence : ∀ guard ∈ graph.guards types view answer,
      InvertingSubtype ghost s guard.sub guard.sup) {term : Term}
    (typing : HasType ghost s context term (types (graph.root, graph.payload))) :
    HasType ghost s context (pack term) ((graph.interface view answer).package answer) :=
  interfacePackTyping (graph.packingInstance types view answer evidence) typing

private theorem withGuardsOpened {depth : Nat} (guards : List (WFConstraint depth))
    (payload : WFTy depth) (assumptions : List (WFConstraint depth))
    (context : TypingContext depth) (body : Term) (answer : WFTy depth) :
    InterfaceOpened ghost (withGuards guards (.payload payload)) assumptions context body answer ↔
      HasType ghost ⟨depth, guards.reverse ++ assumptions⟩
        (context.bind payload) body answer := by
  induction guards generalizing assumptions with
  | nil => rfl
  | cons first remaining ih =>
      rw [List.reverse_cons, List.append_assoc, List.singleton_append]
      exact ih (first :: assumptions)

/-- The opened scope is exactly the exported graph guard list, followed by outer assumptions. -/
def Graph.openContext {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) (view answer : WFTy depth)
    (assumptions : List (WFConstraint depth)) : SubtypingContext :=
  ⟨depth, (graph.guards types view answer).reverse ++ assumptions⟩

omit [DecidableEq Node] in
theorem Graph.bodyOpened {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) (view runtimeAnswer : WFTy depth)
    (assumptions : List (WFConstraint depth)) (context : TypingContext depth)
    (body : Term) (answer : WFTy depth) :
    InterfaceOpened ghost (graph.body types view runtimeAnswer) assumptions context body answer ↔
      HasType ghost (graph.openContext types view runtimeAnswer assumptions)
        (context.bind (types (graph.root, graph.payload))) body answer :=
  withGuardsOpened _ _ _ _ _ _

def Graph.Opened (graph : Graph Node Label) (ghost : FieldName → Bool) :
    (remaining : List (Node × Label)) → {depth : Nat} →
      (Node × Label → WFTy depth) → WFTy depth → WFTy depth →
      List (WFConstraint depth) → TypingContext depth → Term → WFTy depth → Prop
  | [], _, types, view, runtimeAnswer, assumptions, context, body, answer =>
      HasType ghost (graph.openContext types view runtimeAnswer assumptions)
        (context.bind (types (graph.root, graph.payload))) body answer
  | key :: rest, _, types, view, runtimeAnswer, assumptions, context, body, answer =>
      graph.Opened ghost rest (bindComponent types key) view.weaken runtimeAnswer.weaken
        (assumptions.map WFConstraint.weaken) context.bindType (body.liftTy 1) answer.weaken

/-- Every abstract node witness remains in scope over the whole consumer. -/
theorem Graph.telescopeOpened {depth : Nat} (graph : Graph Node Label)
    (remaining : List (Node × Label)) (types : Node × Label → WFTy depth)
    (view runtimeAnswer : WFTy depth) (assumptions : List (WFConstraint depth))
    (context : TypingContext depth) (body : Term) (answer : WFTy depth) :
    InterfaceOpened ghost (graph.telescope remaining types view runtimeAnswer)
        assumptions context body answer ↔
      graph.Opened ghost remaining types view runtimeAnswer
        assumptions context body answer := by
  induction remaining generalizing depth body with
  | nil => exact graph.bodyOpened types view runtimeAnswer assumptions context body answer
  | cons key rest ih =>
      exact ih (bindComponent types key) view.weaken runtimeAnswer.weaken
        (assumptions.map WFConstraint.weaken) context.bindType (body.liftTy 1) answer.weaken

/-- Opening a package scopes every graph witness and invariant over the same client body. -/
theorem Graph.unpackTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    (graph : Graph Node Label) (view answer : WFTy s.typeDepth) {value body : Term}
    (producer : HasType ghost s context value ((graph.interface view answer).package answer))
    (consumer : graph.Opened ghost graph.keys (fun _ => WFTy.top) view answer
      s.assumptions context body answer) :
    HasType ghost s context (.app value (.abs body)) answer :=
  interfaceUnpackTyping producer
    ((graph.telescopeOpened graph.keys (fun _ => WFTy.top) view answer
      s.assumptions context body answer).mpr consumer)

omit [DecidableEq Node] in
theorem Graph.openedGuard {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) (view answer : WFTy depth)
    (assumptions : List (WFConstraint depth)) {guard : WFConstraint depth}
    (present : guard ∈ graph.guards types view answer) :
    Subtype (graph.openContext types view answer assumptions) guard.sub guard.sup :=
  @Subtype.hyp (graph.openContext types view answer assumptions) guard
    (List.mem_append_left _ (List.mem_reverse.mpr present))

omit [DecidableEq Node] in
theorem Graph.fieldGuard_member {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) (view answer : WFTy depth)
    {field : Field Node Label} (present : field ∈ graph.fields) {guard : WFConstraint depth}
    (member : guard ∈ graph.fieldGuards types answer field) :
    guard ∈ graph.guards types view answer :=
  List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨field, present, member⟩)

omit [DecidableEq Node] in
/-- The child anchor equations survive opening alongside all node invariants. -/
theorem Graph.openedChild {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) (view answer : WFTy depth)
    (assumptions : List (WFConstraint depth)) {field : Field Node Label}
    (present : field ∈ graph.fields) :
    Subtype (graph.openContext types view answer assumptions)
        (types (field.parent, field.childLabel)) (graph.carrier types field.child) ∧
      Subtype (graph.openContext types view answer assumptions)
        (graph.carrier types field.child) (types (field.parent, field.childLabel)) :=
  ⟨graph.openedGuard types view answer assumptions
      (graph.fieldGuard_member types view answer present List.mem_cons_self),
    graph.openedGuard types view answer assumptions
      (graph.fieldGuard_member types view answer present
        (List.mem_cons_of_mem _ List.mem_cons_self))⟩

omit [DecidableEq Node] in
/-- A field's runtime bound is an exported constraint, not an independent client premise. -/
theorem Graph.openedUniform {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) (view answer : WFTy depth)
    (assumptions : List (WFConstraint depth)) {field : Field Node Label}
    (present : field ∈ graph.fields) :
    Subtype (graph.openContext types view answer assumptions)
      (types (field.parent, graph.payload))
      (CarrierFieldPresence.invariant (types (field.parent, field.presenceLabel))
        (graph.fieldShape types answer field)) :=
  graph.openedGuard types view answer assumptions
    (graph.fieldGuard_member types view answer present
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- A base child package introduces only this anchor; the graph remains in its outer scope. -/
def Graph.openingGuard {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) (node : Node) (fresh : Label → WFTy depth) :
    WFConstraint depth :=
  WFConstraint.constr (precise graph.support fresh) (graph.carrier types node)

/-- The explicit state after opening two child packages from the same finite graph. -/
def Graph.twoOpenContext {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) (view answer : WFTy depth)
    (assumptions : List (WFConstraint depth)) (first second : Field Node Label)
    (freshFirst freshSecond : Label → WFTy depth) : SubtypingContext :=
  ((graph.openContext types view answer assumptions).assume
    (graph.openingGuard types first.child freshFirst)).assume
      (graph.openingGuard types second.child freshSecond)

omit [DecidableEq Node] in
/-- Reopening a precise child identifies every new witness with its original graph witness. -/
theorem Graph.reopenedBounds {s : SubtypingContext} (graph : Graph Node Label)
    (types : Node × Label → WFTy s.typeDepth) (node : Node) (fresh : Label → WFTy s.typeDepth)
    (anchor : InvertingSubtype carrierPolicy s (precise graph.support fresh)
      (graph.carrier types node)) {label : Label} (present : label ∈ graph.support) :
    InvertingSubtype carrierPolicy s (fresh label) (types (node, label)) ∧
      InvertingSubtype carrierPolicy s (types (node, label)) (fresh label) :=
  precise_bounds present anchor

omit [DecidableEq Node] in
/-- Two adjacent projections reuse the existing child invariants and all final member witnesses.
The presence inputs are the bounds obtained from source field typing; both opening anchors and
all runtime invariants are retrieved from their actual exported guard lists. -/
theorem Graph.twoStep {depth : Nat} (graph : Graph Node Label)
    (types : Node × Label → WFTy depth) (view answer : WFTy depth)
    (assumptions : List (WFConstraint depth)) {first second : Field Node Label}
    (firstMember : first ∈ graph.fields) (secondMember : second ∈ graph.fields)
    (adjacent : second.parent = first.child) (freshFirst freshSecond : Label → WFTy depth)
    (firstPresence : InvertingSubtype carrierPolicy
      (graph.twoOpenContext types view answer assumptions first second freshFirst freshSecond)
      WFTy.top (types (first.parent, first.presenceLabel)))
    (secondPresence : InvertingSubtype carrierPolicy
      (graph.twoOpenContext types view answer assumptions first second freshFirst freshSecond)
      WFTy.top (types (second.parent, second.presenceLabel))) :
    InvertingSubtype carrierPolicy
        (graph.twoOpenContext types view answer assumptions first second freshFirst freshSecond)
        (types (first.parent, graph.payload)) (graph.fieldShape types answer first) ∧
      InvertingSubtype carrierPolicy
        (graph.twoOpenContext types view answer assumptions first second freshFirst freshSecond)
        (freshFirst graph.payload) (graph.fieldShape types answer second) ∧
      ∀ label ∈ graph.support,
        InvertingSubtype carrierPolicy
            (graph.twoOpenContext types view answer assumptions first second freshFirst freshSecond)
            (freshSecond label) (types (second.child, label)) ∧
          InvertingSubtype carrierPolicy
            (graph.twoOpenContext types view answer assumptions first second freshFirst freshSecond)
            (types (second.child, label)) (freshSecond label) := by
  let s := graph.twoOpenContext types view answer assumptions first second freshFirst freshSecond
  let firstGuard := graph.openingGuard types first.child freshFirst
  let secondGuard := graph.openingGuard types second.child freshSecond
  have firstAnchor : InvertingSubtype carrierPolicy s (precise graph.support freshFirst)
      (graph.carrier types first.child) :=
    .native (@Subtype.hyp s firstGuard (List.mem_cons_of_mem _ List.mem_cons_self))
  have secondAnchor : InvertingSubtype carrierPolicy s (precise graph.support freshSecond)
      (graph.carrier types second.child) :=
    .native (@Subtype.hyp s secondGuard List.mem_cons_self)
  have firstUniform : InvertingSubtype carrierPolicy s (types (first.parent, graph.payload))
      (CarrierFieldPresence.invariant (types (first.parent, first.presenceLabel))
        (graph.fieldShape types answer first)) :=
    .native (((graph.openedUniform types view answer assumptions firstMember).weakenAssumption
      firstGuard).weakenAssumption secondGuard)
  have secondUniform : InvertingSubtype carrierPolicy s (types (second.parent, graph.payload))
      (CarrierFieldPresence.invariant (types (second.parent, second.presenceLabel))
        (graph.fieldShape types answer second)) :=
    .native (((graph.openedUniform types view answer assumptions secondMember).weakenAssumption
      firstGuard).weakenAssumption secondGuard)
  have payloadBound : InvertingSubtype carrierPolicy s (freshFirst graph.payload)
      (types (second.parent, graph.payload)) := by
    simpa only [adjacent] using
      (graph.reopenedBounds (s := s) types first.child freshFirst firstAnchor
        graph.payloadPresent).1
  exact ⟨CarrierFieldPresence.extract firstUniform firstPresence,
    payloadBound.trans (CarrierFieldPresence.extract secondUniform secondPresence),
    fun label present =>
      graph.reopenedBounds (s := s) types second.child freshSecond secondAnchor present⟩

end CDotFCCT.CTML.Mixed.CarrierRuntimeInterface
