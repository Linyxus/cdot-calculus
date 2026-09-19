import CDotFCCT.MemberUses
import CDotFCCT.CTML.CarrierEquationInterpretation
import CDotFCCT.CTML.MixedCarrierLayout

/-!
# Finite equations for demanded source paths

Every node has a named precise carrier. A demanded child component refers to the
child's name; other components retain their outer witnesses. The complete system
is guarded by the existing ghost rows and therefore has a simultaneous solution.
No requested source bound occurs in these generated equations.
-/

set_option autoImplicit false

namespace CDotFCCT.CarrierPathGraph

open CDot CTMLCore CTML.Mixed

universe u
variable [Signature] {Label : Type u} [DecidableEq Label]

private theorem components_congr {depth : Nat} (support entries : List Label)
    (left right : Label → WFTy depth) (equal : ∀ label ∈ entries, left label = right label)
    (field : Syntax.FieldName) :
    CarrierLayout.components support entries left field =
      CarrierLayout.components support entries right field := by
  induction entries with
  | nil => rfl
  | cons label rest ih =>
      simp only [CarrierLayout.components, equal label List.mem_cons_self,
        ih (fun other member => equal other (List.mem_cons_of_mem label member))]

theorem precise_congr {depth : Nat} (support : List Label) (left right : Label → WFTy depth)
    (equal : ∀ label ∈ support, left label = right label) :
    CarrierLayout.precise support left = CarrierLayout.precise support right :=
  congrArg (row (CarrierLayout.names support))
    (funext (components_congr support support left right equal))

def select (node : MemberUses.PathKey) (field : Signature.TrmLabel) : MemberUses.PathKey :=
  ⟨node.owner, field :: node.fields⟩

/-- Source paths store their final field first, so deleting the head gives the parent. -/
def prefixes (owner : MemberUses.Owner) : Fields → List MemberUses.PathKey
  | [] => [⟨owner, []⟩]
  | field :: rest => ⟨owner, field :: rest⟩ :: prefixes owner rest

def close (nodes : List MemberUses.PathKey) : List MemberUses.PathKey :=
  (nodes.flatMap (fun node => prefixes node.owner node.fields)).eraseDups

theorem self_mem_prefixes (owner : MemberUses.Owner) (fields : Fields) :
    (⟨owner, fields⟩ : MemberUses.PathKey) ∈ prefixes owner fields := by
  cases fields <;> exact List.mem_cons_self

theorem mem_close {nodes : List MemberUses.PathKey} {node : MemberUses.PathKey}
    (present : node ∈ nodes) : node ∈ close nodes :=
  List.mem_eraseDups.mpr
    (List.mem_flatMap.mpr ⟨node, present, self_mem_prefixes node.owner node.fields⟩)

/-- The component label type is shared with the source compiler, not re-encoded here. -/
structure Graph (Label : Type u) where
  support : List Label
  nodes : List MemberUses.PathKey
  childField : Label → Option Signature.TrmLabel

namespace Graph

variable {depth : Nat}

def index (graph : Graph Label) (node : MemberUses.PathKey) (present : node ∈ graph.nodes) :
    Fin graph.nodes.length :=
  ⟨graph.nodes.idxOf node, List.idxOf_lt_length_of_mem present⟩

def component (graph : Graph Label) (outer : MemberUses.PathKey → Label → WFTy depth)
    (node : MemberUses.PathKey) (label : Label) :
    CarrierEquation.Expr carrierPolicy depth graph.nodes.length :=
  match graph.childField label with
  | none => .leaf (outer node label)
  | some field =>
      if present : select node field ∈ graph.nodes then .ref (graph.index _ present)
      else .leaf (outer node label)

def system (graph : Graph Label) (outer : MemberUses.PathKey → Label → WFTy depth) :
    CarrierEquation.System carrierPolicy depth graph.nodes.length where
  body index := CarrierEquation.Expr.precise graph.support (carrierPolicy_names graph.support)
    (graph.component outer (graph.nodes.get index))
  guarded _ := CarrierEquation.Expr.precise_guarded _ _ _

def carrier (graph : Graph Label) (outer : MemberUses.PathKey → Label → WFTy depth)
    (node : MemberUses.PathKey) : WFTy (depth + graph.nodes.length) :=
  CarrierLayout.precise graph.support (fun label => (graph.component outer node label).compile)

theorem compile_at (graph : Graph Label) (outer : MemberUses.PathKey → Label → WFTy depth)
    (node : MemberUses.PathKey) (present : node ∈ graph.nodes) :
    (graph.system outer).compile (graph.index node present) = graph.carrier outer node := by
  simp only [system, CarrierEquation.System.compile, CarrierEquation.Expr.compile_precise,
    index, List.get_eq_getElem, List.getElem_idxOf, carrier]

theorem component_child (graph : Graph Label) (outer : MemberUses.PathKey → Label → WFTy depth)
    (node : MemberUses.PathKey) (label : Label) (field : Signature.TrmLabel)
    (child : graph.childField label = some field) (present : select node field ∈ graph.nodes) :
    (graph.component outer node label).compile =
      (graph.system outer).name (graph.index (select node field) present) := by
  simp only [component, child, dite_eq_left present, CarrierEquation.Expr.compile_ref,
    CarrierEquation.System.name]

def context (graph : Graph Label) (outer : MemberUses.PathKey → Label → WFTy depth)
    (source : List (WFConstraint (depth + graph.nodes.length))) : SubtypingContext :=
  ⟨depth + graph.nodes.length, (graph.system outer).equations ++ source⟩

theorem unfold (graph : Graph Label) (outer : MemberUses.PathKey → Label → WFTy depth)
    (source : List (WFConstraint (depth + graph.nodes.length)))
    (node : MemberUses.PathKey) (present : node ∈ graph.nodes) :
    InvertingSubtype carrierPolicy (graph.context outer source)
      ((graph.system outer).name (graph.index node present)) (graph.carrier outer node) := by
  rw [← graph.compile_at outer node present]
  exact .native (@Subtype.hyp (graph.context outer source)
    ((graph.system outer).unfoldGuard (graph.index node present))
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨_, rfl⟩))))

theorem fold (graph : Graph Label) (outer : MemberUses.PathKey → Label → WFTy depth)
    (source : List (WFConstraint (depth + graph.nodes.length)))
    (node : MemberUses.PathKey) (present : node ∈ graph.nodes) :
    InvertingSubtype carrierPolicy (graph.context outer source)
      (graph.carrier outer node) ((graph.system outer).name (graph.index node present)) := by
  rw [← graph.compile_at outer node present]
  exact .native (@Subtype.hyp (graph.context outer source)
    ((graph.system outer).foldGuard (graph.index node present))
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨_, rfl⟩))))

/-- Both directions come from a solved equation, independently of the requested child type. -/
theorem child_unfold (graph : Graph Label) (outer : MemberUses.PathKey → Label → WFTy depth)
    (source : List (WFConstraint (depth + graph.nodes.length)))
    (node : MemberUses.PathKey) (label : Label) (field : Signature.TrmLabel)
    (child : graph.childField label = some field) (present : select node field ∈ graph.nodes) :
    InvertingSubtype carrierPolicy (graph.context outer source)
      (graph.component outer node label).compile (graph.carrier outer (select node field)) := by
  rw [graph.component_child outer node label field child present]
  exact graph.unfold outer source (select node field) present

theorem child_fold (graph : Graph Label) (outer : MemberUses.PathKey → Label → WFTy depth)
    (source : List (WFConstraint (depth + graph.nodes.length)))
    (node : MemberUses.PathKey) (label : Label) (field : Signature.TrmLabel)
    (child : graph.childField label = some field) (present : select node field ∈ graph.nodes) :
    InvertingSubtype carrierPolicy (graph.context outer source)
      (graph.carrier outer (select node field)) (graph.component outer node label).compile := by
  rw [graph.component_child outer node label field child present]
  exact graph.fold outer source (select node field) present

end Graph

end CDotFCCT.CarrierPathGraph
