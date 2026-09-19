import CDotFCCT.CTML.RecursivePackages
import Mathlib.Data.Fintype.Powerset

/-!
# Generating recursive package witnesses in the presence of aliases

An equation may contain bare references and intersections outside its guarded
arrows. The compiler collects the arrow domains reachable through those alias
edges and uses their union as one recursive arrow's domain. A component with no
reachable arrow receives the empty union, `Bottom`.

Both directions of every original equation follow by native subtyping. Thus a
self alias, or an intersection containing one, does not require an unguarded
recursive type declaration. Arrow domains may contain arbitrary native types,
including references to every member, records, universals and constraints.

The finite reachability decision below is an executable reference implementation:
it enumerates closed vertex sets. Its proofs do not assume a graph solver or
equation evidence supplied by the caller.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.RecursiveAliases

open CTMLCore

namespace Graph

abbrev Edges (size : Nat) := Fin size → List (Fin size)

def Closed {size : Nat} (edges : Edges size) (vertices : Finset (Fin size)) : Prop :=
  ∀ source ∈ vertices, ∀ target ∈ edges source, target ∈ vertices

instance {size : Nat} (edges : Edges size) (vertices : Finset (Fin size)) :
    Decidable (Closed edges vertices) := inferInstanceAs (Decidable (∀ _ ∈ _, ∀ _ ∈ _, _))

/-- Membership in every edge-closed set containing the initial vertex. -/
def Reach {size : Nat} (edges : Edges size) (source target : Fin size) : Prop :=
  ∀ vertices : Finset (Fin size), source ∈ vertices → Closed edges vertices → target ∈ vertices

instance {size : Nat} (edges : Edges size) (source target : Fin size) :
    Decidable (Reach edges source target) := inferInstanceAs (Decidable (∀ _, _ → _ → _))

theorem Reach.refl {size : Nat} {edges : Edges size} (source : Fin size) :
    Reach edges source source := fun _ contains _ => contains

theorem Reach.edge {size : Nat} {edges : Edges size} {source target : Fin size}
    (edge : target ∈ edges source) : Reach edges source target :=
  fun _ contains closed => closed source contains target edge

theorem Reach.trans {size : Nat} {edges : Edges size} {source middle target : Fin size}
    (first : Reach edges source middle) (second : Reach edges middle target) :
    Reach edges source target := fun vertices contains closed =>
  second vertices (first vertices contains closed) closed

theorem Reach.head {size : Nat} {edges : Edges size} {source target : Fin size}
    (path : Reach edges source target) :
    source = target ∨ ∃ next ∈ edges source, Reach edges next target := by
  let vertices := Finset.univ.filter
    (fun last => source = last ∨ ∃ next ∈ edges source, Reach edges next last)
  refine (Finset.mem_filter.mp (path vertices ?_ ?_)).2
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, .inl rfl⟩
  · intro here membership next edge
    rcases (Finset.mem_filter.mp membership).2 with rfl | ⟨first, firstEdge, rest⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, .inr ⟨next, edge, .refl _⟩⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, .inr ⟨first, firstEdge, rest.trans (.edge edge)⟩⟩

end Graph

/-- An equation's outer intersections and aliases, with already-guarded arrow leaves. -/
inductive Equation (depth size : Nat) where
  | arrow (domain : WFTy depth)
  | reference (index : Fin size)
  | intersection (left right : Equation depth size)

namespace Equation

def references {depth size : Nat} : Equation depth size → List (Fin size)
  | .arrow _ => []
  | .reference index => [index]
  | .intersection left right => left.references ++ right.references

def domains {depth size : Nat} : Equation depth size → List (WFTy depth)
  | .arrow domain => [domain]
  | .reference _ => []
  | .intersection left right => left.domains ++ right.domains

def denote {depth size : Nat} (names : Fin size → WFTy depth) (answer : WFTy depth) :
    Equation depth size → WFTy depth
  | .arrow domain => WFTy.arrow domain answer
  | .reference index => names index
  | .intersection left right => WFTy.intersection (left.denote names answer)
      (right.denote names answer)

def consumer {depth size : Nat} (consumers : Fin size → WFTy depth) :
    Equation depth size → WFTy depth
  | .arrow domain => domain
  | .reference index => consumers index
  | .intersection left right => WFTy.union (left.consumer consumers) (right.consumer consumers)

theorem consumer_le {size : Nat} {s : SubtypingContext}
    (equation : Equation s.typeDepth size) (consumers : Fin size → WFTy s.typeDepth)
    (upper : WFTy s.typeDepth)
    (atoms : ∀ domain ∈ equation.domains, Subtype s domain upper)
    (aliases : ∀ index ∈ equation.references, Subtype s (consumers index) upper) :
    Subtype s (equation.consumer consumers) upper := by
  induction equation with
  | arrow domain => exact atoms domain (List.mem_singleton_self _)
  | reference index => exact aliases index (List.mem_singleton_self _)
  | intersection left right ihLeft ihRight =>
      exact .unionLe
        (ihLeft (fun domain member => atoms domain (List.mem_append_left _ member))
          (fun index member => aliases index (List.mem_append_left _ member)))
        (ihRight (fun domain member => atoms domain (List.mem_append_right _ member))
          (fun index member => aliases index (List.mem_append_right _ member)))

theorem domain_le_consumer {size : Nat} {s : SubtypingContext}
    (equation : Equation s.typeDepth size) (consumers : Fin size → WFTy s.typeDepth)
    {domain : WFTy s.typeDepth} (member : domain ∈ equation.domains) :
    Subtype s domain (equation.consumer consumers) := by
  induction equation with
  | arrow other =>
      cases List.mem_singleton.mp member
      exact .refl
  | reference index => exact False.elim (List.not_mem_nil member)
  | intersection left right ihLeft ihRight =>
      exact (List.mem_append.mp member).elim
        (fun belongs => (ihLeft belongs).trans .leUnionLeft)
        (fun belongs => (ihRight belongs).trans .leUnionRight)

theorem reference_le_consumer {size : Nat} {s : SubtypingContext}
    (equation : Equation s.typeDepth size) (consumers : Fin size → WFTy s.typeDepth)
    {index : Fin size} (member : index ∈ equation.references) :
    Subtype s (consumers index) (equation.consumer consumers) := by
  induction equation with
  | arrow domain => exact False.elim (List.not_mem_nil member)
  | reference other =>
      cases List.mem_singleton.mp member
      exact .refl
  | intersection left right ihLeft ihRight =>
      exact (List.mem_append.mp member).elim
        (fun belongs => (ihLeft belongs).trans .leUnionLeft)
        (fun belongs => (ihRight belongs).trans .leUnionRight)

theorem normalize {size : Nat} {s : SubtypingContext}
    {names consumers : Fin size → WFTy s.typeDepth} {answer : WFTy s.typeDepth}
    (unfold : ∀ index, Subtype s (names index) (WFTy.arrow (consumers index) answer))
    (fold : ∀ index, Subtype s (WFTy.arrow (consumers index) answer) (names index))
    (equation : Equation s.typeDepth size) :
    Subtype s (equation.denote names answer) (WFTy.arrow (equation.consumer consumers) answer) ∧
      Subtype s (WFTy.arrow (equation.consumer consumers) answer)
        (equation.denote names answer) := by
  induction equation with
  | arrow domain => exact ⟨.refl, .refl⟩
  | reference index => exact ⟨unfold index, fold index⟩
  | intersection left right ihLeft ihRight =>
      exact ⟨(Subtype.interMono ihLeft.1 ihRight.1).trans .arrowParamDistribution,
        .leInter ((Subtype.arrow .leUnionLeft .refl).trans ihLeft.2)
          ((Subtype.arrow .leUnionRight .refl).trans ihRight.2)⟩

def witness {size : Nat} {s : SubtypingContext} {names : Fin size → WFTy s.typeDepth}
    {answer : WFTy s.typeDepth} (packages : ∀ index, Coercion.PackageWitness s answer (names index))
    (equation : Equation s.typeDepth size) :
    Coercion.PackageWitness s answer (equation.denote names answer) :=
  ⟨equation.consumer (fun index => (packages index).consumer),
    (equation.normalize (fun index => (packages index).unfold)
      (fun index => (packages index).fold)).1,
    (equation.normalize (fun index => (packages index).unfold)
      (fun index => (packages index).fold)).2⟩

end Equation

def unionOf {depth : Nat} : List (WFTy depth) → WFTy depth
  | [] => WFTy.bottom
  | domain :: rest => WFTy.union domain (unionOf rest)

theorem unionOf_le {s : SubtypingContext} {types : List (WFTy s.typeDepth)}
    {upper : WFTy s.typeDepth} (members : ∀ type ∈ types, Subtype s type upper) :
    Subtype s (unionOf types) upper := by
  induction types with
  | nil => exact .botLe
  | cons head rest ih =>
      exact .unionLe (members head List.mem_cons_self)
        (ih (fun type member => members type (List.mem_cons_of_mem _ member)))

theorem le_unionOf {s : SubtypingContext} {types : List (WFTy s.typeDepth)}
    {type : WFTy s.typeDepth} (member : type ∈ types) : Subtype s type (unionOf types) := by
  induction types with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact .leUnionLeft
      · exact (ih member).trans .leUnionRight

abbrev Equations (depth size : Nat) := Fin size → Equation (depth + size) size

def edges {depth size : Nat} (equations : Equations depth size) : Graph.Edges size :=
  fun index => (equations index).references

def reachableDomains {depth size : Nat} (equations : Equations depth size) (index : Fin size) :
    List (WFTy (depth + size)) :=
  (List.finRange size).flatMap fun next =>
    if Graph.Reach (edges equations) index next then (equations next).domains else []

theorem mem_reachableDomains {depth size : Nat} {equations : Equations depth size}
    {index : Fin size} {domain : WFTy (depth + size)} :
    domain ∈ reachableDomains equations index ↔
      ∃ next, Graph.Reach (edges equations) index next ∧ domain ∈ (equations next).domains := by
  simp only [reachableDomains, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_ite_nil_right]

def resolved {depth size : Nat} (equations : Equations depth size) (index : Fin size) :
    WFTy (depth + size) := unionOf (reachableDomains equations index)

def system {depth size : Nat} (equations : Equations depth size) (answer : WFTy depth) :
    RecursiveSystem depth size := ⟨resolved equations, fun _ => answer.weakenBy size⟩

theorem resolved_le {size : Nat} {s : SubtypingContext}
    (equations : Equations s.typeDepth size) (answer : WFTy s.typeDepth) (index : Fin size) :
    Subtype ((system equations answer).openContext s) (resolved equations index)
      ((equations index).consumer (resolved equations)) := by
  refine unionOf_le (fun domain membership => ?_)
  rcases mem_reachableDomains.mp membership with ⟨next, reach, member⟩
  rcases reach.head with rfl | ⟨first, edge, tail⟩
  · exact Equation.domain_le_consumer (s := (system equations answer).openContext s)
      (equations index) (resolved equations) member
  · exact (le_unionOf (mem_reachableDomains.mpr ⟨next, tail, member⟩)).trans
      (Equation.reference_le_consumer (s := (system equations answer).openContext s)
        (equations index) (resolved equations) edge)

theorem le_resolved {size : Nat} {s : SubtypingContext}
    (equations : Equations s.typeDepth size) (answer : WFTy s.typeDepth) (index : Fin size) :
    Subtype ((system equations answer).openContext s)
      ((equations index).consumer (resolved equations)) (resolved equations index) := by
  refine Equation.consumer_le (s := (system equations answer).openContext s)
    (equations index) (resolved equations) _ ?_ ?_
  · exact fun domain member => le_unionOf
      (mem_reachableDomains.mpr ⟨index, .refl index, member⟩)
  · intro next edge
    refine unionOf_le (fun domain membership => ?_)
    rcases mem_reachableDomains.mp membership with ⟨last, tail, member⟩
    exact le_unionOf
      (mem_reachableDomains.mpr ⟨last, (Graph.Reach.edge edge).trans tail, member⟩)

/-- The generated scope supplies the package representation of every member. -/
def package {size : Nat} (s : SubtypingContext)
    (equations : Equations s.typeDepth size) (answer : WFTy s.typeDepth) (index : Fin size) :
    Coercion.PackageWitness ((system equations answer).openContext s) (answer.weakenBy size)
      ((system equations answer).name index) :=
  ⟨resolved equations index, (system equations answer).unfold s index,
    (system equations answer).fold s index⟩

theorem unfold {size : Nat} (s : SubtypingContext)
    (equations : Equations s.typeDepth size) (answer : WFTy s.typeDepth) (index : Fin size) :
    Subtype ((system equations answer).openContext s) ((system equations answer).name index)
      ((equations index).denote (system equations answer).name (answer.weakenBy size)) :=
  ((system equations answer).unfold s index).trans
    ((Subtype.arrow (le_resolved equations answer index) .refl).trans
      ((equations index).witness (package s equations answer)).fold)

theorem fold {size : Nat} (s : SubtypingContext)
    (equations : Equations s.typeDepth size) (answer : WFTy s.typeDepth) (index : Fin size) :
    Subtype ((system equations answer).openContext s)
      ((equations index).denote (system equations answer).name (answer.weakenBy size))
      ((system equations answer).name index) :=
  ((equations index).witness (package s equations answer)).unfold.trans
    ((Subtype.arrow (resolved_le equations answer index) .refl).trans
      ((system equations answer).fold s index))

/-- Export the input equations, without exposing the graph normalization to clients. -/
def guards {depth size : Nat} (equations : Equations depth size) (answer : WFTy depth) :
    List (WFConstraint (depth + size)) :=
  List.ofFn (fun index => WFConstraint.constr ((system equations answer).name index)
    ((equations index).denote (system equations answer).name (answer.weakenBy size))) ++
  List.ofFn (fun index => WFConstraint.constr
    ((equations index).denote (system equations answer).name (answer.weakenBy size))
    ((system equations answer).name index))

theorem guards_valid {size : Nat} (s : SubtypingContext)
    (equations : Equations s.typeDepth size) (answer : WFTy s.typeDepth)
    (guard : WFConstraint (s.typeDepth + size)) (member : guard ∈ guards equations answer) :
    Subtype ((system equations answer).openContext s) guard.sub guard.sup := by
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_ofFn.mp member with ⟨index, rfl⟩
    exact unfold s equations answer index
  · rcases List.mem_ofFn.mp member with ⟨index, rfl⟩
    exact fold s equations answer index

def interface {depth size : Nat} (equations : Equations depth size) (answer : WFTy depth)
    (payload : WFTy (depth + size)) : Interface depth :=
  Interface.bindBlock size (Interface.guards (guards equations answer) (.payload payload))

theorem consumerSubtype {size : Nat} (s : SubtypingContext)
    (equations : Equations s.typeDepth size) (answer result : WFTy s.typeDepth)
    (payload : WFTy (s.typeDepth + size)) :
    Subtype ((system equations answer).openContext s)
      (((interface equations answer payload).consumer result).weakenBy size)
      (WFTy.arrow payload (result.weakenBy size)) :=
  RecursivePackage.consumerSubtypeWithGuards (system equations answer) (guards equations answer)
    payload result (guards_valid s equations answer)

/-- Hide all generated witnesses and prove every exported input equation at the constructor. -/
theorem packTyping {size : Nat} {s : SubtypingContext} {context : TypingContext s.typeDepth}
    (equations : Equations s.typeDepth size) (answer result : WFTy s.typeDepth)
    {term : CTMLCore.Syntax.Term} {payload : WFTy (s.typeDepth + size)}
    (typing : Recursive.HasType ((system equations answer).openContext s) (context.bindTypes size)
      (term.liftTy size) payload) :
    Recursive.HasType s context (pack term)
      ((interface equations answer payload).package result) :=
  RecursivePackage.packWithGuardsTyping (system equations answer) (guards equations answer)
    result (guards_valid s equations answer) typing

end CDotFCCT.CTML.RecursiveAliases
