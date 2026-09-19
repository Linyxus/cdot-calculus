import CDotFCCT.CTML.CarrierLayout
import CDotFCCT.CTML.TransparentInterfaces
import CDotFCCT.CTML.InterfaceSubtyping

/-!
# Closing carrier witnesses in continuation-encoded packages

One universal telescope hides every component of a precise carrier, including
the runtime payload type. Its sole guard relates that carrier to the requested
view. Instantiation uses the producer's existing witnesses and bound derivation.
The telescope does not add term constructors or a representation of type members.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Transparent.CarrierLayout

open CTMLCore CTMLCore.Syntax

universe u
variable {Label : Type u} [DecidableEq Label]

theorem components_substAt {depth : Nat} (support entries : List Label)
    (types : Label → WFTy (depth + 1)) (field : FieldName)
    (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (components support entries types field).substAt index valid replacement =
      components support entries (fun label => (types label).substAt index valid replacement)
        field := by
  induction entries with
  | nil => rfl
  | cons first rest ih =>
      simp only [components]
      split
      · rfl
      · split
        · rfl
        · exact ih

theorem precise_substAt {depth : Nat} (support : List Label)
    (types : Label → WFTy (depth + 1)) (index : Nat) (valid : index ≤ depth)
    (replacement : WFTy depth) :
    (precise support types).substAt index valid replacement =
      precise support (fun label => (types label).substAt index valid replacement) := by
  unfold precise
  have commute (fields : List FieldName) :
      (row fields (components support support types)).substAt index valid replacement =
        row fields (components support support
          (fun label => (types label).substAt index valid replacement)) := by
    induction fields with
    | nil => rfl
    | cons first rest ih =>
        simpa only [row, WFTy.union, WFTy.substAt_joint, WFTy.substAt_record,
          components_substAt] using congrArg
            (WFTy.union (WFTy.record first (components support support
              (fun label => (types label).substAt index valid replacement) first))) ih
  exact commute _

/-- Introduce a fresh component name, shifting all previously introduced names. -/
def bindComponent {depth : Nat} (types : Label → WFTy depth) (label : Label) :
    Label → WFTy (depth + 1) :=
  fun selected => if selected = label then WFTy.var 0 (by omega) else (types selected).weaken

theorem bindComponent_substAt {depth : Nat} (types : Label → WFTy (depth + 1))
    (label : Label) (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (fun selected => (bindComponent types label selected).substAt (index + 1)
      (by omega) replacement.weaken) =
      bindComponent (fun selected => (types selected).substAt index valid replacement) label := by
  funext selected
  by_cases same : selected = label
  · simp only [bindComponent, same, ite_true]
    apply WFTy.eq_of_raw_eq
    simp [WFTy.substAt, WFTy.var, Ty.substAt, Ty.substWith]
  · simp only [bindComponent, same, ite_false]
    exact WFTy.substAt_weaken valid (types selected) replacement

/-- Bind components in order; the answer and requested view remain outside their scope. -/
def telescope (support : List Label) (payload : Label) :
    (remaining : List Label) → {depth : Nat} →
      (Label → WFTy depth) → WFTy depth → Interface depth
  | [], _, types, view =>
      .guard (WFConstraint.constr (precise support types) view) (.payload (types payload))
  | label :: rest, _, types, view =>
      .bind (telescope support payload rest (bindComponent types label) view.weaken)

theorem telescope_substAt (support : List Label) (payload : Label) (remaining : List Label)
    {depth : Nat} (types : Label → WFTy (depth + 1)) (view : WFTy (depth + 1))
    (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (telescope support payload remaining types view).substAt index valid replacement =
      telescope support payload remaining
        (fun selected => (types selected).substAt index valid replacement)
        (view.substAt index valid replacement) := by
  induction remaining generalizing depth index with
  | nil =>
      simp only [telescope, Interface.substAt]
      have constraint :
          (WFConstraint.constr (precise support types) view).substAt index valid replacement =
            WFConstraint.constr
              (precise support (fun selected => (types selected).substAt index valid replacement))
              (view.substAt index valid replacement) := by
        exact congrArg (fun sub => WFConstraint.constr sub
          (view.substAt index valid replacement)) (precise_substAt _ _ _ _ _)
      rw [constraint]
  | cons label rest ih =>
      simp only [telescope, Interface.substAt]
      rw [ih, bindComponent_substAt, WFTy.substAt_weaken]

theorem bindComponent_instantiate {depth : Nat} (types : Label → WFTy depth)
    (label : Label) :
    (fun selected => (bindComponent types label selected).instantiate (types label)) = types := by
  funext selected
  by_cases same : selected = label
  · subst selected
    simp only [bindComponent, ite_true]
    rfl
  · simp only [bindComponent, same, ite_false, WFTy.weaken_instantiate_cancel]

theorem telescope_instantiateCurrent (support : List Label) (payload : Label)
    (remaining : List Label) {depth : Nat} (types : Label → WFTy depth)
    (view : WFTy depth) (label : Label) :
    (telescope support payload remaining (bindComponent types label) view.weaken).instantiate
      (types label) = telescope support payload remaining types view :=
  (telescope_substAt support payload remaining (bindComponent types label) view.weaken
    0 (Nat.zero_le depth) (types label)).trans
      (congrArg₂ (telescope support payload remaining)
        (bindComponent_instantiate types label)
        (WFTy.weaken_instantiate_cancel view (types label)))

/-- Every telescope binder is discharged with the corresponding producer witness. -/
def telescopeInstance {s : SubtypingContext} (support : List Label) (payload : Label)
    (remaining : List Label) (types : Label → WFTy s.typeDepth) (view : WFTy s.typeDepth)
    (included : InvertingSubtype s (precise support types) view) :
    InterfaceInstance s (telescope support payload remaining types view) (types payload) := by
  induction remaining with
  | nil => exact .guard included (.payload _)
  | cons label rest ih =>
      refine .bind (types label) ?_
      rw [telescope_instantiateCurrent]
      exact ih

theorem components_congr {depth : Nat} (support entries : List Label)
    {left right : Label → WFTy depth} (equal : ∀ label ∈ entries, left label = right label)
    (field : FieldName) : components support entries left field =
      components support entries right field := by
  induction entries with
  | nil => rfl
  | cons label rest ih =>
      simp only [components]
      split
      · exact congrArg WFTy.neg (equal label List.mem_cons_self)
      · split
        · exact equal label List.mem_cons_self
        · exact ih (fun selected present => equal selected (List.mem_cons_of_mem label present))

theorem precise_congr {depth : Nat} (support : List Label)
    {left right : Label → WFTy depth} (equal : ∀ label ∈ support, left label = right label) :
    precise support left = precise support right :=
  congrArg (row (names support)) (funext (components_congr support support equal))

/-- Initial assignments are irrelevant for all components rebound by the telescope. -/
theorem telescope_congr (support : List Label) (payload : Label) (remaining : List Label)
    {depth : Nat} {left right : Label → WFTy depth} (view : WFTy depth)
    (equal : ∀ label, (label ∈ support ∨ label = payload) → label ∉ remaining →
      left label = right label) :
    telescope support payload remaining left view =
      telescope support payload remaining right view := by
  induction remaining generalizing depth with
  | nil =>
      simp only [telescope]
      rw [precise_congr support (fun label present => equal label (.inl present) (by simp)),
        equal payload (.inr rfl) (by simp)]
  | cons label rest ih =>
      simp only [telescope]
      apply congrArg Interface.bind
      apply ih
      intro selected used absent
      by_cases same : selected = label
      · simp only [bindComponent, same, ite_true]
      · simp only [bindComponent, same, ite_false]
        exact congrArg WFTy.weaken (equal selected used (by simp [same, absent]))

/-- The exported schema depends on the finite label support and requested view only. -/
def interface {depth : Nat} (support : List Label) (payload : Label) (view : WFTy depth) :
    Interface depth := telescope support payload support (fun _ => WFTy.top) view

/-- Packing automatically chooses all member and payload witnesses from the precise carrier. -/
def packingInstance {s : SubtypingContext} (support : List Label) (payload : Label)
    (present : payload ∈ support) (types : Label → WFTy s.typeDepth)
    (view : WFTy s.typeDepth) (included : InvertingSubtype s (precise support types) view) :
    InterfaceInstance s (interface support payload view) (types payload) := by
  have equal : interface support payload view = telescope support payload support types view :=
    telescope_congr support payload support view (fun label used absent =>
      False.elim (absent (used.elim id (fun same => same ▸ present))))
  rw [equal]
  exact telescopeInstance support payload support types view included

/-- Widening a carrier view transports the whole shared-witness interface. -/
theorem telescopeMap (support : List Label) (payload : Label) (remaining : List Label)
    {s : SubtypingContext} (types : Label → WFTy s.typeDepth)
    {sub sup : WFTy s.typeDepth} (included : CTMLCore.Subtype s sub sup) :
    Interface.Map s (telescope support payload remaining types sub)
      (telescope support payload remaining types sup) := by
  induction remaining generalizing s with
  | nil =>
      refine .sourceGuard (.targetGuard ?_ (.payload .refl))
      exact .trans (@CTMLCore.Subtype.hyp
        (s.assume (WFConstraint.constr (precise support types) sub))
        (WFConstraint.constr (precise support types) sub) List.mem_cons_self)
        (included.weakenAssumption _)
  | cons label rest ih => exact .bind (ih (bindComponent types label) included.weakenType)

/-- Any proved bound on views lifts to a bound on complete existential packages. -/
theorem packageSubtype {s : SubtypingContext} (support : List Label) (payload : Label)
    {sub sup : WFTy s.typeDepth} (included : InvertingSubtype s sub sup)
    (answer : WFTy s.typeDepth) :
    InvertingSubtype s ((interface support payload sub).package answer)
      ((interface support payload sup).package answer) := by
  refine .nativeWith [WFConstraint.constr sub sup]
    ((telescopeMap support payload support (fun _ => WFTy.top)
      (@CTMLCore.Subtype.hyp ⟨s.typeDepth, [WFConstraint.constr sub sup]⟩
        (WFConstraint.constr sub sup) List.mem_cons_self)).packageSubtype answer) ?_
  intro guard present
  obtain rfl := List.mem_singleton.mp present
  exact included

end CDotFCCT.CTML.Transparent.CarrierLayout
