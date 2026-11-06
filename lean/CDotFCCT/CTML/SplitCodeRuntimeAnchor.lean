import CDotFCCT.CTML.ComplementedProduct
import CDotFCCT.CTML.MixedCarrierPackages
import CDotFCCT.CTML.MixedInterfaceWeakening

/-!
# Complemented codes and unrestricted runtime identity

Source membership uses an optional product of code witnesses only. A separate
full identity anchor retains those witnesses together with the arbitrary runtime
payload type. Its paired union row is used only to identify two openings of an
existing anchor, never to encode a source relational upper bound.

Only the member and child codes receive complement guards. No complement guard
is imposed on the runtime payload. The ghost policy is a parameter: using the
optional-product semantic characterization additionally requires its structural
code labels to be designated ghost labels. This module adds no label policy or
typing rule and does not infer a runtime anchor from source-code membership.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.SplitCodeRuntimeAnchor

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation
open CarrierLayout

variable {ghost : FieldName → Bool}

inductive Slot where
  | payload | member | child
  deriving DecidableEq

def support : List Slot := [.payload, .member, .child]

def components {depth : Nat} (data member child : WFTy depth) : Slot → WFTy depth
  | .payload => data
  | .member => member
  | .child => child

def identityRow {depth : Nat} (data member child : WFTy depth) : WFTy depth :=
  precise support (components data member child)

def code {depth : Nat} (member child : WFTy depth) : WFTy depth :=
  OptionalProduct.productTy member child

def body {depth : Nat} (data member child view anchor : WFTy depth) : Interface depth :=
  .guard (ComplementedProduct.complementGuard member)
    (.guard (ComplementedProduct.complementGuard child)
      (.guard (WFConstraint.constr (code member child) view)
        (.guard (WFConstraint.constr (identityRow data member child) anchor) (.payload data))))

private def bindChild {depth : Nat} (data member view anchor : WFTy depth) : Interface depth :=
  .bind (body data.weaken member.weaken (WFTy.var 0 (by omega)) view.weaken anchor.weaken)

private def bindMember {depth : Nat} (data view anchor : WFTy depth) : Interface depth :=
  .bind (bindChild data.weaken (WFTy.var 0 (by omega)) view.weaken anchor.weaken)

def interface {depth : Nat} (view anchor : WFTy depth) : Interface depth :=
  .bind (bindMember (WFTy.var 0 (by omega)) view.weaken anchor.weaken)

private theorem identityRow_substAt {depth : Nat} (data member child : WFTy (depth + 1))
    (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (identityRow data member child).substAt index valid replacement =
      identityRow (data.substAt index valid replacement) (member.substAt index valid replacement)
        (child.substAt index valid replacement) := by
  rw [identityRow, precise_substAt]
  apply congrArg (precise support)
  funext component
  cases component <;> rfl

private theorem code_substAt {depth : Nat} (member child : WFTy (depth + 1))
    (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (code member child).substAt index valid replacement =
      code (member.substAt index valid replacement) (child.substAt index valid replacement) := by
  simp only [code, OptionalProduct.productTy, OptionalProduct.optionalTy,
    WFTy.intersection, WFTy.union, WFTy.substAt_joint, WFTy.substAt_record]
  rfl

private theorem constraint_substAt {depth : Nat} (sub sup : WFTy (depth + 1))
    (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (WFConstraint.constr sub sup).substAt index valid replacement =
      WFConstraint.constr (sub.substAt index valid replacement)
        (sup.substAt index valid replacement) := rfl

private theorem complement_substAt {depth : Nat} (type : WFTy (depth + 1))
    (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (ComplementedProduct.complementGuard type).substAt index valid replacement =
      ComplementedProduct.complementGuard (type.substAt index valid replacement) := rfl

private theorem body_substAt {depth : Nat} (data member child view anchor : WFTy (depth + 1))
    (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (body data member child view anchor).substAt index valid replacement =
      body (data.substAt index valid replacement) (member.substAt index valid replacement)
        (child.substAt index valid replacement) (view.substAt index valid replacement)
        (anchor.substAt index valid replacement) := by
  simp only [body, Interface.substAt, constraint_substAt, complement_substAt,
    identityRow_substAt, code_substAt]

private theorem fresh_substAt {depth : Nat} (index : Nat) (valid : index ≤ depth)
    (replacement : WFTy depth) :
    (WFTy.var 0 (by omega) : WFTy (depth + 1 + 1)).substAt (index + 1)
        (by omega) replacement.weaken = (WFTy.var 0 (by omega) : WFTy (depth + 1)) := by
  apply WFTy.eq_of_raw_eq
  simp [WFTy.substAt, WFTy.var, Ty.substAt, Ty.substWith]

private theorem bindChild_substAt {depth : Nat} (data member view anchor : WFTy (depth + 1))
    (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (bindChild data member view anchor).substAt index valid replacement =
      bindChild (data.substAt index valid replacement) (member.substAt index valid replacement)
        (view.substAt index valid replacement) (anchor.substAt index valid replacement) := by
  simp only [bindChild, Interface.substAt, body_substAt]
  rw [WFTy.substAt_weaken, WFTy.substAt_weaken, fresh_substAt index valid,
    WFTy.substAt_weaken, WFTy.substAt_weaken]

private theorem bindMember_substAt {depth : Nat} (data view anchor : WFTy (depth + 1))
    (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (bindMember data view anchor).substAt index valid replacement =
      bindMember (data.substAt index valid replacement) (view.substAt index valid replacement)
        (anchor.substAt index valid replacement) := by
  simp only [bindMember, Interface.substAt, bindChild_substAt]
  rw [WFTy.substAt_weaken, fresh_substAt index valid,
    WFTy.substAt_weaken, WFTy.substAt_weaken]

/-- The producer supplies code membership and code completeness, plus its existing full anchor. -/
def packingInstance {s : SubtypingContext} (data member child view anchor : WFTy s.typeDepth)
    (memberComplete : InvertingSubtype ghost s WFTy.top (WFTy.union member (WFTy.neg member)))
    (childComplete : InvertingSubtype ghost s WFTy.top (WFTy.union child (WFTy.neg child)))
    (membership : InvertingSubtype ghost s (code member child) view)
    (anchored : InvertingSubtype ghost s (identityRow data member child) anchor) :
    InterfaceInstance ghost s (interface view anchor) data := by
  refine .bind data ?_
  simp only [Interface.instantiate, bindMember_substAt]
  change InterfaceInstance ghost s
    (bindMember data (view.weaken.instantiate data) (anchor.weaken.instantiate data)) data
  rw [WFTy.weaken_instantiate_cancel, WFTy.weaken_instantiate_cancel]
  refine .bind member ?_
  simp only [Interface.instantiate, bindChild_substAt]
  change InterfaceInstance ghost s
    (bindChild (data.weaken.instantiate member) member (view.weaken.instantiate member)
      (anchor.weaken.instantiate member)) data
  rw [WFTy.weaken_instantiate_cancel, WFTy.weaken_instantiate_cancel,
    WFTy.weaken_instantiate_cancel]
  refine .bind child ?_
  simp only [Interface.instantiate, body_substAt]
  change InterfaceInstance ghost s
    (body (data.weaken.instantiate child) (member.weaken.instantiate child) child
      (view.weaken.instantiate child) (anchor.weaken.instantiate child)) data
  rw [WFTy.weaken_instantiate_cancel, WFTy.weaken_instantiate_cancel,
    WFTy.weaken_instantiate_cancel, WFTy.weaken_instantiate_cancel]
  exact .guard memberComplete (.guard childComplete (.guard membership (.guard anchored
    (.payload data))))

/-- A known producer generates the full identity anchor by reflexivity, for arbitrary `D`. -/
theorem packTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {term : Term} {data member child view answer : WFTy s.typeDepth}
    (typing : HasType ghost s context term data)
    (memberComplete : InvertingSubtype ghost s WFTy.top (WFTy.union member (WFTy.neg member)))
    (childComplete : InvertingSubtype ghost s WFTy.top (WFTy.union child (WFTy.neg child)))
    (membership : InvertingSubtype ghost s (code member child) view) :
    HasType ghost s context (pack term)
      ((interface view (identityRow data member child)).package answer) :=
  interfacePackTyping
    (packingInstance data member child view (identityRow data member child)
      memberComplete childComplete membership (.native .refl)) typing

/-- For generated `Top` codes, even the completeness and source-membership proofs are automatic. -/
theorem packTopCodesTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {term : Term} {data answer : WFTy s.typeDepth} (typing : HasType ghost s context term data) :
    HasType ghost s context (pack term)
      ((interface (code WFTy.top WFTy.top) (identityRow data WFTy.top WFTy.top)).package answer) :=
  packTyping typing (.native .leUnionLeft) (.native .leUnionLeft) (.native .refl)

/-- The leaf context records code constraints and full identity separately. -/
def openContext (s : SubtypingContext) (data member child view anchor : WFTy s.typeDepth) :
    SubtypingContext :=
  (((s.assume (ComplementedProduct.complementGuard member)).assume
    (ComplementedProduct.complementGuard child)).assume
      (WFConstraint.constr (code member child) view)).assume
        (WFConstraint.constr (identityRow data member child) anchor)

theorem bodyOpened {s : SubtypingContext} (context : TypingContext s.typeDepth)
    (data member child view anchor : WFTy s.typeDepth) (term : Term) (answer : WFTy s.typeDepth) :
    InterfaceOpened ghost (body data member child view anchor) s.assumptions context term answer ↔
      HasType ghost (openContext s data member child view anchor) (context.bind data) term answer :=
  Iff.rfl

/-- Paired-row inversion is used for identity, with no complement premise on any component. -/
theorem identityBounds {s : SubtypingContext}
    (reflective : ∀ field ∈ names support, ghost field = true)
    {data member child fixedData fixedMember fixedChild : WFTy s.typeDepth}
    (anchored : InvertingSubtype ghost s (identityRow data member child)
      (identityRow fixedData fixedMember fixedChild)) (component : Slot) :
    InvertingSubtype ghost s (components data member child component)
        (components fixedData fixedMember fixedChild component) ∧
      InvertingSubtype ghost s (components fixedData fixedMember fixedChild component)
        (components data member child component) := by
  have present : component ∈ support := by cases component <;> simp [support]
  change InvertingSubtype ghost s (precise support (components data member child))
    (precise support (components fixedData fixedMember fixedChild)) at anchored
  have atSlot := (precise_eq_slot present (components data member child)) ▸
    (precise_eq_slot present (components fixedData fixedMember fixedChild)) ▸ anchored
  exact ⟨memberUpperBound (slot support component present) reflective (.native .refl) atSlot,
    memberLowerBound (slot support component present) reflective (.native .refl) atSlot⟩

/-- A fresh child opening recovers every original witness from the actual exported anchor. -/
theorem openedIdentities (s : SubtypingContext)
    (reflective : ∀ field ∈ names support, ghost field = true)
    (data member child view fixedData fixedMember fixedChild : WFTy s.typeDepth)
    (component : Slot) :
    InvertingSubtype ghost
        (openContext s data member child view (identityRow fixedData fixedMember fixedChild))
        (components data member child component)
        (components fixedData fixedMember fixedChild component) ∧
      InvertingSubtype ghost
        (openContext s data member child view (identityRow fixedData fixedMember fixedChild))
        (components fixedData fixedMember fixedChild component)
        (components data member child component) :=
  identityBounds reflective
    (.native (@Subtype.hyp
      (openContext s data member child view (identityRow fixedData fixedMember fixedChild))
      (WFConstraint.constr (identityRow data member child)
        (identityRow fixedData fixedMember fixedChild)) List.mem_cons_self)) component

/-- The runtime result is transported back to the original unrestricted payload type. -/
theorem openedPayloadTyping (s : SubtypingContext)
    (reflective : ∀ field ∈ names support, ghost field = true)
    (data member child view fixedData fixedMember fixedChild : WFTy s.typeDepth)
    {context : TypingContext s.typeDepth} {term : Term}
    (typing : HasType ghost
      (openContext s data member child view (identityRow fixedData fixedMember fixedChild))
      context term data) :
    HasType ghost
      (openContext s data member child view (identityRow fixedData fixedMember fixedChild))
      context term fixedData :=
  typing.subsumption
    (openedIdentities s reflective data member child view
      fixedData fixedMember fixedChild .payload).1

private theorem nativeCodeMono {s : SubtypingContext}
    {member child fixedMember fixedChild : WFTy s.typeDepth}
    (memberForward : Subtype s member fixedMember)
    (memberBackward : Subtype s fixedMember member)
    (childForward : Subtype s child fixedChild)
    (childBackward : Subtype s fixedChild child) :
    Subtype s (code member child) (code fixedMember fixedChild) :=
  .interMono
    (.interMono (.record (.unionMono .refl (.record memberForward)))
      (.record (.unionMono .refl (.record (.neg memberBackward)))))
    (.interMono (.record (.unionMono .refl (.record childForward)))
      (.record (.unionMono .refl (.record (.neg childBackward)))))

theorem codeMono {s : SubtypingContext}
    {member child fixedMember fixedChild : WFTy s.typeDepth}
    (memberForward : InvertingSubtype ghost s member fixedMember)
    (memberBackward : InvertingSubtype ghost s fixedMember member)
    (childForward : InvertingSubtype ghost s child fixedChild)
    (childBackward : InvertingSubtype ghost s fixedChild child) :
    InvertingSubtype ghost s (code member child) (code fixedMember fixedChild) := by
  let guards := [WFConstraint.constr member fixedMember, WFConstraint.constr fixedMember member,
    WFConstraint.constr child fixedChild, WFConstraint.constr fixedChild child]
  refine .nativeWith guards (nativeCodeMono
    (@Subtype.hyp ⟨s.typeDepth, guards⟩ _ List.mem_cons_self)
    (@Subtype.hyp ⟨s.typeDepth, guards⟩ _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (@Subtype.hyp ⟨s.typeDepth, guards⟩ _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (@Subtype.hyp ⟨s.typeDepth, guards⟩ _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))))) ?_
  intro guard present
  rcases List.mem_cons.mp present with rfl | present
  · exact memberForward
  · rcases List.mem_cons.mp present with rfl | present
    · exact memberBackward
    · rcases List.mem_cons.mp present with rfl | present
      · exact childForward
      · obtain rfl := List.mem_singleton.mp present
        exact childBackward

/-- Code identity and runtime identity are recovered independently from the same full anchor. -/
theorem openedCodeIdentity (s : SubtypingContext)
    (reflective : ∀ field ∈ names support, ghost field = true)
    (data member child view fixedData fixedMember fixedChild : WFTy s.typeDepth) :
    InvertingSubtype ghost
        (openContext s data member child view (identityRow fixedData fixedMember fixedChild))
        (code member child) (code fixedMember fixedChild) ∧
      InvertingSubtype ghost
        (openContext s data member child view (identityRow fixedData fixedMember fixedChild))
        (code fixedMember fixedChild) (code member child) := by
  have members := openedIdentities s reflective data member child view
    fixedData fixedMember fixedChild .member
  have children := openedIdentities s reflective data member child view
    fixedData fixedMember fixedChild .child
  exact ⟨codeMono members.1 members.2 children.1 children.2,
    codeMono members.2 members.1 children.2 children.1⟩

/-- The source-facing code guard does not mention the runtime payload. -/
theorem openedMembership (s : SubtypingContext)
    (data member child view anchor : WFTy s.typeDepth) :
    Subtype (openContext s data member child view anchor) (code member child) view :=
  @Subtype.hyp (openContext s data member child view anchor)
    (WFConstraint.constr (code member child) view)
    (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The same complemented code cannot determine an arbitrary runtime payload identity. -/
theorem noRuntimeIdentityFromCode
    (reflective : ∀ field ∈ names support, ghost field = true) :
    ¬ InvertingSubtype ghost SubtypingContext.empty
      (identityRow WFTy.top WFTy.top WFTy.top)
      (identityRow WFTy.bottom WFTy.top WFTy.top) := by
  intro anchored
  exact Mixed.noCollapse
    (empty_validates ghost (fun _ _ => (fun _ => False, fun _ => False)) 0)
    (identityBounds reflective anchored .payload).1

/-- The package is the ordinary CPS constructor, with one administrative beta reduction. -/
theorem packSteps {value continuation : Term} (isValue : Value continuation) :
    Steps (.app (pack value) continuation) (.app continuation value) := by
  refine .trans (.appBeta _ _ isValue) ?_
  change Steps (.app continuation ((value.lift 1).substAt 0 continuation)) _
  rw [Term.lift_substAt_cancel]
  exact .refl

end CDotFCCT.CTML.Mixed.SplitCodeRuntimeAnchor
