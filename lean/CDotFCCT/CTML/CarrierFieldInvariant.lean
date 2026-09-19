import CDotFCCT.CTML.MixedCarrierOpening
import CDotFCCT.CTML.CarrierBinding
import CDotFCCT.TermCPS

/-!
# Fixed carrier anchors for ordinary runtime fields

A field package is indexed by the child's precise carrier from the parent's scope.
Its fresh existential witnesses must refine that fixed carrier. Paired positive and
negative carrier slots therefore identify every reopened witness with the existing
one. This is a stronger representation invariant than independently packaged field
views, which `SharedWitnessFusion.noFieldFusion` rules out.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierFieldInvariant

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation
open CarrierLayout

universe u
variable {Label : Type u} [DecidableEq Label]

private theorem arrowParameter {s : SubtypingContext} {sub sup result : WFTy s.typeDepth}
    (included : InvertingSubtype carrierPolicy s sub sup) :
    InvertingSubtype carrierPolicy s (WFTy.arrow sup result) (WFTy.arrow sub result) := by
  refine .nativeWith [WFConstraint.constr sub sup]
    (.arrow (@Subtype.hyp ⟨s.typeDepth, [WFConstraint.constr sub sup]⟩
      (WFConstraint.constr sub sup) List.mem_cons_self) .refl) ?_
  intro guard member
  obtain rfl := List.mem_singleton.mp member
  exact included

/-- Every fresh component remains equal, in subtyping, to the fixed field anchor. -/
theorem anchoredWitnesses {s : SubtypingContext} {support : List Label} {label : Label}
    (present : label ∈ support) {fresh fixed : Label → WFTy s.typeDepth}
    (anchored : InvertingSubtype carrierPolicy s (precise support fresh) (precise support fixed)) :
    InvertingSubtype carrierPolicy s (fresh label) (fixed label) ∧
      InvertingSubtype carrierPolicy s (fixed label) (fresh label) :=
  precise_bounds present anchored

set_option backward.isDefEq.respectTransparency false in
/-- A consumer of the fixed payload also consumes every fresh opening of its anchor. -/
theorem telescopeConsumerStable (support : List Label) (payload : Label)
    (present : payload ∈ support) (remaining : List Label) {s : SubtypingContext}
    (fresh fixed : Label → WFTy s.typeDepth) (answer : WFTy s.typeDepth) :
    InvertingSubtype carrierPolicy s (WFTy.arrow (fixed payload) answer)
      ((telescope support payload remaining fresh (precise support fixed)).consumer answer) := by
  induction remaining generalizing s with
  | nil =>
      let guard := WFConstraint.constr (precise support fresh) (precise support fixed)
      refine .trans (.native (.constrainedRight guard _)) (.constrainedCovariant guard ?_)
      exact arrowParameter (anchoredWitnesses present
        (.native (@Subtype.hyp (s.assume guard) guard List.mem_cons_self))).1
  | cons label rest ih =>
      refine .trans (.native .forallRight) (.forallCovariant ?_)
      simpa only [telescope, Interface.consumer, WFTy.weaken, WFTy.liftAt_arrow,
        Transparent.CarrierLayout.precise_liftAt] using
          ih (s := s.bindType) (bindComponent fresh label) (fun item => (fixed item).weaken)
            answer.weaken

def anchoredInterface {depth : Nat} (support : List Label) (payload : Label)
    (fixed : Label → WFTy depth) : Interface depth :=
  interface support payload (precise support fixed)

/-- Opening needs no independently chosen path witnesses: the ordinary continuation suffices. -/
theorem anchoredConsumerSubtype (support : List Label) (payload : Label)
    (present : payload ∈ support) {s : SubtypingContext}
    (fixed : Label → WFTy s.typeDepth) (answer : WFTy s.typeDepth) :
    InvertingSubtype carrierPolicy s (WFTy.arrow (fixed payload) answer)
      ((anchoredInterface support payload fixed).consumer answer) :=
  telescopeConsumerStable support payload present support (fun _ => WFTy.top) fixed answer

/-- An anchored existential computation can return the original fixed payload type directly. -/
theorem anchoredPackageSubtype (support : List Label) (payload : Label)
    (present : payload ∈ support) {s : SubtypingContext}
    (fixed : Label → WFTy s.typeDepth) (answer : WFTy s.typeDepth) :
    InvertingSubtype carrierPolicy s ((anchoredInterface support payload fixed).package answer)
      (WFTy.arrow (WFTy.arrow (fixed payload) answer) answer) :=
  arrowParameter (anchoredConsumerSubtype support payload present fixed answer)

def objectPayload {depth : Nat} (support : List Label) (payload : Label)
    (fixed : Label → WFTy depth) (field : FieldName) (answer : WFTy depth) : WFTy depth :=
  WFTy.arrow (WFTy.cls "$Unit")
    (WFTy.record field ((anchoredInterface support payload fixed).package answer))

/-- The exact Z-based runtime object for a field aliasing an already scoped source variable. -/
def aliasObject (field : FieldName) (index : Nat) : Term :=
  .fix (.abs (.abs (.record "DOT" (.cons field (pack (.var (index + 2))) .nil (by simp)))))

/-- The generated object is literally the runtime compiler's output for a source field alias. -/
theorem aliasObject_runtime [CDot.Signature] (env : TermCPS.Env)
    (tag : CDot.Path) (tagLabel : CDot.Signature.TypLabel) (body : CDot.Typ)
    (field : CDot.Signature.TrmLabel) (child : CDot.Var) :
    TermCPS.value env (.new tag tagLabel body (.cons .nil (.trm field (.path (.var child))))) =
      some (aliasObject (env.fieldName field) (env.free child)) := by
  rfl

/-- The producer generates the field anchor with its actual child witnesses and reflexivity. -/
theorem aliasObjectTyping (support : List Label) (payload : Label)
    (present : payload ∈ support) {s : SubtypingContext} {context : TypingContext s.typeDepth}
    (fixed : Label → WFTy s.typeDepth) (field : FieldName) (answer : WFTy s.typeDepth)
    {index : Nat} (lookup : context.Lookup index (fixed payload)) :
    HasType carrierPolicy s context (aliasObject field index)
      (objectPayload support payload fixed field answer) :=
  .fixpoint (.abstraction (.abstraction
    ((HasType.record (.cons
      (interfacePackVariableTyping
        (packingInstance support payload present fixed (precise support fixed) (.native .refl))
        (.there (.there lookup))) .nil)).subsumption (.native .interRight))))

/-- One path step forces the object and invokes the selected suspended field. -/
def fieldCall (parent : Term) (field : FieldName) (continuation : Term) : Term :=
  .app (.proj (.app parent (.record "$Unit" .nil)) field) continuation

/-- This works for an arbitrary already-translated parent path, not just a root variable.
The continuation receives the fixed payload, without opening a new independent path identity. -/
theorem fieldCallTyping (support : List Label) (payload : Label)
    (present : payload ∈ support) {s : SubtypingContext} {context : TypingContext s.typeDepth}
    (fixed : Label → WFTy s.typeDepth) (field : FieldName) (answer : WFTy s.typeDepth)
    {parent continuation : Term}
    (parentTyping : HasType carrierPolicy s context parent
      (objectPayload support payload fixed field answer))
    (continuationTyping : HasType carrierPolicy s context continuation
      (WFTy.arrow (fixed payload) answer)) :
    HasType carrierPolicy s context (fieldCall parent field continuation) answer :=
  .application ((HasType.projection
    (.application parentTyping (.native (.record .nil)))).subsumption
      (anchoredPackageSubtype support payload present fixed answer)) continuationTyping

/-- A source field alias supplies the invariant, rather than assuming a field-result inequality. -/
theorem aliasFieldCallTyping (support : List Label) (payload : Label)
    (present : payload ∈ support) {s : SubtypingContext} {context : TypingContext s.typeDepth}
    (fixed : Label → WFTy s.typeDepth) (field : FieldName) (answer : WFTy s.typeDepth)
    {index : Nat} (lookup : context.Lookup index (fixed payload)) {continuation : Term}
    (continuationTyping : HasType carrierPolicy s context continuation
      (WFTy.arrow (fixed payload) answer)) :
    HasType carrierPolicy s context
      (fieldCall (aliasObject field index) field continuation) answer :=
  fieldCallTyping support payload present fixed field answer
    (aliasObjectTyping support payload present fixed field answer lookup) continuationTyping

/-- A recursive child carrier cannot itself be stored beneath only a reflective ghost label. -/
theorem wholeChildCycleNotGuarded (index : Nat) :
    ¬ GuardedAt carrierPolicy 0 (.record (code index true) (.var 0)) := by
  simp only [GuardedAt, carrierPolicy_code, ↓reduceIte, ne_eq, not_true_eq_false,
    not_false_eq_true]

end CDotFCCT.CTML.Mixed.CarrierFieldInvariant
