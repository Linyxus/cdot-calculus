import CDotFCCT.CTML.MixedCarrierLayout
import CDotFCCT.CTML.CarrierPackages
import CDotFCCT.CTML.MixedInterfaces

/-!
# Shared carrier packages in the record-guarded target

The interface, witness telescope and binding algebra are the existing pure syntax.
Only the proof certificates change: each bound and consumer uses the mixed target
with one fixed label policy. Packing still generates all witnesses from the carrier.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierLayout

open CTMLCore CTMLCore.Syntax

export Transparent.CarrierLayout (bindComponent telescope interface components_substAt
  precise_substAt bindComponent_substAt telescope_substAt bindComponent_instantiate
  telescope_instantiateCurrent components_congr precise_congr telescope_congr telescopeMap)

universe u
variable {Label : Type u} [DecidableEq Label] {ghost : FieldName → Bool}

/-- Every telescope binder is discharged with the corresponding producer witness. -/
def telescopeInstance {s : SubtypingContext} (support : List Label) (payload : Label)
    (remaining : List Label) (types : Label → WFTy s.typeDepth) (view : WFTy s.typeDepth)
    (included : InvertingSubtype ghost s (precise support types) view) :
    InterfaceInstance ghost s (telescope support payload remaining types view) (types payload) := by
  induction remaining with
  | nil => exact .guard included (.payload _)
  | cons label rest ih =>
      refine .bind (types label) ?_
      rw [telescope_instantiateCurrent]
      exact ih


/-- Packing automatically chooses all member and payload witnesses from the precise carrier. -/
def packingInstance {s : SubtypingContext} (support : List Label) (payload : Label)
    (present : payload ∈ support) (types : Label → WFTy s.typeDepth)
    (view : WFTy s.typeDepth) (included : InvertingSubtype ghost s (precise support types) view) :
    InterfaceInstance ghost s (interface support payload view) (types payload) := by
  have equal : interface support payload view = telescope support payload support types view :=
    telescope_congr support payload support view (fun label used absent =>
      False.elim (absent (used.elim id (fun same => same ▸ present))))
  rw [equal]
  exact telescopeInstance support payload support types view included


/-- Any proved bound on views lifts to a bound on complete existential packages. -/
theorem packageSubtype {s : SubtypingContext} (support : List Label) (payload : Label)
    {sub sup : WFTy s.typeDepth} (included : InvertingSubtype ghost s sub sup)
    (answer : WFTy s.typeDepth) :
    InvertingSubtype ghost s ((interface support payload sub).package answer)
      ((interface support payload sup).package answer) := by
  refine .nativeWith [WFConstraint.constr sub sup]
    ((telescopeMap support payload support (fun _ => WFTy.top)
      (@CTMLCore.Subtype.hyp ⟨s.typeDepth, [WFConstraint.constr sub sup]⟩
        (WFConstraint.constr sub sup) List.mem_cons_self)).packageSubtype answer) ?_
  intro guard present
  obtain rfl := List.mem_singleton.mp present
  exact included

end CDotFCCT.CTML.Mixed.CarrierLayout
