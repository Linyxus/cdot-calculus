import CDotFCCT.CTML.MixedInversion
import CDotFCCT.CTML.CarrierLayout

/-!
# Shared member bounds from a labelled carrier

A precise carrier uses the same witness in a negative lower slot and a positive
upper slot. Each view may constrain either slot while leaving other components
arbitrary. Row inversion recovers native bounds on that one witness through an
opaque intermediate type. No carrier component needs a runtime inhabitant.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax

variable {ghost : FieldName → Bool}

universe u

/-- CarrierLayout reserves strings made only of `m`; runtime labels use a separate namespace. -/
def carrierPolicy (field : FieldName) : Bool := field.toList.all (fun char => char == 'm')

theorem carrierPolicy_code (index : Nat) (upper : Bool) :
    carrierPolicy (Transparent.CarrierLayout.code index upper) = true := by
  simp [carrierPolicy, Transparent.CarrierLayout.code]

theorem carrierPolicy_names {Label : Type u} [DecidableEq Label] (support : List Label) :
    ∀ field ∈ Transparent.CarrierLayout.names support, carrierPolicy field = true := by
  intro field member
  obtain ⟨label, _, found⟩ := List.mem_flatMap.mp member
  rcases List.mem_cons.mp found with rfl | found
  · exact carrierPolicy_code _ false
  · obtain rfl := List.mem_singleton.mp found
    exact carrierPolicy_code _ true

theorem InvertingSubtype.rowMono {s : SubtypingContext} (labels : List FieldName)
    {sub sup : FieldName → WFTy s.typeDepth}
    (included : ∀ field ∈ labels, InvertingSubtype ghost s (sub field) (sup field)) :
    InvertingSubtype ghost s (row labels sub) (row labels sup) := by
  let guards := labels.map (fun field => WFConstraint.constr (sub field) (sup field))
  refine .nativeWith guards
    (row_mono (s := ⟨s.typeDepth, guards⟩) labels (fun field member =>
      @CTMLCore.Subtype.hyp ⟨s.typeDepth, guards⟩ (WFConstraint.constr (sub field) (sup field))
        (List.mem_map.mpr ⟨field, member, rfl⟩))) ?_
  intro guard member
  obtain ⟨field, present, rfl⟩ := List.mem_map.mp member
  exact included field present

theorem memberVariance {s : SubtypingContext} {labels : List FieldName}
    (slot : Transparent.MemberSlot labels) {lower₁ lower₂ upper₁ upper₂ : WFTy s.typeDepth}
    {rest₁ rest₂ : FieldName → WFTy s.typeDepth}
    (lower : InvertingSubtype ghost s lower₂ lower₁)
    (upper : InvertingSubtype ghost s upper₁ upper₂)
    (rest : ∀ field ∈ labels, InvertingSubtype ghost s (rest₁ field) (rest₂ field)) :
    InvertingSubtype ghost s (slot.view lower₁ upper₁ rest₁) (slot.view lower₂ upper₂ rest₂) := by
  refine InvertingSubtype.rowMono labels (fun field member => ?_)
  by_cases atLower : field = slot.lower
  · simpa [Transparent.MemberSlot.components, atLower] using lower.neg
  · by_cases atUpper : field = slot.upper
    · simpa [Transparent.MemberSlot.components, atUpper, Ne.symm slot.different] using upper
    · simpa [Transparent.MemberSlot.components, atLower, atUpper] using rest field member

theorem memberLowerBound {s : SubtypingContext} {labels : List FieldName}
    (slot : Transparent.MemberSlot labels)
    (reflective : ∀ field ∈ labels, ghost field = true)
    {witness carrier lower upper : WFTy s.typeDepth}
    {preciseRest viewRest : FieldName → WFTy s.typeDepth}
    (precise : InvertingSubtype ghost s (slot.precise witness preciseRest) carrier)
    (view : InvertingSubtype ghost s carrier (slot.view lower upper viewRest)) :
    InvertingSubtype ghost s lower witness := by
  have component := InvertingSubtype.rowInverse reflective slot.lowerPresent (precise.trans view)
  simp only [Transparent.MemberSlot.components, ite_true] at component
  exact component.negInverse

theorem memberUpperBound {s : SubtypingContext} {labels : List FieldName}
    (slot : Transparent.MemberSlot labels)
    (reflective : ∀ field ∈ labels, ghost field = true)
    {witness carrier lower upper : WFTy s.typeDepth}
    {preciseRest viewRest : FieldName → WFTy s.typeDepth}
    (precise : InvertingSubtype ghost s (slot.precise witness preciseRest) carrier)
    (view : InvertingSubtype ghost s carrier (slot.view lower upper viewRest)) :
    InvertingSubtype ghost s witness upper := by
  have component := InvertingSubtype.rowInverse reflective slot.upperPresent (precise.trans view)
  simpa [Transparent.MemberSlot.components, Ne.symm slot.different] using component

end CDotFCCT.CTML.Mixed
