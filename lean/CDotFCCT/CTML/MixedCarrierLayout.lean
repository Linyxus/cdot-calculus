import CDotFCCT.CTML.MixedCarrierBounds

/-!
# Existing carrier layouts in the mixed target judgment

The source compiler retains its existing carrier syntax and allocation. Every
generated label is reflective under `carrierPolicy`, so alias-bound extraction
requires no additional premise from the source derivation or compiler client.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierLayout

open CTMLCore CTMLCore.Syntax

export Transparent.CarrierLayout
  (code code_injective name name_injective names name_present slot slot_congr
    distinctSides components components_at precise components_eq_slot precise_eq_slot)

universe u
variable {Label : Type u} [DecidableEq Label]

theorem precise_bounds {s : SubtypingContext} {support : List Label} {label : Label}
    (present : label ∈ support) {left right : Label → WFTy s.typeDepth}
    (included : InvertingSubtype carrierPolicy s (precise support left) (precise support right)) :
    InvertingSubtype carrierPolicy s (left label) (right label) ∧
      InvertingSubtype carrierPolicy s (right label) (left label) := by
  have atSlot := (precise_eq_slot present left) ▸
    (precise_eq_slot present right) ▸ included
  exact ⟨memberUpperBound (slot support label present) (carrierPolicy_names support)
      (.native .refl) atSlot,
    memberLowerBound (slot support label present) (carrierPolicy_names support)
      (.native .refl) atSlot⟩

theorem precise_symmetric {s : SubtypingContext} {support : List Label}
    {left right : Label → WFTy s.typeDepth}
    (included : InvertingSubtype carrierPolicy s (precise support left) (precise support right)) :
    InvertingSubtype carrierPolicy s (precise support right) (precise support left) := by
  refine InvertingSubtype.rowMono (names support) (fun field member => ?_)
  obtain ⟨label, present, found⟩ := List.mem_flatMap.mp member
  rcases List.mem_cons.mp found with rfl | found
  · simpa only [components_at present present, Bool.false_eq_true, ite_false] using
      (precise_bounds present included).1.neg
  · obtain rfl := List.mem_singleton.mp found
    simpa only [components_at present present, ite_true] using
      (precise_bounds present included).2

end CDotFCCT.CTML.Mixed.CarrierLayout
