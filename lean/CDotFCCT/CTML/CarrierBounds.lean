import CDotFCCT.CTML.TransparentSafety

/-!
# Shared member bounds from a labelled carrier

A precise carrier uses the same witness in a negative lower slot and a positive
upper slot. Each view may constrain either slot while leaving other components
arbitrary. Row inversion recovers native bounds on that one witness through an
opaque intermediate type. No carrier component needs a runtime inhabitant.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Transparent

open CTMLCore CTMLCore.Syntax

theorem InvertingSubtype.rowMono {s : SubtypingContext} (labels : List FieldName)
    {sub sup : FieldName → WFTy s.typeDepth}
    (included : ∀ field ∈ labels, InvertingSubtype s (sub field) (sup field)) :
    InvertingSubtype s (row labels sub) (row labels sup) := by
  let guards := labels.map (fun field => WFConstraint.constr (sub field) (sup field))
  refine .nativeWith guards
    (row_mono (s := ⟨s.typeDepth, guards⟩) labels (fun field member =>
      @CTMLCore.Subtype.hyp ⟨s.typeDepth, guards⟩ (WFConstraint.constr (sub field) (sup field))
        (List.mem_map.mpr ⟨field, member, rfl⟩))) ?_
  intro guard member
  obtain ⟨field, present, rfl⟩ := List.mem_map.mp member
  exact included field present

structure MemberSlot (labels : List FieldName) where
  lower : FieldName
  upper : FieldName
  different : lower ≠ upper
  lowerPresent : lower ∈ labels
  upperPresent : upper ∈ labels

def MemberSlot.components {depth : Nat} {labels : List FieldName} (slot : MemberSlot labels)
    (lower upper : WFTy depth) (rest : FieldName → WFTy depth) (field : FieldName) : WFTy depth :=
  if field = slot.lower then WFTy.neg lower else if field = slot.upper then upper else rest field

def MemberSlot.view {depth : Nat} {labels : List FieldName} (slot : MemberSlot labels)
    (lower upper : WFTy depth) (rest : FieldName → WFTy depth) : WFTy depth :=
  row labels (slot.components lower upper rest)

/-- Both slots in a precise member mention this witness, regardless of later views. -/
def MemberSlot.precise {depth : Nat} {labels : List FieldName} (slot : MemberSlot labels)
    (witness : WFTy depth) (rest : FieldName → WFTy depth) : WFTy depth :=
  slot.view witness witness rest

theorem MemberSlot.variance {s : SubtypingContext} {labels : List FieldName}
    (slot : MemberSlot labels) {lower₁ lower₂ upper₁ upper₂ : WFTy s.typeDepth}
    {rest₁ rest₂ : FieldName → WFTy s.typeDepth}
    (lower : InvertingSubtype s lower₂ lower₁) (upper : InvertingSubtype s upper₁ upper₂)
    (rest : ∀ field ∈ labels, InvertingSubtype s (rest₁ field) (rest₂ field)) :
    InvertingSubtype s (slot.view lower₁ upper₁ rest₁) (slot.view lower₂ upper₂ rest₂) := by
  refine InvertingSubtype.rowMono labels (fun field member => ?_)
  by_cases atLower : field = slot.lower
  · simpa [components, atLower] using lower.neg
  · by_cases atUpper : field = slot.upper
    · simpa [components, atUpper, Ne.symm slot.different] using upper
    · simpa [components, atLower, atUpper] using rest field member

theorem MemberSlot.lowerBound {s : SubtypingContext} {labels : List FieldName}
    (slot : MemberSlot labels) {witness carrier lower upper : WFTy s.typeDepth}
    {preciseRest viewRest : FieldName → WFTy s.typeDepth}
    (precise : InvertingSubtype s (slot.precise witness preciseRest) carrier)
    (view : InvertingSubtype s carrier (slot.view lower upper viewRest)) :
    InvertingSubtype s lower witness := by
  have component := InvertingSubtype.rowInverse slot.lowerPresent (precise.trans view)
  simp only [components, ite_true] at component
  exact component.negInverse

theorem MemberSlot.upperBound {s : SubtypingContext} {labels : List FieldName}
    (slot : MemberSlot labels) {witness carrier lower upper : WFTy s.typeDepth}
    {preciseRest viewRest : FieldName → WFTy s.typeDepth}
    (precise : InvertingSubtype s (slot.precise witness preciseRest) carrier)
    (view : InvertingSubtype s carrier (slot.view lower upper viewRest)) :
    InvertingSubtype s witness upper := by
  have component := InvertingSubtype.rowInverse slot.upperPresent (precise.trans view)
  simpa [components, Ne.symm slot.different] using component

end CDotFCCT.CTML.Transparent
