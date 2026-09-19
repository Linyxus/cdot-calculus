import CDotFCCT.CTML.MixedTypeWeakening

/-!
# Type substitution for mixed subtyping

Removing a type name and substituting a well-scoped replacement preserves mixed
subtyping. Substitution changes payload types and constraint scopes while leaving
the fixed ghost-label policy unchanged, including in single-field and row inversion.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax

variable {ghost : FieldName → Bool}

private theorem InvertingSubtype.castSubstitutionContext
    {source target : SubtypingContext} (equal : source = target)
    {sub sup : WFTy source.typeDepth} (targetSub targetSup : WFTy target.typeDepth)
    (subs : sub.raw = targetSub.raw) (sups : sup.raw = targetSup.raw)
    (h : InvertingSubtype ghost source sub sup) :
    InvertingSubtype ghost target targetSub targetSup := by
  cases equal
  exact (WFTy.eq_of_raw_eq subs) ▸ (WFTy.eq_of_raw_eq sups) ▸ h

theorem row_substAtDepth {depth : Nat} (labels : List FieldName)
    (types : FieldName → WFTy depth) (index : Nat) (valid : index < depth)
    (replacement : WFTy (depth - 1)) :
    (row labels types).substAtDepth index valid replacement =
      row labels (fun field => (types field).substAtDepth index valid replacement) := by
  induction labels with
  | nil => exact WFTy.substAtDepth_extremum valid _ replacement
  | cons field rest ih =>
      simp only [row, Transparent.row, WFTy.union, WFTy.substAtDepth_joint,
        WFTy.substAtDepth_record] at *
      exact congrArg
        (WFTy.joint .union (WFTy.record field ((types field).substAtDepth index valid replacement)))
        ih

/-- Type substitution at any valid de Bruijn position preserves the same mixed rules. -/
theorem InvertingSubtype.substTypeAt {context : SubtypingContext}
    {sub sup : WFTy context.typeDepth} (h : InvertingSubtype ghost context sub sup)
    (index : Nat) (valid : index < context.typeDepth)
    (replacement : WFTy (context.typeDepth - 1)) :
    InvertingSubtype ghost (context.substAt index valid replacement)
      (sub.substAtDepth index valid replacement) (sup.substAtDepth index valid replacement) := by
  induction h generalizing index with
  | native h => exact .native (h.substTypeAt index valid replacement)
  | nativeWith guards h evidence ih =>
      refine .nativeWith _ (h.substTypeAt index valid replacement) ?_
      intro guard member
      obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
      dsimp only [SubtypingContext.substAt]
      rw [WFConstraint.substAtDepth_sub, WFConstraint.substAtDepth_sup]
      exact ih old present index valid replacement
  | trans _ _ first second =>
      exact .trans (first index valid replacement) (second index valid replacement)
  | inverse marked _ ih =>
      have substituted := ih index valid replacement
      simp only [WFTy.substAtDepth_record] at substituted
      exact .inverse marked substituted
  | rowInverse reflective member _ ih =>
      have substituted := ih index valid replacement
      rw [row_substAtDepth, row_substAtDepth] at substituted
      exact .rowInverse reflective member substituted
  | cut guard _ _ inferred body =>
      refine .cut (guard.substAtDepth index valid replacement) ?_ ?_
      · dsimp only [SubtypingContext.substAt]
        rw [WFConstraint.substAtDepth_sub, WFConstraint.substAtDepth_sup]
        exact inferred index valid replacement
      · exact InvertingSubtype.castSubstitutionContext
          (SubtypingContext.substAt_assume_comm _ index valid replacement guard)
          _ _ rfl rfl (body index valid replacement)
  | forallCovariant _ ih =>
      rename_i source sub sup bodyProof
      let underReplacement : WFTy (source.bindType.typeDepth - 1) :=
        replacement.weaken.castDepth (by rw [SubtypingContext.bindType_typeDepth]; omega)
      have underValid : index + 1 < source.bindType.typeDepth := by
        rw [SubtypingContext.bindType_typeDepth]
        omega
      let underSub : WFTy ((source.substAt index valid replacement).bindType.typeDepth) :=
        (sub.substAtDepth (index + 1) underValid underReplacement).castDepth (by
          simp only [SubtypingContext.bindType_typeDepth, SubtypingContext.substAt]
          omega)
      let underSup : WFTy ((source.substAt index valid replacement).bindType.typeDepth) :=
        (sup.substAtDepth (index + 1) underValid underReplacement).castDepth (by
          simp only [SubtypingContext.bindType_typeDepth, SubtypingContext.substAt]
          omega)
      have premise : InvertingSubtype ghost
          (source.substAt index valid replacement).bindType underSub underSup :=
        InvertingSubtype.castSubstitutionContext
          (SubtypingContext.substAt_bindType_comm source index valid replacement)
          underSub underSup (WFTy.raw_castDepth _ _).symm (WFTy.raw_castDepth _ _).symm
          (ih (index + 1) underValid underReplacement)
      exact InvertingSubtype.castSubstitutionContext rfl _ _
        (WFTy.raw_all_substAtDepth sub index valid replacement)
        (WFTy.raw_all_substAtDepth sup index valid replacement) (.forallCovariant premise)
  | constrainedCovariant guard _ ih =>
      rename_i source sub sup bodyProof
      simp only [WFTy.substAtDepth_constrained]
      refine .constrainedCovariant (s := source.substAt index valid replacement)
        (guard.substAtDepth index valid replacement) ?_
      exact InvertingSubtype.castSubstitutionContext
        (SubtypingContext.substAt_assume_comm source index valid replacement guard)
        _ _ rfl rfl (ih index valid replacement)

/-- Front substitution also transforms every constraint on the removed type name. -/
theorem InvertingSubtype.substitute {depth : Nat}
    {guards : List (WFConstraint (depth + 1))} {sub sup : WFTy (depth + 1)}
    (h : InvertingSubtype ghost ⟨depth + 1, guards⟩ sub sup) (replacement : WFTy depth) :
    InvertingSubtype ghost
      ⟨depth, guards.map (fun guard => guard.instantiate replacement)⟩
      (sub.instantiate replacement) (sup.instantiate replacement) :=
  h.substTypeAt 0 (Nat.succ_pos depth) replacement

private theorem substAt_bindType_zero (context : SubtypingContext)
    (replacement : WFTy context.typeDepth) :
    context.bindType.substAt 0 (Nat.succ_pos context.typeDepth) replacement = context := by
  obtain ⟨depth, assumptions⟩ := context
  apply congrArg (SubtypingContext.mk depth)
  change (assumptions.map WFConstraint.weaken).map
    (fun guard => guard.substAtDepth 0 (Nat.succ_pos depth) replacement) = assumptions
  induction assumptions with
  | nil => rfl
  | cons guard rest ih =>
      simp only [List.map_cons, ih]
      exact congrArg (· :: rest)
        (WFConstraint.eq_of_raw_eq
          (Constraint.lift_substAt_zero_cancel guard.raw replacement.raw))

/-- Instantiating a derivation under a fresh name returns to its original context. -/
theorem InvertingSubtype.instantiate {context : SubtypingContext}
    {sub sup : WFTy (context.typeDepth + 1)}
    (h : InvertingSubtype ghost context.bindType sub sup)
    (replacement : WFTy context.typeDepth) :
    InvertingSubtype ghost context (sub.instantiate replacement) (sup.instantiate replacement) :=
  InvertingSubtype.castSubstitutionContext (substAt_bindType_zero context replacement)
    _ _ rfl rfl (h.substTypeAt 0 (Nat.succ_pos context.typeDepth) replacement)

end CDotFCCT.CTML.Mixed
