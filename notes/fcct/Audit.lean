import FCCT

/-!
Independent checks for the FCCT review. Run from `external/ctml/fcct/lean`:

    lake env lean ../../../../notes/fcct/Audit.lean
-/

namespace FCCT.Review

open Syntax

/-- A stopping condition that distinguishes Bool from arrows. -/
def boolLanding : Landing where
  rel := fun type target => type = WFTy.bool ∧ target = WFTy.bool
  sound := by
    rintro _ _ ⟨rfl, rfl⟩
    exact .refl
  arrowClosed := by
    intro _ _ _ _ _ _ _ h
    exact False.elim (Ty.noConfusion (congrArg WFTy.raw h.1))
  recursiveClosed :=
    ⟨fun h => False.elim (Ty.noConfusion (congrArg WFTy.raw h.1)),
     fun h => False.elim (Ty.noConfusion (congrArg WFTy.raw h.1))⟩

/-- A closed prefix-free subtype of Bool must itself be Bool. -/
theorem prefixFreeBelowBool {type : WFTy 0} (prefixFree : type.PrefixFree)
    (h : Subtype SubtypingContext.empty type WFTy.bool) : type = WFTy.bool := by
  have landing := h.landsAt (landing := boolLanding) ⟨rfl, rfl⟩ trivial
  obtain ⟨raw, hScoped⟩ := type
  cases raw with
  | var index => exact (Nat.not_lt_zero index hScoped).elim
  | bool => rfl
  | arrow _ _ => exact False.elim (Ty.noConfusion (congrArg WFTy.raw landing.1))
  | recArrow _ _ => exact False.elim (Ty.noConfusion (congrArg WFTy.raw landing.1))
  | all _ => exact prefixFree.elim
  | constrained _ _ => exact prefixFree.elim

/-- The paper's impredicative bottom type, `∀α. α`. -/
def bottom : WFTy 0 := WFTy.all (WFTy.var 0 Nat.zero_lt_one)

theorem bottomBelow (type : WFTy 0) : Subtype SubtypingContext.empty bottom type :=
  @Subtype.forallLeft SubtypingContext.empty (WFTy.var 0 Nat.zero_lt_one) type

/-- Lemma C.10(3) cannot preserve every target with one prefix-free replacement. -/
theorem noUniformPrefixFreeReplacement :
    ¬ ∃ type : WFTy 0, type.PrefixFree ∧
      (∀ target : WFTy 0, target.PrefixFree →
        Subtype SubtypingContext.empty bottom target →
        Subtype SubtypingContext.empty type target) := by
  rintro ⟨type, prefixFree, allTargets⟩
  have isBool := prefixFreeBelowBool prefixFree (allTargets WFTy.bool trivial (bottomBelow _))
  exact Subtype.bool_not_le_arrow
    (isBool ▸ allTargets (WFTy.arrow WFTy.bool WFTy.bool) trivial (bottomBelow _))

end FCCT.Review

#print axioms FCCT.Subtype.lands
#print axioms FCCT.Subtype.arrowInversion
#print axioms FCCT.Subtype.guardOfPrefixFreeSupertype
#print axioms FCCT.Subtype.instantiationOfPrefixFreeSupertype
#print axioms FCCT.HasType.substAt
#print axioms FCCT.HasType.substTypeAt
#print axioms FCCT.HasType.simplify
#print axioms FCCT.HasType.progress
#print axioms FCCT.HasType.preservation
#print axioms FCCT.HasType.soundness
#print axioms FCCT.Evaluation.Step.deterministic
#print axioms FCCT.HasType.polyZ
#print axioms FCCT.HasType.unfoldZ
#print axioms FCCT.FixpointExamples.guardedPolymorphicPreservation
#print axioms FCCT.FixpointExamples.terminatingSteps
#print axioms FCCT.FixpointExamples.loopTyping
#print axioms FCCT.FixpointExamples.loopDoesNotTerminate
#print axioms FCCT.Review.noUniformPrefixFreeReplacement
#print axioms FCCT.RecursiveTypeExamples.unfoldSelf
#print axioms FCCT.RecursiveTypeExamples.foldSelf
#print axioms FCCT.RecursiveTypeExamples.omegaTyping
#print axioms FCCT.RecursiveTypeExamples.loopStep
#print axioms FCCT.RecursiveTypeExamples.boolNotSelf
