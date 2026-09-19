import CDotFCCT.CTML.MixedRecursion
import CTMLCore.Declarative.RecursiveTypeWeakening

/-!
# Type-variable weakening preserves ordinary record guards

Fresh outer type variables leave the local recursive name untouched. The proof
checks ghost fields recursively and retains ordinary record guards through all
constructors, including arbitrary constraint endpoints and universal binders.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax

variable {ghost : FieldName → Bool}

mutual
  theorem GuardedAt.liftAbove {type : Ty} {index cutoff : Nat}
      (guarded : GuardedAt ghost index type) (above : index < cutoff) (amount : Nat) :
      GuardedAt ghost index (type.liftAt cutoff amount) :=
    match type with
    | .var found => by
        simp only [Ty.liftAt]
        split <;> simp only [GuardedAt] at guarded ⊢ <;> omega
    | .extremum _ | .cls _ | .arrow _ _ => trivial
    | .neg body => GuardedAt.liftAbove (type := body) guarded above amount
    | .joint _ _ _ =>
        ⟨guarded.1.liftAbove above amount, guarded.2.liftAbove above amount⟩
    | .record field payload => by
        cases marked : ghost field with
        | false => simp only [Ty.liftAt, GuardedAt, marked, Bool.false_eq_true, ↓reduceIte]
        | true =>
            have inner : GuardedAt ghost index payload := by
              simpa only [GuardedAt, marked, ↓reduceIte] using guarded
            simpa only [Ty.liftAt, GuardedAt, marked, ↓reduceIte] using
              GuardedAt.liftAbove inner above amount
    | .all body =>
        GuardedAt.liftAbove (type := body) (index := index + 1) (cutoff := cutoff + 1)
          guarded (Nat.succ_lt_succ above) amount
    | .constrained _ _ =>
        ⟨guarded.1.liftAbove above amount, guarded.2.liftAbove above amount⟩

  theorem GuardGuardedAt.liftAbove {guard : Constraint} {index cutoff : Nat}
      (guarded : GuardGuardedAt ghost index guard) (above : index < cutoff) (amount : Nat) :
      GuardGuardedAt ghost index (guard.liftAt cutoff amount) :=
    match guard with
    | .constr _ _ => ⟨guarded.1.liftAbove above amount, guarded.2.liftAbove above amount⟩
end

/-- Shift the outer scope while preserving the local recursive name at index zero. -/
def Definition.liftAt {n : Nat} (definition : Definition ghost n)
    (index : Nat) (valid : index ≤ n) : Definition ghost (n + 1) where
  body := definition.body.liftAt (index + 1) (Nat.add_le_add_right valid 1)
  guarded := definition.guarded.liftAbove (Nat.zero_lt_succ index) 1

theorem Definition.native_liftAt {n : Nat} (definition : Definition ghost n)
    (index : Nat) (valid : index ≤ n) :
    (definition.liftAt index valid).native = definition.native.liftAt index valid := rfl

theorem Definition.openContext_liftAt (s : SubtypingContext)
    (definition : Definition ghost s.typeDepth) (index : Nat) (valid : index ≤ s.typeDepth) :
    (definition.native.openContext s).insertTypeAt (index + 1) (Nat.add_le_add_right valid 1) =
      (definition.liftAt index valid).native.openContext (s.insertTypeAt index valid) :=
  RecursiveType.openContext_liftAt s definition.native index valid

end CDotFCCT.CTML.Mixed
