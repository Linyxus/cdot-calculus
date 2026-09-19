import CDotFCCT.CTML.TransparentSubtyping
import CDotFCCT.CTML.TransparentRecursion
import CDotFCCT.CTML.TransparentRows
import CTMLCore.Declarative.Lattice

/-!
# Checking record inversion with function-guarded recursion

This experimental subtyping relation closes native Core subtyping under record
inversion. Cut makes an inferred bound available to any native rule; the two binder
rules permit inversion inside universal and constraint abstractions as well.

The model validates the whole relation and the stricter recursive definitions.
In particular, no such definition can cause a closed `Top ≤ Bottom` derivation.
This is a subtyping consistency result, not a typing-safety or DOT translation theorem.
The existing target judgments are unchanged.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Transparent

open CTMLCore CTMLCore.Syntax CTMLCore.Indexed

inductive InvertingSubtype : (s : SubtypingContext) → WFTy s.typeDepth →
    WFTy s.typeDepth → Prop where
  | native {s : SubtypingContext} {sub sup : WFTy s.typeDepth} :
      Subtype s sub sup → InvertingSubtype s sub sup
  | nativeWith {s : SubtypingContext} {sub sup : WFTy s.typeDepth}
      (guards : List (WFConstraint s.typeDepth)) :
      Subtype ⟨s.typeDepth, guards⟩ sub sup →
      (∀ guard ∈ guards, InvertingSubtype s guard.sub guard.sup) →
      InvertingSubtype s sub sup
  | trans {s : SubtypingContext} {sub middle sup : WFTy s.typeDepth} :
      InvertingSubtype s sub middle → InvertingSubtype s middle sup →
      InvertingSubtype s sub sup
  | inverse {s : SubtypingContext} {field : FieldName} {sub sup : WFTy s.typeDepth} :
      InvertingSubtype s (WFTy.record field sub) (WFTy.record field sup) →
      InvertingSubtype s sub sup
  | rowInverse {s : SubtypingContext} {labels : List FieldName}
      {sub sup : FieldName → WFTy s.typeDepth} {field : FieldName} :
      field ∈ labels → InvertingSubtype s (row labels sub) (row labels sup) →
      InvertingSubtype s (sub field) (sup field)
  | cut {s : SubtypingContext} (guard : WFConstraint s.typeDepth)
      {sub sup : WFTy s.typeDepth} :
      InvertingSubtype s guard.sub guard.sup →
      InvertingSubtype (s.assume guard) sub sup → InvertingSubtype s sub sup
  | forallCovariant {s : SubtypingContext} {sub sup : WFTy (s.typeDepth + 1)} :
      InvertingSubtype s.bindType sub sup →
      InvertingSubtype s (WFTy.all sub) (WFTy.all sup)
  | constrainedCovariant {s : SubtypingContext} (guard : WFConstraint s.typeDepth)
      {sub sup : WFTy s.typeDepth} :
      InvertingSubtype (s.assume guard) sub sup →
      InvertingSubtype s (WFTy.constrained guard sub) (WFTy.constrained guard sup)

theorem InvertingSubtype.sound {s : SubtypingContext} {sub sup : WFTy s.typeDepth}
    (typing : InvertingSubtype s sub sup) :
    ∀ env n, Validates s env n →
      Includes (interpret env sub.raw) (interpret env sup.raw) n := by
  induction typing with
  | native typing => exact subtype_sound typing
  | nativeWith guards typing _ ih =>
      exact fun env n valid => subtype_sound typing env n
        (fun guard member => (guard_iff guard env n).mpr (ih guard member env n valid))
  | trans _ _ first second =>
      exact fun env n valid => (first env n valid).trans (second env n valid)
  | inverse _ ih => exact fun env n valid => TransparentRecord.inverse (ih env n valid)
  | rowInverse member _ ih => exact fun env n valid => row_inverse member (ih env n valid)
  | cut guard _ _ inferred body =>
      exact fun env n valid => body env n
        (valid.assume ((guard_iff guard env n).mpr (inferred env n valid)))
  | forallCovariant _ ih =>
      exact fun env n valid k within term =>
        ⟨fun related argument =>
          (ih (env.cons argument) n (valid.bindType argument) k within term).1
            (related argument),
         fun ⟨argument, apart⟩ => ⟨argument,
          (ih (env.cons argument) n (valid.bindType argument) k within term).2 apart⟩⟩
  | constrainedCovariant _ _ ih =>
      exact fun env n valid k within term =>
        ⟨fun related j below holds =>
          (ih env j ((valid.below (Nat.le_trans below within)).assume holds)
            j (Nat.le_refl j) term).1 (related j below holds),
         fun apart => ⟨apart.1,
          (ih env k ((valid.below within).assume apart.1)
            k (Nat.le_refl k) term).2 apart.2⟩⟩

/-- Negation composes with inversion by ordinary native reasoning under a proved bound. -/
theorem InvertingSubtype.neg {s : SubtypingContext} {sub sup : WFTy s.typeDepth}
    (typing : InvertingSubtype s sup sub) :
    InvertingSubtype s (WFTy.neg sub) (WFTy.neg sup) :=
  .cut (WFConstraint.constr sup sub) typing
    (.native (.neg (@Subtype.hyp (s.assume (WFConstraint.constr sup sub))
      (WFConstraint.constr sup sub) List.mem_cons_self)))

theorem InvertingSubtype.negInverse {s : SubtypingContext} {sub sup : WFTy s.typeDepth}
    (typing : InvertingSubtype s (WFTy.neg sup) (WFTy.neg sub)) :
    InvertingSubtype s sub sup :=
  .trans (.native (.negDouble .upper))
    (.trans typing.neg (.native (.negDouble .lower)))

theorem Definition.validates {s : SubtypingContext} {env : Environment} {n : Nat}
    (definition : Definition s.typeDepth) (valid : Validates s env n) :
    Validates (definition.native.openContext s)
      (env.cons (definition.interpretation env)) n :=
  ((valid.bindType _).assume (definition.guards env n).1).assume
    (definition.guards env n).2

theorem noCollapse {s : SubtypingContext} {env : Environment} {n : Nat}
    (valid : Validates s env n) : ¬ InvertingSubtype s WFTy.top WFTy.bottom :=
  fun typing => (typing.sound env n valid n (Nat.le_refl n) (.var 0)).1 trivial

/-- A function-guarded recursive equation cannot reproduce the earlier inversion collapse. -/
theorem Definition.noCollapse (definition : Definition 0) :
    ¬ InvertingSubtype (definition.native.openContext SubtypingContext.empty)
      WFTy.top WFTy.bottom :=
  Transparent.noCollapse (definition.validates
    (empty_validates (fun _ _ => (fun _ => False, fun _ => False)) 0))

end CDotFCCT.CTML.Transparent
