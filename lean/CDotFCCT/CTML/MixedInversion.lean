import CDotFCCT.CTML.MixedSubtyping
import CDotFCCT.CTML.MixedRecursion
import CDotFCCT.CTML.MixedRows
import CTMLCore.Declarative.Lattice

/-!
# Ghost-component inversion with ordinary record-guarded recursion

Inversion is available only for designated ghost labels. Ordinary record fields
remain recursion guards, including when their payload contains arbitrary constraints.
The fixed label policy is shared by subtyping and recursive type formation.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Indexed

inductive InvertingSubtype (ghost : FieldName → Bool) : (s : SubtypingContext) → WFTy s.typeDepth →
    WFTy s.typeDepth → Prop where
  | native {s : SubtypingContext} {sub sup : WFTy s.typeDepth} :
      Subtype s sub sup → InvertingSubtype ghost s sub sup
  | nativeWith {s : SubtypingContext} {sub sup : WFTy s.typeDepth}
      (guards : List (WFConstraint s.typeDepth)) :
      Subtype ⟨s.typeDepth, guards⟩ sub sup →
      (∀ guard ∈ guards, InvertingSubtype ghost s guard.sub guard.sup) →
      InvertingSubtype ghost s sub sup
  | trans {s : SubtypingContext} {sub middle sup : WFTy s.typeDepth} :
      InvertingSubtype ghost s sub middle → InvertingSubtype ghost s middle sup →
      InvertingSubtype ghost s sub sup
  | inverse {s : SubtypingContext} {field : FieldName} {sub sup : WFTy s.typeDepth} :
      ghost field = true →
      InvertingSubtype ghost s (WFTy.record field sub) (WFTy.record field sup) →
      InvertingSubtype ghost s sub sup
  | rowInverse {s : SubtypingContext} {labels : List FieldName}
      {sub sup : FieldName → WFTy s.typeDepth} {field : FieldName} :
      (∀ label ∈ labels, ghost label = true) →
      field ∈ labels → InvertingSubtype ghost s (row labels sub) (row labels sup) →
      InvertingSubtype ghost s (sub field) (sup field)
  | cut {s : SubtypingContext} (guard : WFConstraint s.typeDepth)
      {sub sup : WFTy s.typeDepth} :
      InvertingSubtype ghost s guard.sub guard.sup →
      InvertingSubtype ghost (s.assume guard) sub sup → InvertingSubtype ghost s sub sup
  | forallCovariant {s : SubtypingContext} {sub sup : WFTy (s.typeDepth + 1)} :
      InvertingSubtype ghost s.bindType sub sup →
      InvertingSubtype ghost s (WFTy.all sub) (WFTy.all sup)
  | constrainedCovariant {s : SubtypingContext} (guard : WFConstraint s.typeDepth)
      {sub sup : WFTy s.typeDepth} :
      InvertingSubtype ghost (s.assume guard) sub sup →
      InvertingSubtype ghost s (WFTy.constrained guard sub) (WFTy.constrained guard sup)

variable {ghost : FieldName → Bool}

theorem InvertingSubtype.sound {s : SubtypingContext} {sub sup : WFTy s.typeDepth}
    (typing : InvertingSubtype ghost s sub sup) :
    ∀ env n, Validates ghost s env n →
      Includes (interpret ghost env sub.raw) (interpret ghost env sup.raw) n := by
  induction typing with
  | native typing => exact subtype_sound ghost typing
  | nativeWith guards typing _ ih =>
      exact fun env n valid => subtype_sound ghost typing env n
        (fun guard member => (guard_iff ghost guard env n).mpr (ih guard member env n valid))
  | trans _ _ first second =>
      exact fun env n valid => (first env n valid).trans (second env n valid)
  | inverse marked _ ih =>
      exact fun env n valid => record_inverse ghost marked (ih env n valid)
  | rowInverse reflective member _ ih =>
      exact fun env n valid => row_inverse ghost reflective member (ih env n valid)
  | cut guard _ _ inferred body =>
      exact fun env n valid => body env n
        (valid.assume ((guard_iff ghost guard env n).mpr (inferred env n valid)))
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
    (typing : InvertingSubtype ghost s sup sub) :
    InvertingSubtype ghost s (WFTy.neg sub) (WFTy.neg sup) :=
  .cut (WFConstraint.constr sup sub) typing
    (.native (.neg (@Subtype.hyp (s.assume (WFConstraint.constr sup sub))
      (WFConstraint.constr sup sub) List.mem_cons_self)))

theorem InvertingSubtype.negInverse {s : SubtypingContext} {sub sup : WFTy s.typeDepth}
    (typing : InvertingSubtype ghost s (WFTy.neg sup) (WFTy.neg sub)) :
    InvertingSubtype ghost s sub sup :=
  .trans (.native (.negDouble .upper))
    (.trans typing.neg (.native (.negDouble .lower)))

theorem Definition.validates {s : SubtypingContext} {env : Environment} {n : Nat}
    (definition : Definition ghost s.typeDepth) (valid : Validates ghost s env n) :
    Validates ghost (definition.native.openContext s)
      (env.cons (definition.interpretation env)) n :=
  ((valid.bindType _).assume (definition.guards env n).1).assume
    (definition.guards env n).2

theorem noCollapse {s : SubtypingContext} {env : Environment} {n : Nat}
    (valid : Validates ghost s env n) : ¬ InvertingSubtype ghost s WFTy.top WFTy.bottom :=
  fun typing => (typing.sound env n valid n (Nat.le_refl n) (.var 0)).1 trivial

/-- A mixed record-guarded recursive equation cannot reproduce the earlier inversion collapse. -/
theorem Definition.noCollapse (definition : Definition ghost 0) :
    ¬ InvertingSubtype ghost (definition.native.openContext SubtypingContext.empty)
      WFTy.top WFTy.bottom :=
  Mixed.noCollapse (definition.validates
    (empty_validates ghost (fun _ _ => (fun _ => False, fun _ => False)) 0))

end CDotFCCT.CTML.Mixed
