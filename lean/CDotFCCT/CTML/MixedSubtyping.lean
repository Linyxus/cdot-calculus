import CDotFCCT.CTML.MixedContext
import CTMLCore.Declarative.IndexedTransport
import CTMLCore.Declarative.Subtyping

/-!
# Native Core subtyping in the mixed-record model

Every primitive subtyping rule preserves positive observations and reflects
negative ones. Assumed bounds need hold only through the current index.
The statement includes impredicative universals and arbitrary constraint abstraction.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Indexed

variable (ghost : FieldName → Bool)

/-- Both ordinary fields and ghost carriers are covariant in their payload. -/
theorem record_monotone {sub sup : Candidate} {n : Nat}
    (included : Includes sub sup n) (field : FieldName) :
    Includes (record ghost field sub) (record ghost field sup) n := by
  cases marked : ghost field with
  | false => simpa only [record, marked, Bool.false_eq_true, ↓reduceIte] using
      included.record field
  | true => simpa only [record, marked, ↓reduceIte] using
      TransparentRecord.monotone included field

theorem record_union (field : FieldName) {left right : Candidate}
    (leftDown : Downward left) (rightDown : Downward right) (n : Nat) :
    Includes (record ghost field (joint .union left right))
      (joint .union (record ghost field left) (record ghost field right)) n := by
  cases marked : ghost field with
  | false => simpa only [record, marked, Bool.false_eq_true, ↓reduceIte] using
      Indexed.recordUnion field leftDown rightDown n
  | true =>
      simp only [record, marked, ↓reduceIte]
      exact fun _ _ _ =>
        ⟨TransparentRecord.observes_or.mp, TransparentRecord.observesAll_and.mpr⟩

theorem record_intersection (field : FieldName) (left right : Candidate) (n : Nat) :
    Includes (joint .intersection (record ghost field left) (record ghost field right))
      (record ghost field (joint .intersection left right)) n := by
  cases marked : ghost field with
  | false => simpa only [record, marked, Bool.false_eq_true, ↓reduceIte] using
      Indexed.recordIntersection field left right n
  | true =>
      simp only [record, marked, ↓reduceIte]
      exact fun _ _ _ =>
        ⟨TransparentRecord.observes_and.mpr, TransparentRecord.observesAll_or.mp⟩

theorem subtype_sound {context : SubtypingContext} {sub sup : WFTy context.typeDepth}
    (typing : Subtype context sub sup) :
    ∀ env n, Validates ghost context env n →
      Includes (interpret ghost env sub.raw) (interpret ghost env sup.raw) n := by
  induction typing with
  | hyp guard member =>
    exact fun env n valid => (guard_iff ghost guard env n).mp (valid guard member)
  | refl => exact fun _ n _ => Includes.refl _ n
  | trans _ _ first second =>
    exact fun env n valid => (first env n valid).trans (second env n valid)
  | extremum kind =>
    cases kind with
    | top => exact fun _ _ _ _ _ _ => ⟨fun _ => trivial, False.elim⟩
    | bottom => exact fun _ _ _ _ _ _ => ⟨False.elim, fun _ => trivial⟩
  | neg _ ih => exact fun env n valid k within term =>
    ⟨(ih env n valid k within term).2, (ih env n valid k within term).1⟩
  | negDouble direction =>
    cases direction <;> exact fun _ n _ => Includes.refl _ n
  | classNeg different =>
    exact fun _ _ _ _ _ _ =>
      ⟨fun ⟨_, _, equal⟩ _ _ other => different
        (congrArg (fun | .record className _ => className | _ => "") (equal.symm.trans other)),
       fun ⟨_, _, equal⟩ _ _ other => different
        (congrArg (fun | .record className _ => className | _ => "") (other.symm.trans equal))⟩
  | arrow _ _ params results =>
    exact fun env n valid => (params env n valid).arrow (results env n valid)
  | arrowParamDistribution => exact fun _ n _ => arrowParamUnion _ _ _ n
  | arrowRetDistribution => exact fun _ n _ => arrowResultIntersection _ _ _ n
  | record _ ih => exact fun env n valid => record_monotone ghost (ih env n valid) _
  | recordDistribution kind =>
    cases kind with
    | union => exact fun env n _ =>
        record_union ghost _ (interpret_downward ghost _ env) (interpret_downward ghost _ env) n
    | intersection => exact fun _ n _ => record_intersection ghost _ _ _ n
  | jointAll kind _ _ left right =>
    cases kind with
    | union => exact fun env n valid k within term =>
        ⟨fun related => related.elim (left env n valid k within term).1
          (right env n valid k within term).1,
         fun apart => ⟨(left env n valid k within term).2 apart,
           (right env n valid k within term).2 apart⟩⟩
    | intersection => exact fun env n valid k within term =>
        ⟨fun related => ⟨(left env n valid k within term).1 related,
          (right env n valid k within term).1 related⟩,
         fun apart => apart.elim (left env n valid k within term).2
           (right env n valid k within term).2⟩
  | jointAnyLeft kind _ ih =>
    cases kind with
    | union => exact fun env n valid k within term =>
        ⟨fun related => .inl ((ih env n valid k within term).1 related),
         fun apart => (ih env n valid k within term).2 apart.1⟩
    | intersection => exact fun env n valid k within term =>
        ⟨fun related => (ih env n valid k within term).1 related.1,
         fun apart => .inl ((ih env n valid k within term).2 apart)⟩
  | jointAnyRight kind _ ih =>
    cases kind with
    | union => exact fun env n valid k within term =>
        ⟨fun related => .inr ((ih env n valid k within term).1 related),
         fun apart => (ih env n valid k within term).2 apart.2⟩
    | intersection => exact fun env n valid k within term =>
        ⟨fun related => (ih env n valid k within term).1 related.2,
         fun apart => .inr ((ih env n valid k within term).2 apart)⟩
  | jointDistribution kind =>
    cases kind with
    | union => exact fun _ _ _ _ _ _ => ⟨or_and_left.mpr, and_or_left.mp⟩
    | intersection => exact fun _ _ _ _ _ _ => ⟨and_or_left.mp, or_and_left.mpr⟩
  | forallLeft =>
    intro env n valid
    change Includes _ (interpret ghost env (Ty.substAt _ 0 _)) n
    rw [interpret_substAt_zero ghost]
    exact fun _ _ _ => ⟨fun related => related _, fun apart => ⟨_, apart⟩⟩
  | forallCovariant sub sup _ ih =>
    exact fun env n valid k within term =>
      ⟨fun related argument =>
        (ih (env.cons argument) n (valid.bindType argument) k within term).1 (related argument),
       fun ⟨argument, apart⟩ => ⟨argument,
         (ih (env.cons argument) n (valid.bindType argument) k within term).2 apart⟩⟩
  | @forallRight ctx type =>
    exact fun env _ _ k _ term =>
      ⟨fun related argument =>
        (congrArg (fun candidate : Candidate => (candidate k).1 term)
          (interpret_lift ghost type.raw env argument)).symm ▸ related,
       fun ⟨argument, apart⟩ =>
        congrArg (fun candidate : Candidate => (candidate k).2 term)
          (interpret_lift ghost type.raw env argument) ▸ apart⟩
  | constrainedLeft guard _ _ ih =>
    exact fun env n valid k within _ =>
      let holds := (guard_iff ghost guard env k).mpr ((ih env n valid).below within)
      ⟨fun related => related k (Nat.le_refl k) holds, fun apart => ⟨holds, apart⟩⟩
  | constrainedCovariant _ _ _ _ ih =>
    exact fun env n valid k within term =>
      ⟨fun related j below holds =>
        (ih env j ((valid.below (Nat.le_trans below within)).assume holds)
          j (Nat.le_refl j) term).1 (related j below holds),
       fun apart => ⟨apart.1,
         (ih env k ((valid.below within).assume apart.1)
           k (Nat.le_refl k) term).2 apart.2⟩⟩
  | constrainedRight _ body =>
    exact fun env _ _ k _ term =>
      ⟨fun related j within _ => (interpret_downward ghost body.raw env j k within term).1 related,
       fun apart => apart.2⟩

end CDotFCCT.CTML.Mixed
