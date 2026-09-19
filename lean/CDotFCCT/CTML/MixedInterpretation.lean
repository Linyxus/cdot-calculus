import CDotFCCT.CTML.TransparentRecords
import CTMLCore.Declarative.IndexedGuarded

/-!
# Type interpretation with ordinary records and reflective ghost labels

A fixed field-label policy separates ordinary runtime records from ghost carriers.
Ordinary records retain the native step-index guard; ghost fields reflect component
subtyping at the current index. Universals and arbitrary constraints are unchanged.
This module proves locality and downward closure for the complete type syntax.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Indexed

variable (ghost : FieldName → Bool)

/-- Reflective ghost labels and guarded ordinary fields share the native type syntax. -/
def record (field : FieldName) (payload : Candidate) : Candidate :=
  if ghost field then TransparentRecord.record field payload else Indexed.record field payload

/-- Both field interpretations inspect at most the current prefix. -/
theorem record_congr {field : FieldName} {left right : Candidate} {n : Nat}
    (agree : Agree n left right) : record ghost field left n = record ghost field right n := by
  cases marked : ghost field with
  | false => simpa only [record, marked, Bool.false_eq_true, ↓reduceIte] using
      Indexed.record_congr (field := field) (fun k smaller => agree k (Nat.le_of_lt smaller))
  | true => simpa only [record, marked, ↓reduceIte] using
      TransparentRecord.congr (field := field) agree.at

/-- Downward closure holds for either kind of field label. -/
theorem record_downward {payload : Candidate} (closed : Downward payload) (field : FieldName) :
    Downward (record ghost field payload) := by
  cases marked : ghost field with
  | false => simpa only [record, marked, Bool.false_eq_true, ↓reduceIte] using
      Indexed.record_downward field payload
  | true => simpa only [record, marked, ↓reduceIte] using
      TransparentRecord.downward closed field

/-- Only designated ghost labels admit unrestricted component reflection. -/
theorem record_inverse {field : FieldName} (marked : ghost field = true)
    {sub sup : Candidate} {n : Nat}
    (included : Includes (record ghost field sub) (record ghost field sup) n) :
    Includes sub sup n :=
  TransparentRecord.inverse (by simpa only [record, marked, ↓reduceIte] using included)

/-- Ordinary records guard every recursive occurrence in their payload. -/
theorem record_guarded {field : FieldName} (ordinary : ghost field = false) :
    Contractive (record ghost field) := by
  intro n left right agree
  simpa only [record, ordinary, Bool.false_eq_true, ↓reduceIte] using
    Indexed.record_congr (field := field) agree

mutual
  def interpret (ghost : FieldName → Bool) (env : Environment) : Ty → Candidate
    | .var index => prefixClosure (env index)
    | .extremum .top => fun _ => (fun _ => True, fun _ => False)
    | .extremum .bottom => fun _ => (fun _ => False, fun _ => True)
    | .neg body => negative (interpret ghost env body)
    | .joint kind left right => joint kind (interpret ghost env left) (interpret ghost env right)
    | .arrow param result => arrow (interpret ghost env param) (interpret ghost env result)
    | .cls name => fun _ =>
        (fun term => ∃ (names : List FieldName) (fields : TermFields names),
          term = .record name fields,
         fun term => ∀ {names : List FieldName} (fields : TermFields names),
          term ≠ .record name fields)
    | .record field payload => record ghost field (interpret ghost env payload)
    | .all body => universal (fun argument => interpret ghost (env.cons argument) body)
    | .constrained guard body =>
        constrained (interpretGuard ghost env guard) (interpret ghost env body)

  def interpretGuard (ghost : FieldName → Bool) (env : Environment) : Constraint → Nat → Prop
    | .constr sub sup => Includes (interpret ghost env sub) (interpret ghost env sup)
end

/-- Interpretation at `n` never observes an environment beyond `n`. -/
private theorem interpretCongr :
    (∀ type : Ty, ∀ left right n, Environment.Agree n left right →
      interpret ghost left type n = interpret ghost right type n) ∧
    (∀ guard : Constraint, ∀ left right n, Environment.Agree n left right →
      interpretGuard ghost left guard n = interpretGuard ghost right guard n) :=
  TyConstraint.mutualInduction
    (fun type => ∀ left right n, Environment.Agree n left right →
      interpret ghost left type n = interpret ghost right type n)
    (fun guard => ∀ left right n, Environment.Agree n left right →
      interpretGuard ghost left guard n = interpretGuard ghost right guard n)
    (varCase := fun index _ _ _ agree => prefixClosure_congr (agree index))
    (extremumCase := fun kind _ _ _ _ => by cases kind <;> rfl)
    (negCase := fun _ ih left right n agree =>
      congrArg (fun observation : Observation => (observation.2, observation.1))
        (ih left right n agree))
    (jointCase := fun _ _ _ ihLeft ihRight left right n agree =>
      joint_congr (ihLeft left right n agree) (ihRight left right n agree))
    (arrowCase := fun _ _ ihParam ihResult left right n agree =>
      arrow_congr
        (fun k smaller => ihParam left right k (agree.below (Nat.le_of_lt smaller)))
        (fun k smaller => ihResult left right k (agree.below (Nat.le_of_lt smaller))))
    (classCase := fun _ _ _ _ _ => rfl)
    (recordCase := fun _ _ ih left right n agree =>
      record_congr ghost (fun k within => ih left right k (agree.below within)))
    (allCase := fun _ ih left right n agree =>
      universal_congr fun argument => ih _ _ n (agree.cons argument))
    (constrainedCase := fun _ _ ihGuard ihBody left right n agree =>
      constrained_congr
        (fun k within => ihGuard left right k (agree.below within))
        (fun k within => ihBody left right k (agree.below within)))
    (constrCase := fun _ _ ihSub ihSup left right n agree =>
      includes_congr
        (fun k within => ihSub left right k (agree.below within))
        (fun k within => ihSup left right k (agree.below within)))

theorem interpret_congr (type : Ty) {left right : Environment} {n : Nat}
    (agree : Environment.Agree n left right) :
    interpret ghost left type n = interpret ghost right type n :=
  (interpretCongr ghost).1 type left right n agree

theorem interpretGuard_congr (guard : Constraint) {left right : Environment} {n : Nat}
    (agree : Environment.Agree n left right) :
    interpretGuard ghost left guard n = interpretGuard ghost right guard n :=
  (interpretCongr ghost).2 guard left right n agree

private theorem interpretationDownward :
    (∀ type : Ty, ∀ env, Downward (interpret ghost env type)) ∧
    (∀ guard : Constraint, ∀ env m n, m ≤ n →
      interpretGuard ghost env guard n → interpretGuard ghost env guard m) :=
  TyConstraint.mutualInduction
    (fun type => ∀ env, Downward (interpret ghost env type))
    (fun guard => ∀ env m n, m ≤ n →
      interpretGuard ghost env guard n → interpretGuard ghost env guard m)
    (varCase := fun _ _ _ _ within _ =>
      ⟨fun all k below => all k (Nat.le_trans below within),
       fun all k below => all k (Nat.le_trans below within)⟩)
    (extremumCase := fun kind _ _ _ _ _ => by cases kind <;> exact ⟨id, id⟩)
    (negCase := fun _ ih env m n within term =>
      ⟨(ih env m n within term).2, (ih env m n within term).1⟩)
    (jointCase := fun kind _ _ ihLeft ihRight env m n within term =>
      match kind with
      | .union =>
        ⟨Or.imp (ihLeft env m n within term).1 (ihRight env m n within term).1,
         And.imp (ihLeft env m n within term).2 (ihRight env m n within term).2⟩
      | .intersection =>
        ⟨And.imp (ihLeft env m n within term).1 (ihRight env m n within term).1,
         Or.imp (ihLeft env m n within term).2 (ihRight env m n within term).2⟩)
    (arrowCase := fun _ _ _ _ _ => arrow_downward _ _)
    (classCase := fun _ _ _ _ _ _ => ⟨id, id⟩)
    (recordCase := fun _ _ ih env => record_downward ghost (ih env) _)
    (allCase := fun _ ih env m n within term =>
      ⟨fun all argument => (ih (env.cons argument) m n within term).1 (all argument),
       fun ⟨argument, negative⟩ =>
        ⟨argument, (ih (env.cons argument) m n within term).2 negative⟩⟩)
    (constrainedCase := fun _ _ ihGuard ihBody env m n within term =>
      ⟨fun all k below => all k (Nat.le_trans below within),
       fun both => ⟨ihGuard env m n within both.1, (ihBody env m n within term).2 both.2⟩⟩)
    (constrCase := fun _ _ _ _ _ _ _ within all k below =>
      all k (Nat.le_trans below within))

theorem interpret_downward (type : Ty) (env : Environment) :
    Downward (interpret ghost env type) := (interpretationDownward ghost).1 type env

theorem interpretGuard_downward (guard : Constraint) (env : Environment)
    {m n : Nat} (within : m ≤ n) :
    interpretGuard ghost env guard n → interpretGuard ghost env guard m :=
  (interpretationDownward ghost).2 guard env m n within

end CDotFCCT.CTML.Mixed
