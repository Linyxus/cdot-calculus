import CDotFCCT.CTML.TransparentRecords
import CTMLCore.Declarative.IndexedGuarded

/-!
# Type interpretation with transparent record fields

This interpretation changes only the record constructor of the indexed model.
It retains the existing arrow, universal, constraint, and polarity operations.
The model's agreement lemmas are checked independently of the current target's
interpretation; no target typing or subtyping rule is added here.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Transparent

open CTMLCore CTMLCore.Syntax CTMLCore.Indexed

mutual
  def interpret (env : Environment) : Ty → Candidate
    | .var index => prefixClosure (env index)
    | .extremum .top => fun _ => (fun _ => True, fun _ => False)
    | .extremum .bottom => fun _ => (fun _ => False, fun _ => True)
    | .neg body => negative (interpret env body)
    | .joint kind left right => joint kind (interpret env left) (interpret env right)
    | .arrow param result => arrow (interpret env param) (interpret env result)
    | .cls name => fun _ =>
        (fun term => ∃ (names : List FieldName) (fields : TermFields names),
          term = .record name fields,
         fun term => ∀ {names : List FieldName} (fields : TermFields names),
          term ≠ .record name fields)
    | .record field payload => TransparentRecord.record field (interpret env payload)
    | .all body => universal (fun argument => interpret (env.cons argument) body)
    | .constrained guard body => constrained (interpretGuard env guard) (interpret env body)

  def interpretGuard (env : Environment) : Constraint → Nat → Prop
    | .constr sub sup => Includes (interpret env sub) (interpret env sup)
end

/-- Interpretation at `n` never observes an environment beyond `n`. -/
private theorem interpretCongr :
    (∀ type : Ty, ∀ left right n, Environment.Agree n left right →
      interpret left type n = interpret right type n) ∧
    (∀ guard : Constraint, ∀ left right n, Environment.Agree n left right →
      interpretGuard left guard n = interpretGuard right guard n) :=
  TyConstraint.mutualInduction
    (fun type => ∀ left right n, Environment.Agree n left right →
      interpret left type n = interpret right type n)
    (fun guard => ∀ left right n, Environment.Agree n left right →
      interpretGuard left guard n = interpretGuard right guard n)
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
      TransparentRecord.congr (ih left right n agree))
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
    interpret left type n = interpret right type n := interpretCongr.1 type left right n agree

theorem interpretGuard_congr (guard : Constraint) {left right : Environment} {n : Nat}
    (agree : Environment.Agree n left right) :
    interpretGuard left guard n = interpretGuard right guard n :=
  interpretCongr.2 guard left right n agree

private theorem interpretationDownward :
    (∀ type : Ty, ∀ env, Downward (interpret env type)) ∧
    (∀ guard : Constraint, ∀ env m n, m ≤ n →
      interpretGuard env guard n → interpretGuard env guard m) :=
  TyConstraint.mutualInduction
    (fun type => ∀ env, Downward (interpret env type))
    (fun guard => ∀ env m n, m ≤ n →
      interpretGuard env guard n → interpretGuard env guard m)
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
    (recordCase := fun _ _ ih env => TransparentRecord.downward (ih env) _)
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
    Downward (interpret env type) := interpretationDownward.1 type env

theorem interpretGuard_downward (guard : Constraint) (env : Environment)
    {m n : Nat} (within : m ≤ n) :
    interpretGuard env guard n → interpretGuard env guard m :=
  interpretationDownward.2 guard env m n within

end CDotFCCT.CTML.Transparent
