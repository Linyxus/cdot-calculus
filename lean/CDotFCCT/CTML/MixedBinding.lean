import CDotFCCT.CTML.MixedInterpretation
import CTMLCore.Declarative.IndexedBinding

/-!
# Binding laws for the mixed-record interpretation

The environment lifting relation is shared with the original indexed model.
Substitution preserves the field-label policy, including both observations of ghost fields.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Indexed

variable (ghost : FieldName → Bool)

private theorem interpretationLiftAt :
    (∀ type : Ty, ∀ cutoff amount env extended,
      Environment.Lifted cutoff amount env extended →
        interpret ghost extended (type.liftAt cutoff amount) = interpret ghost env type) ∧
    (∀ guard : Constraint, ∀ cutoff amount env extended,
      Environment.Lifted cutoff amount env extended →
        interpretGuard ghost extended (guard.liftAt cutoff amount) =
          interpretGuard ghost env guard) :=
  TyConstraint.mutualInduction
    (fun type => ∀ cutoff amount env extended,
      Environment.Lifted cutoff amount env extended →
        interpret ghost extended (type.liftAt cutoff amount) = interpret ghost env type)
    (fun guard => ∀ cutoff amount env extended,
      Environment.Lifted cutoff amount env extended →
        interpretGuard ghost extended (guard.liftAt cutoff amount) = interpretGuard ghost env guard)
    (varCase := fun index cutoff _ _ _ lifted =>
      if above : cutoff ≤ index then by
        simpa only [Ty.liftAt, ite_eq_left above, interpret] using
          congrArg prefixClosure (lifted.2 index above)
      else by
        simpa only [Ty.liftAt, ite_eq_right above, interpret] using
          congrArg prefixClosure (lifted.1 index (Nat.lt_of_not_ge above)))
    (extremumCase := fun kind _ _ _ _ _ => by cases kind <;> rfl)
    (negCase := fun _ ih cutoff amount env extended lifted =>
      congrArg negative (ih cutoff amount env extended lifted))
    (jointCase := fun kind _ _ ihLeft ihRight cutoff amount env extended lifted =>
      congrArg₂ (joint kind) (ihLeft cutoff amount env extended lifted)
        (ihRight cutoff amount env extended lifted))
    (arrowCase := fun _ _ ihParam ihResult cutoff amount env extended lifted =>
      congrArg₂ arrow (ihParam cutoff amount env extended lifted)
        (ihResult cutoff amount env extended lifted))
    (classCase := fun _ _ _ _ _ _ => rfl)
    (recordCase := fun field _ ih cutoff amount env extended lifted =>
      congrArg (record ghost field) (ih cutoff amount env extended lifted))
    (allCase := fun _ ih cutoff amount _ _ lifted =>
      congrArg universal (funext fun argument =>
        ih (cutoff + 1) amount _ _ (lifted.cons argument)))
    (constrainedCase := fun _ _ ihGuard ihBody cutoff amount env extended lifted =>
      congrArg₂ constrained (ihGuard cutoff amount env extended lifted)
        (ihBody cutoff amount env extended lifted))
    (constrCase := fun _ _ ihSub ihSup cutoff amount env extended lifted =>
      congrArg₂ Includes (ihSub cutoff amount env extended lifted)
        (ihSup cutoff amount env extended lifted))

theorem interpret_lift (type : Ty) (env : Environment) (argument : Candidate) :
    interpret ghost (env.cons argument) (type.lift 1) = interpret ghost env type :=
  (interpretationLiftAt ghost).1 type 0 1 env (env.cons argument)
    ⟨fun _ below => False.elim (Nat.not_lt_zero _ below), fun _ _ => rfl⟩

theorem interpretGuard_lift (guard : Constraint) (env : Environment) (argument : Candidate) :
    interpretGuard ghost (env.cons argument) (guard.lift 1) = interpretGuard ghost env guard :=
  (interpretationLiftAt ghost).2 guard 0 1 env (env.cons argument)
    ⟨fun _ below => False.elim (Nat.not_lt_zero _ below), fun _ _ => rfl⟩

theorem interpret_liftAt (type : Ty) {cutoff amount : Nat} {env extended : Environment}
    (lifted : Environment.Lifted cutoff amount env extended) :
    interpret ghost extended (type.liftAt cutoff amount) = interpret ghost env type :=
  (interpretationLiftAt ghost).1 type cutoff amount env extended lifted

theorem interpretGuard_liftAt (guard : Constraint) {cutoff amount : Nat}
    {env extended : Environment} (lifted : Environment.Lifted cutoff amount env extended) :
    interpretGuard ghost extended (guard.liftAt cutoff amount) = interpretGuard ghost env guard :=
  (interpretationLiftAt ghost).2 guard cutoff amount env extended lifted

/-- Relate a simultaneous syntactic substitution to the environment it replaces. -/
def Substituted (substitution : Nat → Ty) (source target : Environment) : Prop :=
  ∀ index, interpret ghost target (substitution index) = prefixClosure (source index)

theorem Substituted.cons {substitution : Nat → Ty} {source target : Environment}
    (substituted : Substituted ghost substitution source target) (argument : Candidate) :
    Substituted ghost (fun | 0 => .var 0 | index + 1 => (substitution index).lift 1)
      (source.cons argument) (target.cons argument)
  | 0 => rfl
  | index + 1 =>
      (interpret_lift ghost (substitution index) target argument).trans (substituted index)

private theorem interpretationSubstWith :
    (∀ type : Ty, ∀ substitution source target,
      Substituted ghost substitution source target →
        interpret ghost target (type.substWith substitution) = interpret ghost source type) ∧
    (∀ guard : Constraint, ∀ substitution source target,
      Substituted ghost substitution source target →
        interpretGuard ghost target (guard.substWith substitution) =
          interpretGuard ghost source guard) :=
  TyConstraint.mutualInduction
    (fun type => ∀ substitution source target,
      Substituted ghost substitution source target →
        interpret ghost target (type.substWith substitution) = interpret ghost source type)
    (fun guard => ∀ substitution source target,
      Substituted ghost substitution source target →
        interpretGuard ghost target (guard.substWith substitution) =
          interpretGuard ghost source guard)
    (varCase := fun index _ _ _ substituted => substituted index)
    (extremumCase := fun kind _ _ _ _ => by cases kind <;> rfl)
    (negCase := fun _ ih substitution source target substituted =>
      congrArg negative (ih substitution source target substituted))
    (jointCase := fun kind _ _ ihLeft ihRight substitution source target substituted =>
      congrArg₂ (joint kind) (ihLeft substitution source target substituted)
        (ihRight substitution source target substituted))
    (arrowCase := fun _ _ ihParam ihResult substitution source target substituted =>
      congrArg₂ arrow (ihParam substitution source target substituted)
        (ihResult substitution source target substituted))
    (classCase := fun _ _ _ _ _ => rfl)
    (recordCase := fun field _ ih substitution source target substituted =>
      congrArg (record ghost field) (ih substitution source target substituted))
    (allCase := fun _ ih _ _ _ substituted =>
      congrArg universal (funext fun argument => ih _ _ _ (substituted.cons ghost argument)))
    (constrainedCase := fun _ _ ihGuard ihBody substitution source target substituted =>
      congrArg₂ constrained (ihGuard substitution source target substituted)
        (ihBody substitution source target substituted))
    (constrCase := fun _ _ ihSub ihSup substitution source target substituted =>
      congrArg₂ Includes (ihSub substitution source target substituted)
        (ihSup substitution source target substituted))

private theorem substAtZero (replacement : Ty) (env : Environment) :
    Substituted ghost
      (fun index => if index < 0 then .var index
        else if index = 0 then replacement else .var (index - 1))
      (env.cons (interpret ghost env replacement)) env
  | 0 => (prefixClosure_eq (interpret_downward ghost replacement env)).symm
  | _ + 1 => rfl

theorem interpret_substAt_zero (body replacement : Ty) (env : Environment) :
    interpret ghost env (body.substAt 0 replacement) =
      interpret ghost (env.cons (interpret ghost env replacement)) body :=
  (interpretationSubstWith ghost).1 body _ _ _ (substAtZero ghost replacement env)

theorem interpretGuard_substAt_zero (guard : Constraint) (replacement : Ty) (env : Environment) :
    interpretGuard ghost env (guard.substAt 0 replacement) =
      interpretGuard ghost (env.cons (interpret ghost env replacement)) guard :=
  (interpretationSubstWith ghost).2 guard _ _ _ (substAtZero ghost replacement env)

end CDotFCCT.CTML.Mixed
