import CDotFCCT.CTML.ArrowGuarded
import CDotFCCT.CTML.TransparentInterpretation

/-!
# Guarded fixed points in the transparent-record model

Native record wrappers preserve contractiveness supplied by functions inside
those records. The stricter recursion predicate is checked through every type
constructor, including arbitrary constraints and universals. This proves the
recursive equations in the candidate model; it is not a new target safety theorem.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Transparent

open CTMLCore CTMLCore.Syntax CTMLCore.Indexed

private theorem guardedInterpretation :
    (∀ type : Ty, ∀ index, type.ArrowGuardedAt index → ∀ left right n,
      Environment.GuardedAgree index n left right →
        interpret left type n = interpret right type n) ∧
    (∀ guard : Constraint, ∀ index, guard.ArrowGuardedAt index → ∀ left right n,
      Environment.GuardedAgree index n left right →
        interpretGuard left guard n = interpretGuard right guard n) :=
  TyConstraint.mutualInduction
    (fun type => ∀ index, type.ArrowGuardedAt index → ∀ left right n,
      Environment.GuardedAgree index n left right →
        interpret left type n = interpret right type n)
    (fun guard => ∀ index, guard.ArrowGuardedAt index → ∀ left right n,
      Environment.GuardedAgree index n left right →
        interpretGuard left guard n = interpretGuard right guard n)
    (varCase := fun found _ different _ _ _ agree =>
      prefixClosure_congr (agree.outside found different))
    (extremumCase := fun kind _ _ _ _ _ _ => by cases kind <;> rfl)
    (negCase := fun _ ih index guarded left right n agree =>
      congrArg (fun observation : Observation => (observation.2, observation.1))
        (ih index guarded left right n agree))
    (jointCase := fun _ _ _ ihLeft ihRight index guarded left right n agree =>
      joint_congr (ihLeft index guarded.1 left right n agree)
        (ihRight index guarded.2 left right n agree))
    (arrowCase := fun param result _ _ _ _ _ _ _ agree =>
      arrow_congr
        (fun _ smaller => interpret_congr param (agree.before smaller))
        (fun _ smaller => interpret_congr result (agree.before smaller)))
    (classCase := fun _ _ _ _ _ _ _ => rfl)
    (recordCase := fun _ _ ih index guarded left right n agree =>
      TransparentRecord.congr (ih index guarded left right n agree))
    (allCase := fun _ ih index guarded _ _ n agree =>
      universal_congr fun argument => ih (index + 1) guarded _ _ n (agree.cons argument))
    (constrainedCase := fun _ _ ihGuard ihBody index guarded left right _ agree =>
      constrained_congr
        (fun k within => ihGuard index guarded.1 left right k (agree.below within))
        (fun k within => ihBody index guarded.2 left right k (agree.below within)))
    (constrCase := fun _ _ ihSub ihSup index guarded left right _ agree =>
      includes_congr
        (fun k within => ihSub index guarded.1 left right k (agree.below within))
        (fun k within => ihSup index guarded.2 left right k (agree.below within)))

/-- Function guards prevent observing the recursive slot at the current index. -/
theorem interpret_guarded {type : Ty} {index n : Nat} (guarded : type.ArrowGuardedAt index)
    {left right : Environment} (agree : Environment.GuardedAgree index n left right) :
    interpret left type n = interpret right type n :=
  guardedInterpretation.1 type index guarded left right n agree

def Definition.operator {depth : Nat} (definition : Definition depth) (env : Environment)
    (self : Candidate) : Candidate := interpret (env.cons self) definition.body.raw

theorem Definition.contractive {depth : Nat} (definition : Definition depth)
    (env : Environment) : Contractive (definition.operator env) :=
  fun _ _ _ agree => interpret_guarded definition.guarded
    ⟨fun
      | 0, different, _, _ => False.elim (different rfl)
      | _ + 1, _, _, _ => rfl,
     agree⟩

def Definition.interpretation {depth : Nat} (definition : Definition depth)
    (env : Environment) : Candidate :=
  fixedPoint (definition.operator env) (fun _ => False, fun _ => False)

theorem Definition.unfold {depth : Nat} (definition : Definition depth)
    (env : Environment) (n : Nat) :
    definition.interpretation env n =
      interpret (env.cons (definition.interpretation env)) definition.body.raw n :=
  fixedPoint_unfold (definition.contractive env) _ n

theorem Definition.downward {depth : Nat} (definition : Definition depth)
    (env : Environment) : Downward (definition.interpretation env) := by
  intro m n within term
  rw [definition.unfold env n, definition.unfold env m]
  exact interpret_downward definition.body.raw _ m n within term

/-- The bound variable's prefix closure agrees with its recursive body at every index. -/
theorem Definition.equation {depth : Nat} (definition : Definition depth) (env : Environment) :
    interpret (env.cons (definition.interpretation env)) definition.native.name.raw =
      interpret (env.cons (definition.interpretation env)) definition.body.raw :=
  (prefixClosure_eq (definition.downward env)).trans (funext (definition.unfold env))

theorem Definition.guards {depth : Nat} (definition : Definition depth)
    (env : Environment) (n : Nat) :
    let extended := env.cons (definition.interpretation env)
    interpretGuard extended (.constr definition.native.name.raw definition.body.raw) n ∧
      interpretGuard extended (.constr definition.body.raw definition.native.name.raw) n := by
  change Includes _ _ n ∧ Includes _ _ n
  rw [definition.equation env]
  exact ⟨fun _ _ _ => ⟨id, id⟩, fun _ _ _ => ⟨id, id⟩⟩

end CDotFCCT.CTML.Transparent
