import CDotFCCT.CTML.MixedInterpretation

/-!
# Record-guarded fixed points with reflective ghost labels

Ordinary record fields guard recursive occurrences directly. Reflective ghost
labels propagate the guardedness obligation to their payload instead. Universals,
negation, and arbitrary constraints remain available. The resulting operators
have genuine fixed points that satisfy both directions of every recursive equation.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Indexed

mutual
  /-- Ordinary records or arrows guard recursion; ghost records propagate the obligation. -/
  def GuardedAt (ghost : FieldName → Bool) (index : Nat) : Ty → Prop
    | .var found => found ≠ index
    | .extremum _ => True
    | .neg body => GuardedAt ghost index body
    | .joint _ left right => GuardedAt ghost index left ∧ GuardedAt ghost index right
    | .arrow _ _ => True
    | .cls _ => True
    | .record field payload => if ghost field then GuardedAt ghost index payload else True
    | .all body => GuardedAt ghost (index + 1) body
    | .constrained guard body =>
        GuardGuardedAt ghost index guard ∧ GuardedAt ghost index body

  /-- Both constraint endpoints are checked, retaining unrestricted constraint syntax. -/
  def GuardGuardedAt (ghost : FieldName → Bool) (index : Nat) : Constraint → Prop
    | .constr sub sup => GuardedAt ghost index sub ∧ GuardedAt ghost index sup
end

mutual
  theorem GuardedAt.native {ghost : FieldName → Bool} {type : Ty} {index : Nat}
      (guarded : GuardedAt ghost index type) : type.GuardedAt index :=
    match type with
    | .var _ => guarded
    | .extremum _ | .arrow _ _ | .cls _ | .record _ _ => trivial
    | .neg body => GuardedAt.native (type := body) guarded
    | .joint _ _ _ => ⟨GuardedAt.native guarded.1, GuardedAt.native guarded.2⟩
    | .all body => GuardedAt.native (type := body) (index := index + 1) guarded
    | .constrained _ _ => ⟨GuardGuardedAt.native guarded.1, GuardedAt.native guarded.2⟩

  theorem GuardGuardedAt.native {ghost : FieldName → Bool} {guard : Constraint} {index : Nat}
      (guarded : GuardGuardedAt ghost index guard) : guard.GuardedAt index :=
    match guard with
    | .constr _ _ => ⟨GuardedAt.native guarded.1, GuardedAt.native guarded.2⟩
end

/-- A declaration carries the same fixed label policy as its interpretation. -/
structure Definition (ghost : FieldName → Bool) (depth : Nat) where
  body : WFTy (depth + 1)
  guarded : GuardedAt ghost 0 body.raw

variable {ghost : FieldName → Bool}

def Definition.native {depth : Nat} (definition : Definition ghost depth) : RecursiveType depth :=
  ⟨definition.body, definition.guarded.native⟩

def Definition.arrow {depth : Nat} (param ret : WFTy (depth + 1)) : Definition ghost depth :=
  ⟨WFTy.arrow param ret, trivial⟩

/-- Ordinary record fields admit any payload, including negative occurrences and constraints. -/
def Definition.record {depth : Nat} (field : FieldName) (ordinary : ghost field = false)
    (payload : WFTy (depth + 1)) : Definition ghost depth :=
  ⟨WFTy.record field payload, by
    change GuardedAt ghost 0 (.record field payload.raw)
    simp only [GuardedAt, ordinary, Bool.false_eq_true, ↓reduceIte]⟩

/-- A ghost wrapper preserves guards found deeper inside the payload. -/
def Definition.ghostRecord {depth : Nat} (field : FieldName) (marked : ghost field = true)
    (payload : Definition ghost depth) : Definition ghost depth :=
  ⟨WFTy.record field payload.body, by
    change GuardedAt ghost 0 (.record field payload.body.raw)
    simpa only [GuardedAt, marked, ↓reduceIte] using payload.guarded⟩

variable (ghost)

private theorem guardedInterpretation :
    (∀ type : Ty, ∀ index, GuardedAt ghost index type → ∀ left right n,
      Environment.GuardedAgree index n left right →
        interpret ghost left type n = interpret ghost right type n) ∧
    (∀ guard : Constraint, ∀ index, GuardGuardedAt ghost index guard → ∀ left right n,
      Environment.GuardedAgree index n left right →
        interpretGuard ghost left guard n = interpretGuard ghost right guard n) :=
  TyConstraint.mutualInduction
    (fun type => ∀ index, GuardedAt ghost index type → ∀ left right n,
      Environment.GuardedAgree index n left right →
        interpret ghost left type n = interpret ghost right type n)
    (fun guard => ∀ index, GuardGuardedAt ghost index guard → ∀ left right n,
      Environment.GuardedAgree index n left right →
        interpretGuard ghost left guard n = interpretGuard ghost right guard n)
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
        (fun _ smaller => interpret_congr ghost param (agree.before smaller))
        (fun _ smaller => interpret_congr ghost result (agree.before smaller)))
    (classCase := fun _ _ _ _ _ _ _ => rfl)
    (recordCase := fun field payload ih index guarded left right n agree => by
      cases marked : ghost field with
      | false =>
          exact record_guarded ghost marked n _ _
            (fun _ smaller => interpret_congr ghost payload (agree.before smaller))
      | true =>
          have payloadGuarded : GuardedAt ghost index payload := by
            simpa only [GuardedAt, marked, ↓reduceIte] using guarded
          simpa only [interpret, record, marked, ↓reduceIte] using
            TransparentRecord.congr (field := field)
              (ih index payloadGuarded left right n agree))
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

/-- Ordinary records and arrows prevent observing the recursive slot at the current index. -/
theorem interpret_guarded {type : Ty} {index n : Nat} (guarded : GuardedAt ghost index type)
    {left right : Environment} (agree : Environment.GuardedAgree index n left right) :
    interpret ghost left type n = interpret ghost right type n :=
  (guardedInterpretation ghost).1 type index guarded left right n agree

variable {ghost}

def Definition.operator {depth : Nat} (definition : Definition ghost depth) (env : Environment)
    (self : Candidate) : Candidate := interpret ghost (env.cons self) definition.body.raw

theorem Definition.contractive {depth : Nat} (definition : Definition ghost depth)
    (env : Environment) : Contractive (definition.operator env) :=
  fun _ _ _ agree => interpret_guarded ghost definition.guarded
    ⟨fun
      | 0, different, _, _ => False.elim (different rfl)
      | _ + 1, _, _, _ => rfl,
     agree⟩

def Definition.interpretation {depth : Nat} (definition : Definition ghost depth)
    (env : Environment) : Candidate :=
  fixedPoint (definition.operator env) (fun _ => False, fun _ => False)

theorem Definition.unfold {depth : Nat} (definition : Definition ghost depth)
    (env : Environment) (n : Nat) :
    definition.interpretation env n =
      interpret ghost (env.cons (definition.interpretation env)) definition.body.raw n :=
  fixedPoint_unfold (definition.contractive env) _ n

theorem Definition.downward {depth : Nat} (definition : Definition ghost depth)
    (env : Environment) : Downward (definition.interpretation env) := by
  intro m n within term
  rw [definition.unfold env n, definition.unfold env m]
  exact interpret_downward ghost definition.body.raw _ m n within term

/-- The bound variable's prefix closure agrees with its recursive body at every index. -/
theorem Definition.equation {depth : Nat} (definition : Definition ghost depth)
    (env : Environment) :
    interpret ghost (env.cons (definition.interpretation env)) definition.native.name.raw =
      interpret ghost (env.cons (definition.interpretation env)) definition.body.raw :=
  (prefixClosure_eq (definition.downward env)).trans (funext (definition.unfold env))

theorem Definition.guards {depth : Nat} (definition : Definition ghost depth)
    (env : Environment) (n : Nat) :
    let extended := env.cons (definition.interpretation env)
    interpretGuard ghost extended (.constr definition.native.name.raw definition.body.raw) n ∧
      interpretGuard ghost extended (.constr definition.body.raw definition.native.name.raw) n := by
  change Includes _ _ n ∧ Includes _ _ n
  rw [definition.equation env]
  exact ⟨fun _ _ _ => ⟨id, id⟩, fun _ _ _ => ⟨id, id⟩⟩

end CDotFCCT.CTML.Mixed
