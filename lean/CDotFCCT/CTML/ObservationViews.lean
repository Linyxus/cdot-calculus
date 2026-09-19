import CDotFCCT.CTML.Selections
import CTMLCore.Declarative.RecursiveAssumptions
import CTMLCore.Declarative.RecursiveTypeWeakening

/-!
# Retaining CPS views while adding a selected-member observation

An observation may be an intersection of CPS results, universally quantified, or
guarded by arbitrary constraints. A lower-bound conversion is uniformly the identity
at every existing result type, so its CPS mapping can retain all such observations.
This is a statement about observations, not an inversion of native record subtyping.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Coercion

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

def observation {n : Nat} (payload answer : WFTy n) : WFTy n :=
  WFTy.arrow (WFTy.arrow payload answer) answer

inductive Observation : {n : Nat} → WFTy n → WFTy n → Type where
  | result {n : Nat} (payload answer : WFTy n) :
      Observation answer (observation payload answer)
  | both {n : Nat} {answer left right : WFTy n} :
      Observation answer left → Observation answer right →
      Observation answer (WFTy.intersection left right)
  | all {n : Nat} {answer : WFTy n} {body : WFTy (n + 1)} :
      Observation answer.weaken body → Observation answer (WFTy.all body)
  | guarded {n : Nat} {answer body : WFTy n} (guard : WFConstraint n) :
      Observation answer body → Observation answer (WFTy.constrained guard body)

def selectorObservation {n : Nat} (data carrier answer : WFTy n) :
    Observation answer (selector data carrier answer) :=
  .all (.guarded _ (.result _ _))

private theorem reopenFresh (body : Ty) :
    (body.liftAt 1 1).substAt 0 (.var 0) = body := by
  rw [Ty.liftAt_one_eq_substWith.1, Ty.substAt, Ty.substWith_substWith.1]
  refine Eq.trans ?_ (Ty.substWith_id.1 body)
  exact congrArg body.substWith (funext fun | 0 => rfl | _ + 1 => rfl)

theorem openUniversal {s : SubtypingContext} (body : WFTy (s.typeDepth + 1)) :
    Subtype s.bindType (WFTy.all body).weaken body :=
  Eq.mp (congrArg (Subtype s.bindType (WFTy.all body).weaken)
    (show (body.liftAt 1 (Nat.le_add_left 1 s.typeDepth)).instantiate
        (WFTy.var 0 (Nat.zero_lt_succ s.typeDepth)) = body from
      WFTy.eq_of_raw_eq (reopenFresh body.raw)))
    (Subtype.forallLeft (context := s.bindType)
      (body := body.liftAt 1 (Nat.le_add_left 1 s.typeDepth))
      (argument := WFTy.var 0 (Nat.zero_lt_succ s.typeDepth)))

def mapLower (payload observed : Term) : Term :=
  .abs (.app (observed.lift 1)
    (.abs (.app (.app (.app memberLower ((payload.lift 1).lift 1)) (.var 0)) (.var 1))))

theorem mapLower_liftTy (payload observed : Term) :
    (mapLower payload observed).liftTy 1 =
      mapLower (payload.liftTy 1) (observed.liftTy 1) := by
  change Term.abs (.app ((observed.lift 1).liftTy 1)
    (.abs (.app (.app (.app memberLower (((payload.lift 1).lift 1).liftTy 1))
      (.var 0)) (.var 1)))) = _
  rw [← Term.liftTy_liftAt_comm observed 0 1 1,
    ← Term.liftTy_liftAt_comm (payload.lift 1) 0 1 1,
    ← Term.liftTy_liftAt_comm payload 0 1 1]
  rfl

theorem mapLower_result {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {payload observed : Term} {data result answer : WFTy s.typeDepth}
    (hd : HasType s context payload data)
    (ho : HasType s context observed (observation result answer)) :
    HasType s context (mapLower payload observed) (observation result answer) :=
  .abstraction (.application (ho.weakenFront (WFTy.arrow result answer))
    (.abstraction (.application (.application (.application
      (memberLowerTyping _ (preciseMemberOwnView s data result answer))
      ((hd.weakenFront (WFTy.arrow result answer)).weakenFront result))
      (.var _ 0 _ .here)) (.var _ 1 _ (.there .here)))))

private theorem Observation.retainAux {n : Nat} {answer type : WFTy n}
    (shape : Observation answer type) {assumptions : List (WFConstraint n)}
    {context : TypingContext n} {payload observed : Term} {data : WFTy n}
    (hd : HasType ⟨n, assumptions⟩ context payload data)
    (ho : HasType ⟨n, assumptions⟩ context observed type) :
    HasType ⟨n, assumptions⟩ context (mapLower payload observed) type :=
  match shape with
  | .result _ _ => mapLower_result hd ho
  | .both left right =>
      .intersection (left.retainAux hd (ho.subsumption .interLeft))
        (right.retainAux hd (ho.subsumption .interRight))
  | .all body =>
      .forall _ _ _ (.value (.abs _)) ((mapLower_liftTy payload observed).symm ▸
        body.retainAux hd.weakenType (ho.weakenType.subsumption (openUniversal _)))
  | .guarded guard body =>
      .constrained _ _ _ _ (.value (.abs _))
        (body.retainAux (assumptions := guard :: assumptions) (hd.weakenAssumption guard)
          ((ho.weakenAssumption guard).subsumption (@Subtype.constrainedLeft
            ⟨n, guard :: assumptions⟩ guard _
            (@Subtype.hyp ⟨n, guard :: assumptions⟩ guard List.mem_cons_self))))

theorem Observation.retain {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {answer type : WFTy s.typeDepth} (shape : Observation answer type)
    {payload observed : Term} {data : WFTy s.typeDepth}
    (hd : HasType s context payload data) (ho : HasType s context observed type) :
    HasType s context (mapLower payload observed) type :=
  shape.retainAux hd ho

theorem mapLower_select {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {payload observed : Term} {data carrier lower upper answer : WFTy s.typeDepth}
    (bound : Subtype s carrier (memberView lower upper answer))
    (hd : HasType s context payload data)
    (ho : HasType s context observed (observation lower answer)) :
    HasType s context (mapLower payload observed) (selector data carrier answer) := by
  refine .forall _ _ _ (.value (.abs _)) ?_
  rw [mapLower_liftTy]
  refine .constrained _ _ _ _ (.value (.abs _)) (.abstraction ?_)
  exact .application
    ((ho.weakenType.weakenAssumption _).weakenFront _)
    (.abstraction (.application (.application (.application
      (memberLowerTyping _ (lower := lower.weaken) (upper := upper.weaken)
        (.trans (selectorHyp s data carrier answer) (bound.weakenType.weakenAssumption _)))
      (((hd.weakenType.weakenAssumption _).weakenFront _).weakenFront _))
      (.var _ 0 _ .here)) (.var _ 1 _ (.there .here))))

/-- Adding a selected-type observation retains every view described by `shape`. -/
theorem mapLower_refinement {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {payload observed : Term} {data carrier lower upper answer original : WFTy s.typeDepth}
    (shape : Observation answer original)
    (bound : Subtype s carrier (memberView lower upper answer))
    (hd : HasType s context payload data)
    (old : HasType s context observed original)
    (lowerView : HasType s context observed (observation lower answer)) :
    HasType s context (mapLower payload observed)
      (WFTy.intersection original (selector data carrier answer)) :=
  .intersection (shape.retain hd old) (mapLower_select bound hd lowerView)

/-- A coherent observation passes one fixed value to any value continuation. -/
def Returns (observed value : Term) : Prop :=
  ∀ continuation, Value continuation →
    Steps (.app observed continuation) (.app continuation value)

theorem Returns.pack (value : Term) : Returns (CTML.pack value) value := by
  intro continuation hk
  refine .trans (.appBeta _ _ hk) ?_
  change Steps (.app continuation ((value.lift 1).substAt 0 continuation)) _
  simpa only [Term.lift_substAt_cancel] using (Steps.refl (term := .app continuation value))

theorem Returns.mapLower {payload observed value : Term} (returns : Returns observed value)
    (hd : Value payload) (hv : Value value) : Returns (mapLower payload observed) value := by
  intro continuation hk
  refine .trans (.appBeta _ _ hk) ?_
  change Steps (.app ((observed.lift 1).substAt 0 continuation)
    ((Term.abs (.app (.app (.app memberLower ((payload.lift 1).lift 1)) (.var 0))
      (.var 1))).substAt 0 continuation)) _
  rw [Term.lift_substAt_cancel, Term.substAt_abs]
  change Steps (.app observed (.abs (.app (.app (.app memberLower
    (((payload.lift 1).lift 1).substAt 1 (continuation.lift 1))) (.var 0))
      (continuation.lift 1)))) _
  rw [Term.lift_lift_substAt_one]
  refine (returns _ (.abs _)).trans' (.trans (.appBeta _ _ hv) ?_)
  change Steps (.app (.app (.app memberLower ((payload.lift 1).substAt 0 value)) value)
    ((continuation.lift 1).substAt 0 value)) _
  simpa only [Term.lift_substAt_cancel] using memberLowerSteps hd hv hk

/-- The observation payload may itself introduce scoped recursive types. -/
theorem mapLower_resultRecursive {s : SubtypingContext}
    {context : TypingContext s.typeDepth}
    {payload observed : Term} {data result answer : WFTy s.typeDepth}
    (hd : Recursive.HasType s context payload data)
    (ho : Recursive.HasType s context observed (observation result answer)) :
    Recursive.HasType s context (mapLower payload observed) (observation result answer) :=
  .abstraction (.application (ho.weakenFront (WFTy.arrow result answer))
    (.abstraction (.application (.application (.application
      (.native (memberLowerTyping _ (preciseMemberOwnView s data result answer)))
      ((hd.weakenFront (WFTy.arrow result answer)).weakenFront result))
      (.native (.var _ 0 _ .here))) (.native (.var _ 1 _ (.there .here))))))

private theorem Observation.retainRecursiveAux {n : Nat} {answer type : WFTy n}
    (shape : Observation answer type) {assumptions : List (WFConstraint n)}
    {context : TypingContext n} {payload observed : Term} {data : WFTy n}
    (hd : Recursive.HasType ⟨n, assumptions⟩ context payload data)
    (ho : Recursive.HasType ⟨n, assumptions⟩ context observed type) :
    Recursive.HasType ⟨n, assumptions⟩ context (mapLower payload observed) type :=
  match shape with
  | .result _ _ => mapLower_resultRecursive hd ho
  | .both left right =>
      .intersection (left.retainRecursiveAux hd (ho.subsumption .interLeft))
        (right.retainRecursiveAux hd (ho.subsumption .interRight))
  | .all body =>
      .forall _ _ _ (.value (.abs _)) ((mapLower_liftTy payload observed).symm ▸
        body.retainRecursiveAux hd.weakenType (ho.weakenType.subsumption (openUniversal _)))
  | .guarded guard body =>
      .constrained _ _ _ _ (.value (.abs _))
        (body.retainRecursiveAux (assumptions := guard :: assumptions)
          (hd.weakenAssumption guard)
          ((ho.weakenAssumption guard).subsumption (@Subtype.constrainedLeft
            ⟨n, guard :: assumptions⟩ guard _
            (@Subtype.hyp ⟨n, guard :: assumptions⟩ guard List.mem_cons_self))))

theorem Observation.retainRecursive {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {answer type : WFTy s.typeDepth}
    (shape : Observation answer type) {payload observed : Term} {data : WFTy s.typeDepth}
    (hd : Recursive.HasType s context payload data)
    (ho : Recursive.HasType s context observed type) :
    Recursive.HasType s context (mapLower payload observed) type :=
  shape.retainRecursiveAux hd ho

theorem mapLower_selectRecursive {s : SubtypingContext}
    {context : TypingContext s.typeDepth}
    {payload observed : Term} {data carrier lower upper answer : WFTy s.typeDepth}
    (bound : Subtype s carrier (memberView lower upper answer))
    (hd : Recursive.HasType s context payload data)
    (ho : Recursive.HasType s context observed (observation lower answer)) :
    Recursive.HasType s context (mapLower payload observed) (selector data carrier answer) := by
  refine .forall _ _ _ (.value (.abs _)) ?_
  rw [mapLower_liftTy]
  refine .constrained _ _ _ _ (.value (.abs _)) (.abstraction ?_)
  exact .application
    ((ho.weakenType.weakenAssumption _).weakenFront _)
    (.abstraction (.application (.application (.application
      (.native (memberLowerTyping _ (lower := lower.weaken) (upper := upper.weaken)
        (.trans (selectorHyp s data carrier answer) (bound.weakenType.weakenAssumption _))))
      (((hd.weakenType.weakenAssumption _).weakenFront _).weakenFront _))
      (.native (.var _ 0 _ .here))) (.native (.var _ 1 _ (.there .here)))))

theorem mapLower_refinementRecursive {s : SubtypingContext}
    {context : TypingContext s.typeDepth}
    {payload observed : Term} {data carrier lower upper answer original : WFTy s.typeDepth}
    (shape : Observation answer original)
    (bound : Subtype s carrier (memberView lower upper answer))
    (hd : Recursive.HasType s context payload data)
    (old : Recursive.HasType s context observed original)
    (lowerView : Recursive.HasType s context observed (observation lower answer)) :
    Recursive.HasType s context (mapLower payload observed)
      (WFTy.intersection original (selector data carrier answer)) :=
  .intersection (shape.retainRecursive hd old) (mapLower_selectRecursive bound hd lowerView)

end CDotFCCT.CTML.Coercion
