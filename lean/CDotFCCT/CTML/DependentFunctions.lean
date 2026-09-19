import CDotFCCT.CTML.PackageSubtyping

/-!
# Dependent function interfaces after opening the argument's members

An argument's abstract member witness is quantified together with its bounds.
The result may mention that witness; only the CPS answer must remain outside its
scope. At a call, the same witness instantiates the parameter and the result.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

def computation {n : Nat} (type answer : WFTy n) : WFTy n :=
  WFTy.arrow (WFTy.arrow type answer) answer

def dependentArrow {n : Nat} (guards : List (WFConstraint (n + 1)))
    (param result : WFTy (n + 1)) : WFTy n :=
  WFTy.all (qualify guards (WFTy.arrow param result))

def dependentFunction {n : Nat} (guards : List (WFConstraint (n + 1)))
    (param result : WFTy (n + 1)) (answer : WFTy n) : WFTy n :=
  dependentArrow guards param (computation result answer.weaken)

def lambdaCPS (body : Term) : Term := .abs (.abs body)

theorem dependentAbstractionTyping {s : SubtypingContext}
    {context : TypingContext s.typeDepth}
    {guards : List (WFConstraint (s.typeDepth + 1))}
    {param result : WFTy (s.typeDepth + 1)} {body : Term}
    (hBody : HasType (assumeMany s.bindType guards) (context.bindType.bind param)
      (body.liftTy 1) result) :
    HasType s context (.abs body) (dependentArrow guards param result) :=
  .forall _ _ _ (.value (.abs _))
    (qualifyTyping guards (.value (.abs _)) (.abstraction hBody))

/-- A dependent body is checked with the argument and its continuation in scope. -/
theorem dependentLambdaTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {guards : List (WFConstraint (s.typeDepth + 1))}
    {param result : WFTy (s.typeDepth + 1)} {answer : WFTy s.typeDepth} {body : Term}
    (hBody : HasType (assumeMany s.bindType guards)
      ((context.bindType.bind param).bind (WFTy.arrow result answer.weaken))
      (body.liftTy 1) answer.weaken) :
    HasType s context (lambdaCPS body) (dependentFunction guards param result answer) :=
  .forall _ _ _ (.value (.abs _))
    (qualifyTyping guards (.value (.abs _)) (.abstraction (.abstraction hBody)))

theorem qualifiedInstance {s : SubtypingContext}
    {guards : List (WFConstraint (s.typeDepth + 1))} {body : WFTy (s.typeDepth + 1)}
    {witness : WFTy s.typeDepth}
    (evidence : Satisfies s (guards.map (·.instantiate witness))) :
    Subtype s (WFTy.all (qualify guards body)) (body.instantiate witness) := by
  refine .trans (Subtype.forallLeft (argument := witness)) ?_
  induction guards with
  | nil => exact .refl
  | cons guard guards ih =>
      change Subtype s (WFTy.constrained (guard.instantiate witness)
        ((qualify guards body).instantiate witness)) (body.instantiate witness)
      exact .trans (.constrainedLeft _ _ (evidence _ List.mem_cons_self))
        (ih (fun found membership => evidence found (List.mem_cons_of_mem _ membership)))

theorem dependentApplyTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {guards : List (WFConstraint (s.typeDepth + 1))}
    {param result : WFTy (s.typeDepth + 1)} {witness : WFTy s.typeDepth}
    {function argument : Term}
    (hFunction : HasType s context function (dependentArrow guards param result))
    (hArgument : HasType s context argument (param.instantiate witness))
    (evidence : Satisfies s (guards.map (·.instantiate witness))) :
    HasType s context (.app function argument) (result.instantiate witness) := by
  have specialized := hFunction.subsumption (qualifiedInstance evidence)
  change HasType s context function
    (WFTy.arrow (param.instantiate witness) (result.instantiate witness)) at specialized
  exact .application specialized hArgument

/-- A call shares the argument witness with its dependent result continuation. -/
theorem dependentCallTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {guards : List (WFConstraint (s.typeDepth + 1))}
    {param result : WFTy (s.typeDepth + 1)} {answer witness : WFTy s.typeDepth}
    {function argument continuation : Term}
    (hFunction : HasType s context function (dependentFunction guards param result answer))
    (hArgument : HasType s context argument (param.instantiate witness))
    (hContinuation : HasType s context continuation
      (WFTy.arrow (result.instantiate witness) answer))
    (evidence : Satisfies s (guards.map (·.instantiate witness))) :
    HasType s context (.app (.app function argument) continuation) answer := by
  have specialized := hFunction.subsumption (qualifiedInstance evidence)
  change HasType s context function
    (WFTy.arrow (param.instantiate witness)
      (computation (result.instantiate witness) (answer.weaken.instantiate witness))) at specialized
  rw [WFTy.weaken_instantiate_cancel] at specialized
  exact .application (.application specialized hArgument) hContinuation

end CDotFCCT.CTML
