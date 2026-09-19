import CDotFCCT.Existentials

/-! Existential witnesses for guarded recursive function equations, in arbitrary contexts. -/

set_option autoImplicit false

namespace CDotFCCT

open FCCT FCCT.Syntax

/-- `X = P(X) → Q(X)` as two ordinary FCCT constraints on the hidden witness. -/
def recursiveEquation {n : Nat} (param ret : WFTy (n + 1)) : List (WFConstraint (n + 1)) :=
  let witness := WFTy.var 0 (Nat.zero_lt_succ n)
  [WFConstraint.constr witness (WFTy.arrow param ret),
   WFConstraint.constr (WFTy.arrow param ret) witness]

/-- Negative occurrences, open parameters, and constrained/polymorphic components are allowed.
The outer arrow provides the guard needed by the target's recursive-type constructor. -/
theorem recursiveEquationSatisfies {subtyping : SubtypingContext}
    (param ret : WFTy (subtyping.typeDepth + 1)) :
    Satisfies subtyping
      ((recursiveEquation param ret).map (·.instantiate (WFTy.recArrow param ret))) := by
  change Satisfies subtyping
    [WFConstraint.constr (WFTy.recArrow param ret) (WFTy.unfoldRecArrow param ret),
     WFConstraint.constr (WFTy.unfoldRecArrow param ret) (WFTy.recArrow param ret)]
  simpa only [Satisfies, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, WFConstraint.sub, WFConstraint.sup, WFConstraint.constr]
    using And.intro (@Subtype.recUnfold subtyping param ret)
      (@Subtype.recFold subtyping param ret)

/-- Construct a package for a recursive member after checking its concrete payload. -/
theorem packRecursive {subtyping : SubtypingContext}
    {context : TypingContext subtyping.typeDepth} {value : Term}
    (param ret payload : WFTy (subtyping.typeDepth + 1)) (answer : WFTy subtyping.typeDepth)
    (hValue : HasType subtyping context value (payload.instantiate (WFTy.recArrow param ret))) :
    HasType subtyping context (pack value)
      (existsCPS (recursiveEquation param ret) payload answer) :=
  packTyping hValue (recursiveEquationSatisfies param ret)

end CDotFCCT
