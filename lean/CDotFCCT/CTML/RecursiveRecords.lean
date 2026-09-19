import CDotFCCT.CTML.Records
import CTMLCore.Declarative.RecursiveTypes

/-!
# Record introduction through recursive declarations

DOT's path record-introduction rule remains admissible when the typing of the
projection opens guarded recursive types. The recursive names stay scoped in
the resulting record typing; no record encoding or new target rule is needed.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

private theorem projectionExpansive {record : Term} {field : FieldName} :
    ¬ Nonexpansive (.proj record field) := fun | .value value => nomatch value

private theorem recursiveProjectionInverseAux {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {term : Term} {type : WFTy s.typeDepth}
    (h : Recursive.HasType s context term type) :
    ∀ {record : Term} {field : FieldName}, term = .proj record field →
      Recursive.HasType s context record (WFTy.record field type) :=
  match h with
  | .native h => fun equal => .native (projectionInverse (equal ▸ h))
  | .subsumption h sub => fun equal =>
      (recursiveProjectionInverseAux h equal).subsumption (.record sub)
  | .intersection left right => fun equal =>
      (Recursive.HasType.intersection (recursiveProjectionInverseAux left equal)
        (recursiveProjectionInverseAux right equal)).subsumption
          (.recordDistribution .intersection)
  | .projection record => fun equal =>
      Term.proj.inj equal |>.1 ▸ (Term.proj.inj equal |>.2 ▸ record)
  | .recursive definition body => fun equal =>
      .recursive definition
        (recursiveProjectionInverseAux body (congrArg (Term.liftTy 1) equal))
  | .recursiveSystem (size := size) system body => fun equal =>
      .recursiveSystem system
        (recursiveProjectionInverseAux body (congrArg (Term.liftTy size) equal))
  | .forall _ _ _ nonexpansive _ => fun equal =>
      (projectionExpansive (equal ▸ nonexpansive)).elim
  | .constrained _ _ _ _ nonexpansive _ => fun equal =>
      (projectionExpansive (equal ▸ nonexpansive)).elim
  | .abstraction _ | .application _ _ | .record _ | .ascription _ _ |
      .ifThen _ _ _ | .ifElse _ _ _ | .fixpoint _ => fun equal => nomatch equal

/-- The target counterpart of DOT's record introduction, including recursive scopes. -/
theorem recursiveProjectionInverse {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {record : Term} {field : FieldName}
    {type : WFTy s.typeDepth} (h : Recursive.HasType s context (.proj record field) type) :
    Recursive.HasType s context record (WFTy.record field type) :=
  recursiveProjectionInverseAux h rfl

end CDotFCCT.CTML
