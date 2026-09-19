import CDotFCCT.TermCPS
import Mathlib.Data.List.Basic

/-!
# Finite label allocation

DOT's signature need not admit a global injection into strings. A compiler only
needs distinct target names for the finitely many labels in its input. This
allocation is deterministic and injective on a supplied finite support.
-/

set_option autoImplicit false

namespace CDotFCCT.TermCPS

variable [CDot.Signature]

def fieldName (labels : CDot.Fields) (label : CDot.Signature.TrmLabel) : String :=
  String.ofList (List.replicate (labels.idxOf label) 'f')

theorem fieldName_injective {labels : CDot.Fields} {left right : CDot.Signature.TrmLabel}
    (leftMember : left ∈ labels)
    (equal : fieldName labels left = fieldName labels right) : left = right := by
  have lengths := congrArg String.length equal
  simp only [fieldName, String.length_ofList, List.length_replicate] at lengths
  exact (List.idxOf_inj leftMember).mp lengths

def pathLabels : CDot.Path → CDot.Fields
  | .select _ fields => fields

mutual
  def termLabels : CDot.Trm → CDot.Fields
    | .val v => valueLabels v
    | .path p => pathLabels p
    | .app function argument => pathLabels function ++ pathLabels argument
    | .letE rhs body => termLabels rhs ++ termLabels body
    | .caseE p q _ left right =>
        pathLabels p ++ pathLabels q ++ termLabels left ++ termLabels right

  def valueLabels : CDot.Val → CDot.Fields
    | .lambda _ body => termLabels body
    | .new _ _ _ definitions => definitionsLabels definitions

  def definitionsLabels : CDot.Defs → CDot.Fields
    | .nil => []
    | .cons rest (.typ ..) => definitionsLabels rest
    | .cons rest (.trm label rhs) => definitionsLabels rest ++ label :: rhsLabels rhs

  def rhsLabels : CDot.DefRhs → CDot.Fields
    | .path p => pathLabels p
    | .val v => valueLabels v
end

/-- One fixed allocation is used throughout a program, including all nested objects. -/
def programEnv (free : CDot.Var → Nat) (term : CDot.Trm) : Env where
  free := free
  bound := id
  fieldName := fieldName (termLabels term)

end CDotFCCT.TermCPS
