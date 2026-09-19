import CDotFCCT.CTML.MixedRecursion

/-!
# Local check: record guards and component inversion can coexist

The obstruction applies when the same record constructor is both an unrestricted
subtyping reflector and a recursion guard. This experiment separates the two jobs:
ordinary record fields retain the native delayed interpretation, while designated
ghost labels use the transparent interpretation. Only the latter admit inversion.

These local operator laws do not constitute a new calculus or its safety proof.
They settle the key contractiveness case without introducing a function arrow.
A full mixed interpretation must restrict inversion and guardedness by the same
label classification, and prove the remaining typing and subtyping rules sound.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.RecordGuardAnalysis

open CTMLCore CTMLCore.Syntax CTMLCore.Indexed

/-- Ordinary runtime record fields are recursion guards. -/
abbrev runtimeRecord := CTMLCore.Indexed.record

/-- Designated ghost fields reflect subtyping, but are not themselves guards. -/
abbrev ghostRecord := TransparentRecord.record

/-- A candidate transformer observes only the current finite prefix. -/
def Local (body : Candidate → Candidate) : Prop :=
  ∀ n left right, Agree n left right → body left n = body right n

/-- A runtime record guards every locally interpreted payload, including constraints. -/
theorem runtimeGuards {body : Candidate → Candidate} (locality : Local body)
    (field : FieldName) : Contractive (fun self => runtimeRecord field (body self)) :=
  fun _ left right agree => record_congr fun k smaller =>
    locality k left right (fun j within => agree j (Nat.lt_of_le_of_lt within smaller))

/-- Ghost labels preserve a guard provided by an ordinary record elsewhere on the cycle. -/
theorem ghostPreservesGuard {body : Candidate → Candidate} (guarded : Contractive body)
    (field : FieldName) : Contractive (fun self => ghostRecord field (body self)) :=
  TransparentRecord.guarded guarded field

/-- Ghost component inversion remains available for arbitrary (also recursive) payloads. -/
theorem ghostInverse {field : FieldName} {sub sup : Candidate} {n : Nat}
    (included : Includes (ghostRecord field sub) (ghostRecord field sup) n) :
    Includes sub sup n := TransparentRecord.inverse included

/-- `X = {next : ghost(member, X)}` is guarded entirely by a record constructor. -/
def recordCycle (next member : FieldName) (self : Candidate) : Candidate :=
  runtimeRecord next (ghostRecord member self)

theorem recordCycle_contractive (next member : FieldName) :
    Contractive (recordCycle next member) :=
  runtimeGuards (body := ghostRecord member)
    (fun _ _ _ agree => TransparentRecord.congr agree.at) next

/-- The mixed cycle has an actual finite-index fixed point satisfying its equation. -/
def recordSolution (next member : FieldName) : Candidate :=
  fixedPoint (recordCycle next member) (fun _ => False, fun _ => False)

theorem recordSolution_equation (next member : FieldName) (n : Nat) :
    recordSolution next member n = recordCycle next member (recordSolution next member) n :=
  fixedPoint_unfold (recordCycle_contractive next member) _ n

/-- Reversing the wrapper order still admits record-guarded recursion. -/
theorem ghostAroundRecord_contractive (member next : FieldName) :
    Contractive (fun self => ghostRecord member (runtimeRecord next self)) :=
  ghostPreservesGuard (runtimeGuards (fun _ _ _ agree => agree.at) next) member

/-- Reserve one ghost label, leaving ordinary source-field names as recursion guards. -/
def policy (field : FieldName) : Bool := field == "$member"

def selfType : WFTy 1 := WFTy.var 0 (by decide)

/-- The field itself guards the recursion; its payload is a bare recursive name. -/
def directNode : Mixed.Definition policy 0 :=
  .record "next" (by decide) selfType

/-- A reflective component can occur below an ordinary record guard. -/
def ghostNode : Mixed.Definition policy 0 :=
  .record "next" (by decide) (WFTy.record "$member" selfType)

/-- Recursive occurrences in arbitrary constraint endpoints are still admitted. -/
def constrainedNode : Mixed.Definition policy 0 :=
  .record "next" (by decide)
    (WFTy.constrained
      (WFConstraint.constr (WFTy.record "next" WFTy.top) selfType) WFTy.bottom)

/-- The complete mixed interpretation solves a directly record-guarded equation. -/
theorem directNode_equation (env : Environment) :
    Mixed.interpret policy (env.cons (directNode.interpretation env)) selfType.raw =
      Mixed.interpret policy (env.cons (directNode.interpretation env)) directNode.body.raw :=
  directNode.equation env

theorem constrainedNode_guards (env : Environment) (n : Nat) :
    let extended := env.cons (constrainedNode.interpretation env)
    Mixed.interpretGuard policy extended
      (.constr selfType.raw constrainedNode.body.raw) n ∧
      Mixed.interpretGuard policy extended
        (.constr constrainedNode.body.raw selfType.raw) n :=
  constrainedNode.guards env n

/-- The very same policy retains reflection at the separate ghost label. -/
theorem policy_reflects {sub sup : Candidate} {n : Nat}
    (included : Includes (Mixed.record policy "$member" sub)
      (Mixed.record policy "$member" sup) n) : Includes sub sup n :=
  Mixed.record_inverse policy (by decide) included

/-- Reflection cannot also be used to cancel an ordinary record recursion guard. -/
theorem ordinary_not_reflective : policy "next" = false := by decide

theorem ghost_alone_not_guarded :
    ¬ Mixed.GuardedAt policy 0 (.record "$member" (.var 0)) := by
  simp [Mixed.GuardedAt, policy]

end CDotFCCT.CTML.RecordGuardAnalysis
