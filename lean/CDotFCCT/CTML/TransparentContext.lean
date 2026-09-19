import CDotFCCT.CTML.TransparentBinding
import CTMLCore.Language.Context

/-! # Context validity for the transparent-record interpretation -/

set_option autoImplicit false

namespace CDotFCCT.CTML.Transparent

open CTMLCore CTMLCore.Syntax CTMLCore.Indexed

def Validates (context : SubtypingContext) (env : Environment) (n : Nat) : Prop :=
  ∀ guard ∈ context.assumptions, interpretGuard env guard.raw n

theorem Validates.below {context : SubtypingContext} {env : Environment} {m n : Nat}
    (valid : Validates context env n) (within : m ≤ n) : Validates context env m :=
  fun guard member => interpretGuard_downward guard.raw env within (valid guard member)

theorem Validates.assume {context : SubtypingContext} {env : Environment} {n : Nat}
    (valid : Validates context env n) {guard : WFConstraint context.typeDepth}
    (holds : interpretGuard env guard.raw n) : Validates (context.assume guard) env n :=
  fun found member => (List.mem_cons.mp member).elim
    (fun equal => equal ▸ holds) (valid found)

theorem Validates.bindType {context : SubtypingContext} {env : Environment} {n : Nat}
    (valid : Validates context env n) (argument : Candidate) :
    Validates context.bindType (env.cons argument) n := by
  intro guard membership
  obtain ⟨old, member, rfl⟩ := List.mem_map.mp membership
  exact congrFun (interpretGuard_lift old.raw env argument) n ▸ valid old member

theorem empty_validates (env : Environment) (n : Nat) :
    Validates SubtypingContext.empty env n := fun _ member => nomatch member

theorem guard_iff {depth : Nat} (guard : WFConstraint depth) (env : Environment) (n : Nat) :
    interpretGuard env guard.raw n ↔ Includes (interpret env guard.sub.raw)
      (interpret env guard.sup.raw) n := by
  obtain ⟨⟨sub, sup⟩, _⟩ := guard
  exact Iff.rfl

end CDotFCCT.CTML.Transparent
