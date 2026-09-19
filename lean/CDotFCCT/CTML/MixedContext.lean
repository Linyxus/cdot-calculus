import CDotFCCT.CTML.MixedBinding
import CTMLCore.Language.Context

/-! # Context validity for the mixed-record interpretation -/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Indexed

variable (ghost : FieldName → Bool)

def Validates (context : SubtypingContext) (env : Environment) (n : Nat) : Prop :=
  ∀ guard ∈ context.assumptions, interpretGuard ghost env guard.raw n

variable {ghost}

theorem Validates.below {context : SubtypingContext} {env : Environment} {m n : Nat}
    (valid : Validates ghost context env n) (within : m ≤ n) : Validates ghost context env m :=
  fun guard member => interpretGuard_downward ghost guard.raw env within (valid guard member)

theorem Validates.assume {context : SubtypingContext} {env : Environment} {n : Nat}
    (valid : Validates ghost context env n) {guard : WFConstraint context.typeDepth}
    (holds : interpretGuard ghost env guard.raw n) : Validates ghost (context.assume guard) env n :=
  fun found member => (List.mem_cons.mp member).elim
    (fun equal => equal ▸ holds) (valid found)

theorem Validates.bindType {context : SubtypingContext} {env : Environment} {n : Nat}
    (valid : Validates ghost context env n) (argument : Candidate) :
    Validates ghost context.bindType (env.cons argument) n := by
  intro guard membership
  obtain ⟨old, member, rfl⟩ := List.mem_map.mp membership
  exact congrFun (interpretGuard_lift ghost old.raw env argument) n ▸ valid old member

variable (ghost)

theorem empty_validates (env : Environment) (n : Nat) :
    Validates ghost SubtypingContext.empty env n := fun _ member => nomatch member

theorem guard_iff {depth : Nat} (guard : WFConstraint depth) (env : Environment) (n : Nat) :
    interpretGuard ghost env guard.raw n ↔ Includes (interpret ghost env guard.sub.raw)
      (interpret ghost env guard.sup.raw) n := by
  obtain ⟨⟨sub, sup⟩, _⟩ := guard
  exact Iff.rfl

end CDotFCCT.CTML.Mixed
