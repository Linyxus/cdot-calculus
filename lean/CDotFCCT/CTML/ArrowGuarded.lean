import CTMLCore.Language.RecursiveTypes

/-!
# Recursion guarded by functions

Transparent records do not lower the observation index. Their payload therefore
inherits the guardedness obligation. This stricter predicate still admits native
recursive records with suspended fields and contravariant recursive occurrences.
It is separate from CTML's current `Ty.GuardedAt` predicate.
-/

set_option autoImplicit false

namespace CTMLCore.Syntax

mutual
  def Ty.ArrowGuardedAt (index : Nat) : Ty → Prop
    | .var found => found ≠ index
    | .extremum _ => True
    | .neg body => body.ArrowGuardedAt index
    | .joint _ left right => left.ArrowGuardedAt index ∧ right.ArrowGuardedAt index
    | .arrow _ _ => True
    | .cls _ => True
    | .record _ payload => payload.ArrowGuardedAt index
    | .all body => body.ArrowGuardedAt (index + 1)
    | .constrained guard body => guard.ArrowGuardedAt index ∧ body.ArrowGuardedAt index

  def Constraint.ArrowGuardedAt (index : Nat) : Constraint → Prop
    | .constr sub sup => sub.ArrowGuardedAt index ∧ sup.ArrowGuardedAt index
end

mutual
  theorem Ty.ArrowGuardedAt.guarded {type : Ty} {index : Nat}
      (guarded : type.ArrowGuardedAt index) : type.GuardedAt index :=
    match type with
    | .var _ => guarded
    | .extremum _ | .arrow _ _ | .cls _ | .record _ _ => trivial
    | .neg body => Ty.ArrowGuardedAt.guarded (type := body) guarded
    | .joint _ _ _ => ⟨guarded.1.guarded, guarded.2.guarded⟩
    | .all body => Ty.ArrowGuardedAt.guarded (type := body) (index := index + 1) guarded
    | .constrained _ _ => ⟨guarded.1.guarded, guarded.2.guarded⟩

  theorem Constraint.ArrowGuardedAt.guarded {guard : Constraint} {index : Nat}
      (guarded : guard.ArrowGuardedAt index) : guard.GuardedAt index :=
    match guard with
    | .constr _ _ => ⟨guarded.1.guarded, guarded.2.guarded⟩
end

end CTMLCore.Syntax

namespace CDotFCCT.CTML.Transparent

open CTMLCore CTMLCore.Syntax

structure Definition (depth : Nat) where
  body : WFTy (depth + 1)
  guarded : body.raw.ArrowGuardedAt 0

def Definition.native {depth : Nat} (definition : Definition depth) : RecursiveType depth :=
  ⟨definition.body, definition.guarded.guarded⟩

def Definition.arrow {depth : Nat} (param ret : WFTy (depth + 1)) : Definition depth :=
  ⟨WFTy.arrow param ret, trivial⟩

def Definition.record {depth : Nat} (field : FieldName) (payload : Definition depth) :
    Definition depth := ⟨WFTy.record field payload.body, payload.guarded⟩

end CDotFCCT.CTML.Transparent
