import CDotFCCT.CTML.Interfaces

/-!
# Constraint-polymorphic interfaces with dependent results

The telescope used for existential payloads can also quantify a function's whole
arrow type. Both its parameter and result may refer to every witness. Instantiating
the telescope once therefore shares the caller's witnesses across both positions.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Interface

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

/-- Close a telescope by universally quantifying its witnesses and abstracting its guards. -/
def close {n : Nat} : Interface n → WFTy n
  | .payload type => type
  | .guard constraint rest => WFTy.constrained constraint rest.close
  | .bind rest => WFTy.all rest.close

theorem close_substAt {n : Nat} (interface : Interface (n + 1))
    (index : Nat) (valid : index ≤ n) (replacement : WFTy n) :
    interface.close.substAt index valid replacement =
      (interface.substAt index valid replacement).close :=
  match interface with
  | .payload _ => by simp only [close, substAt]
  | .guard constraint rest => by
      simpa only [close, substAt] using
        (WFTy.substAt_constrained valid constraint rest.close replacement).trans
          (congrArg (WFTy.constrained (constraint.substAt index valid replacement))
            (rest.close_substAt index valid replacement))
  | .bind rest => by
      simpa only [close, substAt] using
        (WFTy.substAt_all valid rest.close replacement).trans
          (congrArg WFTy.all (rest.close_substAt (index + 1) (by omega) replacement.weaken))

theorem close_instantiate {n : Nat} (interface : Interface (n + 1)) (witness : WFTy n) :
    interface.close.instantiate witness = (interface.instantiate witness).close :=
  interface.close_substAt 0 (Nat.zero_le n) witness

theorem Instance.closeSubtype {s : SubtypingContext} {interface : Interface s.typeDepth}
    {type : WFTy s.typeDepth} (inst : Instance s interface type) :
    Subtype s interface.close type :=
  match inst with
  | .payload _ => .refl
  | .guard evidence rest => .trans (.constrainedLeft _ _ evidence) rest.closeSubtype
  | .bind (rest := rest) witness inst =>
      .trans (.forallLeft (argument := witness))
        ((rest.close_instantiate witness).symm ▸ inst.closeSubtype)

/-- Check a term under all of the interface's abstract witnesses and assumptions. -/
def Check {n : Nat} (interface : Interface n) (assumptions : List (WFConstraint n))
    (context : TypingContext n) (term : Term) : Prop :=
  match interface with
  | .payload type => HasType ⟨n, assumptions⟩ context term type
  | .guard constraint rest => rest.Check (constraint :: assumptions) context term
  | .bind rest =>
      rest.Check (assumptions.map WFConstraint.weaken) context.bindType (term.liftTy 1)

private theorem introduceAux {n : Nat} (interface : Interface n)
    {assumptions : List (WFConstraint n)} {context : TypingContext n} {term : Term}
    (nonexpansive : Nonexpansive term) (typing : interface.Check assumptions context term) :
    HasType ⟨n, assumptions⟩ context term interface.close :=
  match interface with
  | .payload _ => typing
  | .guard constraint rest =>
      @HasType.constrained ⟨n, assumptions⟩ constraint rest.close context term nonexpansive
        (rest.introduceAux nonexpansive typing)
  | .bind rest =>
      .forall _ _ _ nonexpansive (rest.introduceAux (nonexpansive.liftTy 1) typing)

theorem introduce {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {term : Term} (interface : Interface s.typeDepth) (nonexpansive : Nonexpansive term)
    (typing : interface.Check s.assumptions context term) :
    HasType s context term interface.close :=
  interface.introduceAux nonexpansive typing

/-- One instantiation specializes both the argument and dependent result types. -/
theorem applyTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {interface : Interface s.typeDepth} {param result : WFTy s.typeDepth}
    {function argument : Term} (inst : Instance s interface (WFTy.arrow param result))
    (hFunction : HasType s context function interface.close)
    (hArgument : HasType s context argument param) :
    HasType s context (.app function argument) result :=
  .application (hFunction.subsumption inst.closeSubtype) hArgument

end CDotFCCT.CTML.Interface
