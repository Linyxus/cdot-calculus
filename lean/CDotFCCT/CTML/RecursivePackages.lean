import CDotFCCT.CTML.MutualPackageWitnesses

/-!
# Exporting a simultaneous recursive scope in one existential package

The interface binds every member before exposing the group's equations and its
native payload. Packing instantiates those binders at the group's existing names
and discharges every guard from its defining equations. No witness or equation
proof is supplied by the caller: only the payload's typing inside the scope is needed.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation Coercion

namespace Interface

/-- Close the most recent `size` names around one interface. -/
def bindBlock {depth : Nat} : (size : Nat) → Interface (depth + size) → Interface depth
  | 0, rest => rest
  | size + 1, rest => bindBlock size (.bind rest)

def guards {depth : Nat} (constraints : List (WFConstraint depth)) (rest : Interface depth) :
    Interface depth := constraints.foldr .guard rest

/-- Bind a common witness block around a payload and its requested constraints. -/
def closeGuards {depth : Nat} (size : Nat) (constraints : List (WFConstraint (depth + size)))
    (payload : WFTy (depth + size)) : Interface depth :=
  bindBlock size (guards constraints (.payload payload))

private theorem subtypeCast {s target : SubtypingContext} (equal : s = target)
    {sub sup : WFTy s.typeDepth} (targetSub targetSup : WFTy target.typeDepth)
    (subEqual : sub.raw = targetSub.raw) (supEqual : sup.raw = targetSup.raw)
    (typing : Subtype s sub sup) : Subtype target targetSub targetSup := by
  cases equal
  exact WFTy.eq_of_raw_eq subEqual ▸ WFTy.eq_of_raw_eq supEqual ▸ typing

/-- Instantiate each universal at the same fresh name that its binder introduced. -/
theorem bindBlock_open (s : SubtypingContext) (size : Nat)
    (rest : Interface (s.typeDepth + size)) (answer : WFTy s.typeDepth) :
    Subtype (s.bindTypes size) (((bindBlock size rest).consumer answer).weakenBy size)
      (rest.consumer (answer.weakenBy size)) := by
  induction size with
  | zero =>
      simp only [bindBlock, WFTy.weakenBy_zero]
      exact .refl
  | succ size ih =>
      have earlier := ih (.bind rest)
      have opened := CTMLCore.Subtype.trans earlier.weakenType
        (openUniversal (s := s.bindTypes size) (rest.consumer (answer.weakenBy size).weaken))
      exact subtypeCast (s.bindTypes_succ size).symm _ _
        (Ty.liftAt_add ((bindBlock size (.bind rest)).consumer answer).raw 0 size 1)
        (congrArg WFTy.raw (congrArg rest.consumer (answer.weakenBy_succ size).symm)) opened

theorem guards_open {s : SubtypingContext} (constraints : List (WFConstraint s.typeDepth))
    (rest : Interface s.typeDepth) (answer : WFTy s.typeDepth)
    (evidence : ∀ guard, guard ∈ constraints → Subtype s guard.sub guard.sup) :
    Subtype s ((guards constraints rest).consumer answer) (rest.consumer answer) := by
  induction constraints with
  | nil => exact .refl
  | cons guard tail ih =>
      exact .trans (.constrainedLeft _ _ (evidence guard List.mem_cons_self))
        (ih (fun found membership => evidence found (List.mem_cons_of_mem guard membership)))

end Interface

namespace RecursivePackage

def interface {depth size : Nat} (system : RecursiveSystem depth size)
    (payload : WFTy (depth + size)) : Interface depth :=
  Interface.bindBlock size (Interface.guards system.equations (.payload payload))

theorem pack_liftTypes (term : Term) (size : Nat) :
    (pack term).liftTy size = pack (term.liftTy size) :=
  congrArg (fun payload => Term.abs (.app (.var 0) payload))
    (Term.liftTy_liftAt_comm term 0 1 size).symm

/-- A constructor may export any guards proved in its recursive scope. -/
theorem consumerSubtypeWithGuards {s : SubtypingContext} {size : Nat}
    (system : RecursiveSystem s.typeDepth size)
    (constraints : List (WFConstraint (s.typeDepth + size)))
    (payload : WFTy (s.typeDepth + size)) (answer : WFTy s.typeDepth)
    (evidence : Satisfies (system.openContext s) constraints) :
    Subtype (system.openContext s)
      (((Interface.closeGuards size constraints payload).consumer answer).weakenBy size)
      (WFTy.arrow payload (answer.weakenBy size)) := by
  have opened := (Interface.bindBlock_open s size
    (Interface.guards constraints (.payload payload)) answer).mapAssumptions
      (target := (system.openContext s).assumptions)
      (fun guard member => @Subtype.hyp (system.openContext s) guard
        (List.mem_append_right _ member))
  exact .trans opened (Interface.guards_open _ _ _ evidence)

theorem packWithGuardsTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {size : Nat} (system : RecursiveSystem s.typeDepth size)
    (constraints : List (WFConstraint (s.typeDepth + size))) {term : Term}
    {payload : WFTy (s.typeDepth + size)} (answer : WFTy s.typeDepth)
    (evidence : Satisfies (system.openContext s) constraints)
    (typing : Recursive.HasType (system.openContext s) (context.bindTypes size)
      (term.liftTy size) payload) :
    Recursive.HasType s context (pack term)
      ((Interface.closeGuards size constraints payload).package answer) := by
  refine .recursiveSystem system ?_
  rw [pack_liftTypes]
  exact .abstraction (.application
    ((Recursive.HasType.native (HasType.var _ 0 _ .here)).subsumption
      (consumerSubtypeWithGuards system constraints payload answer evidence))
    (typing.weakenFront _))

/-- All exported witnesses are instantiated together; all defining equations are discharged. -/
theorem consumerSubtype {s : SubtypingContext} {size : Nat}
    (system : RecursiveSystem s.typeDepth size) (payload : WFTy (s.typeDepth + size))
    (answer : WFTy s.typeDepth) :
    Subtype (system.openContext s) (((interface system payload).consumer answer).weakenBy size)
      (WFTy.arrow payload (answer.weakenBy size)) :=
  consumerSubtypeWithGuards system system.equations payload answer
    (fun guard member => @Subtype.hyp (system.openContext s) guard
      (List.mem_append_left _ member))

/-- A constructor hides the entire recursive group using ordinary universal and guard types. -/
theorem packTyping {s : SubtypingContext} {context : TypingContext s.typeDepth} {size : Nat}
    (system : RecursiveSystem s.typeDepth size) {term : Term}
    {payload : WFTy (s.typeDepth + size)} (answer : WFTy s.typeDepth)
    (typing : Recursive.HasType (system.openContext s) (context.bindTypes size)
      (term.liftTy size) payload) :
    Recursive.HasType s context (pack term) ((interface system payload).package answer) :=
  packWithGuardsTyping system system.equations answer
    (fun guard member => @Subtype.hyp (system.openContext s) guard
      (List.mem_append_left _ member)) typing

end RecursivePackage

end CDotFCCT.CTML
