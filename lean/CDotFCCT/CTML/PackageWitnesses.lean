import CDotFCCT.CTML.NegativeSelections
import CDotFCCT.CTML.InterfaceBind

/-!
# Exporting a member witness together with its package representation

An existential telescope can bind both an opaque member name `A` and its consumer
`K`, retaining the native equations `A ≤ K → R` and `K → R ≤ A`. Opening that
telescope constructs the representation evidence used by negative selections.
Packing proves both equations, including when `A` is a locally recursive package.

This augments the existing interface representation. It does not infer source
interfaces or assume that an arbitrary opaque type is equivalent to a package.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

namespace Coercion

structure PackageWitness (s : SubtypingContext) (answer witness : WFTy s.typeDepth) where
  consumer : WFTy s.typeDepth
  unfold : Subtype s witness (WFTy.arrow consumer answer)
  fold : Subtype s (WFTy.arrow consumer answer) witness

def PackageWitness.negative {s : SubtypingContext} {answer witness : WFTy s.typeDepth}
    (package : PackageWitness s answer witness) : NegativeWitness s answer witness :=
  ⟨WFTy.arrow package.consumer answer, .arrow _ _, package.unfold, package.fold⟩

def PackageWitness.interface (s : SubtypingContext) (interface : Interface s.typeDepth)
    (answer : WFTy s.typeDepth) : PackageWitness s answer (interface.package answer) :=
  ⟨interface.consumer answer, .refl, .refl⟩

def PackageWitness.recursive (s : SubtypingContext) (interface : Interface (s.typeDepth + 1))
    (answer : WFTy s.typeDepth) :
    PackageWitness ((recursivePackageDefinition interface answer).openContext s)
      answer.weaken (recursivePackageDefinition interface answer).name :=
  ⟨interface.consumer answer.weaken,
    (recursivePackageDefinition interface answer).unfold s,
    (recursivePackageDefinition interface answer).fold s⟩

def PackageWitness.weakenAssumption {s : SubtypingContext}
    {answer witness : WFTy s.typeDepth} (package : PackageWitness s answer witness)
    (guard : WFConstraint s.typeDepth) : PackageWitness (s.assume guard) answer witness :=
  ⟨package.consumer, package.unfold.weakenAssumption guard, package.fold.weakenAssumption guard⟩

theorem PackageWitness.select {s : SubtypingContext}
    {data carrier answer witness : WFTy s.typeDepth} (package : PackageWitness s answer witness)
    (precise : Subtype s (preciseMember data witness answer) carrier) :
    Subtype s (negativeSelector data carrier answer) witness :=
  negativeSelectorWitness package.unfold package.fold precise

end Coercion

namespace Interface

theorem liftAt_substAt_cancel {n : Nat} (interface : Interface n)
    (index : Nat) (valid : index ≤ n) (replacement : WFTy n) :
    (interface.liftAt index valid).substAt index valid replacement = interface :=
  match interface with
  | .payload type => by
      simpa only [liftAt, substAt] using congrArg Interface.payload
        (show (type.liftAt index valid).substAt index valid replacement = type from
          WFTy.eq_of_raw_eq (Ty.liftAt_substAt_cancel type.raw index replacement.raw))
  | .guard constraint rest => by
      simpa only [liftAt, substAt] using congrArg₂ Interface.guard
        (show (constraint.liftAt index valid).substAt index valid replacement = constraint from
          WFConstraint.eq_of_raw_eq
            (Constraint.liftAt_substAt_cancel constraint.raw index replacement.raw))
        (rest.liftAt_substAt_cancel index valid replacement)
  | .bind rest => by
      simpa only [liftAt, substAt] using congrArg Interface.bind
        (rest.liftAt_substAt_cancel (index + 1) (by omega) replacement.weaken)

def packageName {n : Nat} : WFTy (n + 2) := WFTy.var 0 (by omega)
def packageConsumer {n : Nat} : WFTy (n + 2) := WFTy.var 1 (by omega)

def packageUnfold {n : Nat} (answer : WFTy n) : WFConstraint (n + 2) :=
  WFConstraint.constr packageName (WFTy.arrow packageConsumer answer.weaken.weaken)

def packageFold {n : Nat} (answer : WFTy n) : WFConstraint (n + 2) :=
  WFConstraint.constr (WFTy.arrow packageConsumer answer.weaken.weaken) packageName

def packageScope (s : SubtypingContext) (answer : WFTy s.typeDepth) : SubtypingContext :=
  (s.bindType.bindType.assume (packageUnfold answer)).assume (packageFold answer)

/-- Opened packages provide their representation evidence from their own guards. -/
def packageEvidence (s : SubtypingContext) (answer : WFTy s.typeDepth) :
    Coercion.PackageWitness (packageScope s answer) answer.weaken.weaken packageName :=
  ⟨packageConsumer,
    @Subtype.hyp (packageScope s answer) (packageUnfold answer)
      (List.mem_cons_of_mem _ List.mem_cons_self),
    @Subtype.hyp (packageScope s answer) (packageFold answer) List.mem_cons_self⟩

/-- The consumer is outermost; the member keeps index zero in the remaining interface. -/
def bindPackageWitness {n : Nat} (answer : WFTy n) (rest : Interface (n + 1)) : Interface n :=
  .bind (.bind (.guard (packageUnfold answer)
    (.guard (packageFold answer) (rest.liftAt 1 (by omega)))))

def bindPackageWitnessInstance {s : SubtypingContext} {answer witness type : WFTy s.typeDepth}
    {rest : Interface (s.typeDepth + 1)} (package : Coercion.PackageWitness s answer witness)
    (inst : Instance s (rest.instantiate witness) type) :
    Instance s (bindPackageWitness answer rest) type := by
  refine .bind package.consumer ?_
  simp only [instantiate, substAt, liftAt_substAt_cancel]
  refine .bind witness ?_
  simp only [instantiate, substAt]
  change Instance s
    (.guard (WFConstraint.constr witness
      (WFTy.arrow (package.consumer.weaken.instantiate witness)
        ((answer.weaken.weaken.substAt 1 (by omega) package.consumer.weaken).instantiate witness)))
      (.guard (WFConstraint.constr
        (WFTy.arrow (package.consumer.weaken.instantiate witness)
          ((answer.weaken.weaken.substAt 1 (by omega) package.consumer.weaken).instantiate witness))
        witness) (rest.instantiate witness))) type
  rw [WFTy.substAt_weaken (Nat.zero_le s.typeDepth) answer.weaken package.consumer]
  simp only [WFTy.weaken_instantiate_cancel]
  change Instance s
    (.guard (WFConstraint.constr witness
      (WFTy.arrow package.consumer (answer.weaken.instantiate package.consumer)))
      (.guard (WFConstraint.constr
        (WFTy.arrow package.consumer (answer.weaken.instantiate package.consumer)) witness)
        (rest.instantiate witness))) type
  simp only [WFTy.weaken_instantiate_cancel]
  exact .guard package.unfold (.guard package.fold inst)

theorem bindPackageWitness_consumerTyping {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {answer result : WFTy s.typeDepth}
    {rest : Interface (s.typeDepth + 1)} {body : Term}
    (typing : (rest.liftAt 1 (by omega)).Opened (packageScope s answer).assumptions
      context.bindType.bindType ((body.liftTy 1).liftTy 1) result.weaken.weaken) :
    HasType s context (.abs body) ((bindPackageWitness answer rest).consumer result) :=
  (bindPackageWitness answer rest).consumerTyping typing

theorem bindPackageWitness_recursiveConsumerTyping {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {answer result : WFTy s.typeDepth}
    {rest : Interface (s.typeDepth + 1)} {body : Term}
    (typing : (rest.liftAt 1 (by omega)).RecursiveOpened (packageScope s answer).assumptions
      context.bindType.bindType ((body.liftTy 1).liftTy 1) result.weaken.weaken) :
    Recursive.HasType s context (.abs body) ((bindPackageWitness answer rest).consumer result) :=
  (bindPackageWitness answer rest).recursiveConsumerTyping typing

theorem bindPackageWitness_recursivePackTyping {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {answer result witness type : WFTy s.typeDepth}
    {rest : Interface (s.typeDepth + 1)} {value : Term}
    (package : Coercion.PackageWitness s answer witness)
    (inst : Instance s (rest.instantiate witness) type)
    (typing : Recursive.HasType s context value type) :
    Recursive.HasType s context (pack value) ((bindPackageWitness answer rest).package result) :=
  recursivePackTyping (bindPackageWitnessInstance package inst) typing

end Interface

end CDotFCCT.CTML
