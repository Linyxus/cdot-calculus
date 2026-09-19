import CDotFCCT.CoreDerivation
import CDotFCCT.CTML.RecursiveAliases

/-!
# Elaborating recursive member equations from source types

This is the structural type-declaration pass, not the general term compiler.
It reads actual DOT types, resolves self-member labels in one finite group,
and generates the negative equations consumed by `CTML.RecursiveAliases`.
The generated system proves both bounds of every successfully elaborated alias.

The pass supports top, bottom, intersections, fields, and arrows whose result
depends on the enclosing self but not on the arrow's argument. References under
arrows track self's shifted de Bruijn index. Unsupported types return `none`;
in particular, nested member binders, singleton types and general path-dependent
function results still belong to the remaining full translation work.

Fields and functions use native payload types. Their continuation wrapper keeps
each structural leaf negative; records are not Church encoded. Selections and
intersections remain outside that wrapper so the alias solver can see cycles.
-/

set_option autoImplicit false

namespace CDotFCCT.RecursiveAliasTranslation

open CTMLCore
open CTML.RecursiveAliases

variable [CDot.Signature]

def memberIndex {size : Nat} (labels : Fin size → CDot.Signature.TypLabel)
    (label : CDot.Signature.TypLabel) : Option (Fin size) :=
  (List.finRange size).find? (fun index => labels index == label)

def names {depth size : Nat} (index : Fin size) : WFTy (depth + size) :=
  WFTy.var index (Nat.lt_of_lt_of_le index.isLt (Nat.le_add_left _ _))

def type {depth size : Nat} (labels : Fin size → CDot.Signature.TypLabel)
    (fieldName : CDot.Signature.TrmLabel → String) (answer : WFTy depth)
    (self : Nat) : CDot.Typ → Option (Equation (depth + size) size)
  | .top => some (.arrow WFTy.bottom)
  | .bot => some (.arrow WFTy.top)
  | .path (.select (.bound index) []) label =>
      if index = self then Equation.reference <$> memberIndex labels label else none
  | .and left right => do
      return .intersection (← type labels fieldName answer self left)
        (← type labels fieldName answer self right)
  | .all param result => do
      let param ← type labels fieldName answer self param
      let result ← type labels fieldName answer (self + 1) result
      return .arrow (WFTy.arrow
        (WFTy.arrow (param.denote names (answer.weakenBy size))
          (result.denote names (answer.weakenBy size))) (answer.weakenBy size))
  | .rcd (.trm label body) => do
      let body ← type labels fieldName answer self body
      return .arrow (WFTy.arrow
        (WFTy.record (fieldName label) (body.denote names (answer.weakenBy size)))
        (answer.weakenBy size))
  | _ => none

/-- A successful pass retains the exact source-to-equation computation for every declaration. -/
structure Compiled {depth size : Nat} (labels : Fin size → CDot.Signature.TypLabel)
    (fieldName : CDot.Signature.TrmLabel → String) (answer : WFTy depth)
    (source : Fin size → CDot.Typ) where
  equations : Equations depth size
  computed : ∀ index, type labels fieldName answer 0 (source index) = some (equations index)

def compile {depth size : Nat} (labels : Fin size → CDot.Signature.TypLabel)
    (fieldName : CDot.Signature.TrmLabel → String) (answer : WFTy depth)
    (source : Fin size → CDot.Typ) : Option (Compiled labels fieldName answer source) :=
  if supported : ∀ index, (type labels fieldName answer 0 (source index)).isSome = true then
    some ⟨fun index => (type labels fieldName answer 0 (source index)).get (supported index),
      fun index => (Option.some_get (supported index)).symm⟩
  else none

namespace Compiled

variable {depth size : Nat} {labels : Fin size → CDot.Signature.TypLabel}
  {fieldName : CDot.Signature.TrmLabel → String} {answer : WFTy depth}
  {source : Fin size → CDot.Typ}

def system (compiled : Compiled labels fieldName answer source) : RecursiveSystem depth size :=
  CTML.RecursiveAliases.system compiled.equations answer

def interface (compiled : Compiled labels fieldName answer source)
    (payload : WFTy (depth + size)) : CTML.Interface depth :=
  CTML.RecursiveAliases.interface compiled.equations answer payload

def witness {s : SubtypingContext} {answer : WFTy s.typeDepth}
    (compiled : Compiled labels fieldName answer source) (index : Fin size) :
    CTML.Coercion.PackageWitness (compiled.system.openContext s) (answer.weakenBy size)
      (compiled.system.name index) := package s compiled.equations answer index

theorem unfold {s : SubtypingContext} {answer : WFTy s.typeDepth}
    (compiled : Compiled labels fieldName answer source) (index : Fin size) :
    Subtype (compiled.system.openContext s) (compiled.system.name index)
      ((compiled.equations index).denote names (answer.weakenBy size)) :=
  CTML.RecursiveAliases.unfold s compiled.equations answer index

theorem fold {s : SubtypingContext} {answer : WFTy s.typeDepth}
    (compiled : Compiled labels fieldName answer source) (index : Fin size) :
    Subtype (compiled.system.openContext s)
      ((compiled.equations index).denote names (answer.weakenBy size))
      (compiled.system.name index) :=
  CTML.RecursiveAliases.fold s compiled.equations answer index

/-- The shared telescope exports the original, unnormalized equations. -/
theorem packTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {answer : WFTy s.typeDepth} (compiled : Compiled labels fieldName answer source)
    (result : WFTy s.typeDepth) {term : CTMLCore.Syntax.Term} {payload : WFTy (s.typeDepth + size)}
    (typing : Recursive.HasType (compiled.system.openContext s) (context.bindTypes size)
      (term.liftTy size) payload) :
    Recursive.HasType s context (CTML.pack term) ((compiled.interface payload).package result) :=
  CTML.RecursiveAliases.packTyping compiled.equations answer result typing

end Compiled

end CDotFCCT.RecursiveAliasTranslation
