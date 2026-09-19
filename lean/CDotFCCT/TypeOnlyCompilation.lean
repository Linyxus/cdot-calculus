import CDotFCCT.RecursiveAliasTranslation
import CDotFCCT.TermCPS

/-!
# The type-only object constructor case

This partial constructor pass takes a real `Core.Typing` derivation. If all
definitions are type members and their right-hand sides elaborate, it constructs
the target typing proof for the exact output of `TermCPS.compile`. All witnesses
and equation evidence are generated; the input has no target-typing premises.

The result type exports those members together through one CPS existential
interface. Its runtime payload is the native object thunk used by the general
CPS pass. `none` reports an unsupported constructor; it does not provide a
fallback for the still-unimplemented general typing translation.
-/

set_option autoImplicit false

namespace CDotFCCT.TypeOnlyCompilation

open CTMLCore CTMLCore.Syntax
open RecursiveAliasTranslation

variable [CDot.Signature]

inductive TypeOnly : CDot.Defs → Type where
  | nil : TypeOnly .nil
  | cons {definitions : CDot.Defs} (earlier : TypeOnly definitions)
      (label : CDot.Signature.TypLabel) (body : CDot.Typ) :
      TypeOnly (.cons definitions (.typ label body))

def TypeOnly.inspect : (definitions : CDot.Defs) → Option (TypeOnly definitions)
  | .nil => some .nil
  | .cons definitions (.typ label body) =>
      (fun earlier => .cons earlier label body) <$> inspect definitions
  | .cons _ (.trm ..) => none

def TypeOnly.entries {definitions : CDot.Defs} :
    TypeOnly definitions → List (CDot.Signature.TypLabel × CDot.Typ)
  | .nil => []
  | .cons earlier label body => earlier.entries ++ [(label, body)]

def TypeOnly.labels {definitions : CDot.Defs} (only : TypeOnly definitions) :
    Fin only.entries.length → CDot.Signature.TypLabel := fun index => (only.entries.get index).1

def TypeOnly.bodies {definitions : CDot.Defs} (only : TypeOnly definitions) :
    Fin only.entries.length → CDot.Typ := fun index => (only.entries.get index).2

theorem TypeOnly.fields_empty {definitions : CDot.Defs} (only : TypeOnly definitions)
    (env : TermCPS.Env) : TermCPS.fields env definitions = some [] := by
  induction only with
  | nil => rfl
  | cons earlier label body ih => exact ih

def objectThunk : Term := .fix (.abs (.abs (.record "DOT" .nil)))
def payload {depth : Nat} : WFTy depth := WFTy.arrow WFTy.top (WFTy.cls "DOT")

omit [CDot.Signature] in
theorem objectThunkTyping (s : SubtypingContext) (context : TypingContext s.typeDepth) :
    HasType s context objectThunk payload :=
  .fixpoint (.abstraction (.abstraction (.record .nil)))

theorem TypeOnly.computation {definitions : CDot.Defs} (only : TypeOnly definitions)
    (env : TermCPS.Env) (tag : CDot.Path) (label : CDot.Signature.TypLabel) (body : CDot.Typ) :
    TermCPS.computation env (.val (.new tag label body definitions)) =
      some (CTML.pack objectThunk) := by
  simp only [TermCPS.computation, TermCPS.run, TermCPS.value, only.fields_empty,
    Option.pure_def, CTML.pack, objectThunk]
  rfl

theorem TypeOnly.compile_eq {definitions : CDot.Defs} (only : TypeOnly definitions)
    (env : TermCPS.Env) {sourceContext : CDot.Ctx} {tag : CDot.Path}
    {label : CDot.Signature.TypLabel} {body result : CDot.Typ}
    (derivation : Core.Typing sourceContext (.val (.new tag label body definitions)) result) :
    TermCPS.compile env derivation = CTML.pack objectThunk := by
  simp only [TermCPS.compile, only.computation]
  rfl

structure Result (answer : WFTy 0) (env : TermCPS.Env)
    {sourceContext : CDot.Ctx} {tag : CDot.Path} {label : CDot.Signature.TypLabel}
    {body : CDot.Typ} {definitions : CDot.Defs}
    (derivation : Core.Typing sourceContext
      (.val (.new tag label body definitions)) (.bnd body)) where
  only : TypeOnly definitions
  members : Compiled only.labels env.fieldName answer only.bodies
  typing : Recursive.HasType SubtypingContext.empty TypingContext.empty
    (TermCPS.compile env derivation) ((members.interface payload).package answer)

/-- The supported object case constructs the term's actual target derivation. -/
def compile (answer : WFTy 0) (env : TermCPS.Env)
    {sourceContext : CDot.Ctx} {tag : CDot.Path} {label : CDot.Signature.TypLabel}
    {body : CDot.Typ} {definitions : CDot.Defs}
    (derivation : Core.Typing sourceContext (.val (.new tag label body definitions)) (.bnd body)) :
    Option (Result answer env derivation) := do
  let only ← TypeOnly.inspect definitions
  let members ← RecursiveAliasTranslation.compile only.labels env.fieldName answer only.bodies
  return ⟨only, members, by
    rw [only.compile_eq env derivation]
    exact Compiled.packTyping (s := SubtypingContext.empty) (context := TypingContext.empty)
      (term := objectThunk) members answer (.native (objectThunkTyping _ _))⟩

end CDotFCCT.TypeOnlyCompilation
