import CDotFCCT.CTML.TransparentTyping
import CTMLCore.Declarative.IndexedBlocks

/-!
# Simultaneous recursive witnesses with transparent records

The native `RecursiveSystem` syntax requires an outer function arrow in every
equation. That guard is also contractive in the transparent-record model, even
for mutual negative occurrences and constraints beneath the function arrow.
The names are solved and their scope is closed together.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Transparent

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTMLCore.Indexed

namespace System

def operator {depth size : Nat} (system : RecursiveSystem depth size) (env : Environment)
    (selves : Nat → Fin size → Observation) (n : Nat) : Fin size → Observation :=
  fun index => interpret (env.prepend fun index k => selves k index) (system.body index).raw n

theorem contractive {depth size : Nat} (system : RecursiveSystem depth size)
    (env : Environment) : Contractive (operator system env) :=
  fun _ _ _ agree => funext fun index => arrow_congr
    (fun _ smaller => interpret_congr (system.parameter index).raw
      (env.prepend_before agree smaller))
    (fun _ smaller => interpret_congr (system.result index).raw
      (env.prepend_before agree smaller))

def solution {depth size : Nat} (system : RecursiveSystem depth size)
    (env : Environment) : Nat → Fin size → Observation :=
  fixedPoint (operator system env) (fun _ => (fun _ => False, fun _ => False))

def interpretation {depth size : Nat} (system : RecursiveSystem depth size)
    (env : Environment) (index : Fin size) : Indexed.Candidate :=
  fun n => solution system env n index

def environment {depth size : Nat} (system : RecursiveSystem depth size)
    (env : Environment) : Environment := env.prepend (interpretation system env)

theorem unfold {depth size : Nat} (system : RecursiveSystem depth size)
    (env : Environment) (index : Fin size) (n : Nat) :
    interpretation system env index n =
      interpret (environment system env) (system.body index).raw n :=
  congrFun (fixedPoint_unfold (contractive system env) _ n) index

theorem downward {depth size : Nat} (system : RecursiveSystem depth size)
    (env : Environment) (index : Fin size) : Downward (interpretation system env index) := by
  intro m n within term
  rw [unfold system env index n, unfold system env index m]
  exact interpret_downward (system.body index).raw _ m n within term

theorem equation {depth size : Nat} (system : RecursiveSystem depth size)
    (env : Environment) (index : Fin size) :
    interpret (environment system env) (system.name index).raw =
      interpret (environment system env) (system.body index).raw := by
  change prefixClosure ((environment system env) index) = _
  simp only [environment, Environment.prepend, dite_eq_left index.isLt]
  exact (prefixClosure_eq (downward system env index)).trans
    (funext (unfold system env index))

theorem guards {depth size : Nat} (system : RecursiveSystem depth size)
    (env : Environment) (index : Fin size) (n : Nat) :
    interpretGuard (environment system env) (system.unfoldGuard index).raw n ∧
      interpretGuard (environment system env) (system.foldGuard index).raw n := by
  change Includes _ _ n ∧ Includes _ _ n
  rw [equation system env index]
  exact ⟨fun _ _ _ => ⟨id, id⟩, fun _ _ _ => ⟨id, id⟩⟩

/-- The simultaneous solution satisfies all equations and preserves every outer assumption. -/
theorem validates {size : Nat} {s : SubtypingContext} {env : Environment} {n : Nat}
    (system : RecursiveSystem s.typeDepth size) (valid : Validates s env n) :
    Validates (system.openContext s) (environment system env) n := by
  intro guard membership
  rcases List.mem_append.mp membership with equation | outer
  · exact (List.mem_append.mp equation).elim
      (fun contains => match List.mem_ofFn.mp contains with
        | ⟨index, equal⟩ => equal ▸ (guards system env index n).1)
      (fun contains => match List.mem_ofFn.mp contains with
        | ⟨index, equal⟩ => equal ▸ (guards system env index n).2)
  obtain ⟨old, member, rfl⟩ := List.mem_map.mp outer
  exact congrFun (interpretGuard_liftAt old.raw
    (env.prepend_lifted (interpretation system env))) n ▸ valid old member

theorem noCollapse {size : Nat} (system : RecursiveSystem 0 size) :
    ¬ InvertingSubtype (system.openContext SubtypingContext.empty) WFTy.top WFTy.bottom :=
  Transparent.noCollapse (validates system
    (empty_validates (fun _ _ => (fun _ => False, fun _ => False)) 0))

end System

theorem Valuation.bindTypes {depth size : Nat} {env : Environment}
    {context : TypingContext depth} {n : Nat} {substitute : Nat → Term}
    (valuation : Valuation env context n substitute) (arguments : Fin size → Indexed.Candidate) :
    Valuation (env.prepend arguments) (context.bindTypes size) n substitute := by
  intro index found lookup
  have mapped : (context.entries[index]?).map (WFTy.weakenBy size) = some found := by
    simpa only [TypingContext.bindTypes, List.getElem?_map] using lookup.eq_getElem?
  obtain ⟨old, get, rfl⟩ := Option.map_eq_some_iff.mp mapped
  change Value (substitute index) ∧
    (interpret (env.prepend arguments) (old.raw.lift size) n).1 (substitute index)
  rw [interpret_liftAt old.raw (env.prepend_lifted arguments)]
  exact valuation index old (TypingContext.Lookup.of_getElem? context.entries index old get)

theorem Typing.recursiveSystem {size : Nat} {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {term : Term} {type : WFTy s.typeDepth}
    (system : RecursiveSystem s.typeDepth size)
    (typing : Typing (system.openContext s) (context.bindTypes size)
      (term.liftTy size) (type.weakenBy size)) :
    Typing s context term type := by
  intro env n substitute valid valuation
  simpa only [System.environment, Ty.lift,
    interpret_liftAt type.raw (env.prepend_lifted (System.interpretation system env)),
    instantiate_liftTypes] using
    (show Computation (fun k =>
      (interpret (System.environment system env) (type.raw.lift size) k).1) n
      (instantiate (s.typeDepth + size) substitute (term.liftTy size)) from
        typing (System.environment system env) n substitute
          (System.validates system valid) (valuation.bindTypes _))

end CDotFCCT.CTML.Transparent
