import CDotFCCT.CTML.MixedTyping
import CTMLCore.Declarative.IndexedBlocks

/-!
# Simultaneous native-record recursion in the mixed model

All equations retain their native record bodies. Their outer labels must be ordinary
runtime fields, which guard direct mutual recursion. Ghost carriers may occur anywhere
inside their payloads and retain their reflective interpretation. No arrow is required.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTMLCore.Indexed

namespace RecordSystem

variable (ghost : FieldName → Bool)

def operator {depth size : Nat} (system : RecursiveRecordSystem depth size)
    (env : Environment) (selves : Nat → Fin size → Observation) (n : Nat) :
    Fin size → Observation :=
  fun index => interpret ghost (env.prepend fun index k => selves k index)
    (system.body index).raw n

def solution {depth size : Nat} (system : RecursiveRecordSystem depth size)
    (env : Environment) : Nat → Fin size → Observation :=
  fixedPoint (operator ghost system env) (fun _ => (fun _ => False, fun _ => False))

def interpretation {depth size : Nat} (system : RecursiveRecordSystem depth size)
    (env : Environment) (index : Fin size) : Indexed.Candidate :=
  fun n => solution ghost system env n index

def environment {depth size : Nat} (system : RecursiveRecordSystem depth size)
    (env : Environment) : Environment := env.prepend (interpretation ghost system env)

variable {ghost}

theorem contractive {depth size : Nat} (system : RecursiveRecordSystem depth size)
    (ordinary : ∀ i, ghost (system.field i) = false) (env : Environment) :
    Contractive (operator ghost system env) :=
  fun n _ _ agree => funext fun index => record_guarded ghost (ordinary index) n _ _
    (fun _ smaller => interpret_congr ghost (system.payload index).raw
      (env.prepend_before agree smaller))

theorem unfold {depth size : Nat} (system : RecursiveRecordSystem depth size)
    (ordinary : ∀ i, ghost (system.field i) = false)
    (env : Environment) (index : Fin size) (n : Nat) :
    interpretation ghost system env index n =
      interpret ghost (environment ghost system env) (system.body index).raw n :=
  congrFun (fixedPoint_unfold (contractive system ordinary env) _ n) index

theorem downward {depth size : Nat} (system : RecursiveRecordSystem depth size)
    (ordinary : ∀ i, ghost (system.field i) = false)
    (env : Environment) (index : Fin size) :
    Downward (interpretation ghost system env index) := by
  intro m n within term
  rw [unfold system ordinary env index n, unfold system ordinary env index m]
  exact interpret_downward ghost (system.body index).raw _ m n within term

theorem equation {depth size : Nat} (system : RecursiveRecordSystem depth size)
    (ordinary : ∀ i, ghost (system.field i) = false) (env : Environment) (index : Fin size) :
    interpret ghost (environment ghost system env) (system.name index).raw =
      interpret ghost (environment ghost system env) (system.body index).raw := by
  change prefixClosure ((environment ghost system env) index) = _
  simp only [environment, Environment.prepend, dite_eq_left index.isLt]
  exact (prefixClosure_eq (downward system ordinary env index)).trans
    (funext (unfold system ordinary env index))

theorem guards {depth size : Nat} (system : RecursiveRecordSystem depth size)
    (ordinary : ∀ i, ghost (system.field i) = false)
    (env : Environment) (index : Fin size) (n : Nat) :
    interpretGuard ghost (environment ghost system env) (system.unfoldGuard index).raw n ∧
      interpretGuard ghost (environment ghost system env) (system.foldGuard index).raw n := by
  change Includes _ _ n ∧ Includes _ _ n
  rw [equation system ordinary env index]
  exact ⟨fun _ _ _ => ⟨id, id⟩, fun _ _ _ => ⟨id, id⟩⟩

/-- One solution validates every record equation together with all outer assumptions. -/
theorem validates {size : Nat} {s : SubtypingContext} {env : Environment} {n : Nat}
    (system : RecursiveRecordSystem s.typeDepth size)
    (ordinary : ∀ i, ghost (system.field i) = false) (valid : Validates ghost s env n) :
    Validates ghost (system.openContext s) (environment ghost system env) n := by
  intro guard membership
  rcases List.mem_append.mp membership with equation | outer
  · exact (List.mem_append.mp equation).elim
      (fun contains => match List.mem_ofFn.mp contains with
        | ⟨index, equal⟩ => equal ▸ (guards system ordinary env index n).1)
      (fun contains => match List.mem_ofFn.mp contains with
        | ⟨index, equal⟩ => equal ▸ (guards system ordinary env index n).2)
  obtain ⟨old, member, rfl⟩ := List.mem_map.mp outer
  exact congrFun (interpretGuard_liftAt ghost old.raw
    (env.prepend_lifted (interpretation ghost system env))) n ▸ valid old member

end RecordSystem

variable {ghost : FieldName → Bool}

theorem Valuation.bindTypes {depth size : Nat} {env : Environment}
    {context : TypingContext depth} {n : Nat} {substitute : Nat → Term}
    (valuation : Valuation ghost env context n substitute)
    (arguments : Fin size → Indexed.Candidate) :
    Valuation ghost (env.prepend arguments) (context.bindTypes size) n substitute := by
  intro index found lookup
  have mapped : (context.entries[index]?).map (WFTy.weakenBy size) = some found := by
    simpa only [TypingContext.bindTypes, List.getElem?_map] using lookup.eq_getElem?
  obtain ⟨old, get, rfl⟩ := Option.map_eq_some_iff.mp mapped
  change Value (substitute index) ∧
    (interpret ghost (env.prepend arguments) (old.raw.lift size) n).1 (substitute index)
  rw [interpret_liftAt ghost old.raw (env.prepend_lifted arguments)]
  exact valuation index old (TypingContext.Lookup.of_getElem? context.entries index old get)

/-- Closing a simultaneously solved record group erases all of its local type names. -/
theorem Typing.recursiveRecordSystem {size : Nat} {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {term : Term} {type : WFTy s.typeDepth}
    (system : RecursiveRecordSystem s.typeDepth size)
    (ordinary : ∀ i, ghost (system.field i) = false)
    (typing : Typing ghost (system.openContext s) (context.bindTypes size)
      (term.liftTy size) (type.weakenBy size)) :
    Typing ghost s context term type := by
  intro env n substitute valid valuation
  simpa only [RecordSystem.environment, Ty.lift,
    interpret_liftAt ghost type.raw
      (env.prepend_lifted (RecordSystem.interpretation ghost system env)),
    instantiate_liftTypes] using
    (show Computation (fun k =>
      (interpret ghost (RecordSystem.environment ghost system env) (type.raw.lift size) k).1) n
      (instantiate (s.typeDepth + size) substitute (term.liftTy size)) from
        typing (RecordSystem.environment ghost system env) n substitute
          (RecordSystem.validates system ordinary valid) (valuation.bindTypes _))

end CDotFCCT.CTML.Mixed
