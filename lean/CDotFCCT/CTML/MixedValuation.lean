import CDotFCCT.CTML.MixedContext
import CTMLCore.Declarative.IndexedNonexpansive

/-! # Value substitutions for the mixed-record interpretation -/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTMLCore.Indexed

def Valuation (ghost : FieldName → Bool) {depth : Nat} (env : Environment)
    (context : TypingContext depth) (n : Nat) (substitute : Nat → Term) : Prop :=
  ∀ index type, TypingContext.Lookup context index type →
    Value (substitute index) ∧ (interpret ghost env type.raw n).1 (substitute index)

variable {ghost : FieldName → Bool}

theorem Valuation.below {depth : Nat} {env : Environment} {context : TypingContext depth}
    {m n : Nat} {substitute : Nat → Term} (valuation : Valuation ghost env context n substitute)
    (within : m ≤ n) : Valuation ghost env context m substitute :=
  fun index type lookup => ⟨(valuation index type lookup).1,
    ((interpret_downward ghost type.raw env m n within (substitute index)).1
      (valuation index type lookup).2)⟩

theorem Valuation.bind {depth : Nat} {env : Environment} {context : TypingContext depth}
    {n : Nat} {substitute : Nat → Term} (valuation : Valuation ghost env context n substitute)
    {type : WFTy depth} {term : Term} (value : Value term)
    (related : (interpret ghost env type.raw n).1 term) :
    Valuation ghost env (context.bind type) n
      (fun | 0 => term | index + 1 => substitute index) := by
  intro index found lookup
  cases index with
  | zero => exact Option.some.inj lookup.eq_getElem? ▸ ⟨value, related⟩
  | succ index =>
      exact valuation index found
        (TypingContext.Lookup.of_getElem? context.entries index found lookup.eq_getElem?)

theorem Valuation.bindType {depth : Nat} {env : Environment} {context : TypingContext depth}
    {n : Nat} {substitute : Nat → Term} (valuation : Valuation ghost env context n substitute)
    (argument : Indexed.Candidate) :
    Valuation ghost (env.cons argument) context.bindType n substitute := by
  intro index found lookup
  have mapped : (context.entries[index]?).map WFTy.weaken = some found := by
    simpa only [TypingContext.bindType, List.getElem?_map] using lookup.eq_getElem?
  obtain ⟨old, get, rfl⟩ := Option.map_eq_some_iff.mp mapped
  simpa only [WFTy.raw_weaken, interpret_lift] using
    valuation index old (TypingContext.Lookup.of_getElem? context.entries index old get)

theorem Valuation.empty (env : Environment) (n : Nat) {depth : Nat} (substitute : Nat → Term) :
    Valuation ghost env (TypingContext.empty (typeDepth := depth)) n substitute := by
  intro index found lookup
  exact False.elim (by simpa [TypingContext.empty] using lookup.eq_getElem?)

theorem Valuation.value_at {depth : Nat} {env : Environment}
    {context : TypingContext depth} {n : Nat} {substitute : Nat → Term}
    (valuation : Valuation ghost env context n substitute) (index : Nat)
    (within : index < context.entries.length) : Value (substitute index) :=
  (valuation index context.entries[index]
    (TypingContext.Lookup.of_getElem? context.entries index context.entries[index]
      (List.getElem?_eq_getElem within))).1

theorem nonexpansive_instantiate {depth : Nat} {env : Environment}
    {context : TypingContext depth} {n : Nat} {substitute : Nat → Term}
    (valuation : Valuation ghost env context n substitute) {term : Term}
    (nonexpansive : Nonexpansive term)
    (inScope : ∀ index, term = .var index → index < context.entries.length) :
    Value (instantiate depth substitute term) :=
  match nonexpansive with
  | .value value => Indexed.Value.instantiate value depth substitute
  | .var index => (instantiate_var depth substitute index).symm ▸
      valuation.value_at index (inScope index rfl)

end CDotFCCT.CTML.Mixed
