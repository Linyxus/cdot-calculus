import CDotFCCT.CTML.MixedCalculus

/-!
# Safety with record-guarded recursion and ghost component inversion

The fundamental lemma covers all native terms, arbitrary constraints, universals,
Z, scalar record-guarded definitions and simultaneous record, function or pure carrier equations.
Only designated ghost labels admit component inversion. The runtime is unchanged.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTMLCore.Indexed

variable {ghost : FieldName → Bool}

mutual
  theorem nativeTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
      {term : Term} {type : WFTy s.typeDepth} (typing : CTMLCore.HasType s context term type) :
      Typing ghost s context term type :=
    match typing with
    | .var _ _ _ lookup => .var lookup
    | .subsumption h sub => (nativeTyping h).subsumption (.native sub)
    | .abstraction body => (nativeTyping body).abstraction
    | .application function argument => (nativeTyping function).application (nativeTyping argument)
    | .record fields => Typing.record (nativeFields fields) _
    | .projection record => (nativeTyping record).projection
    | .ascription h sub => (nativeTyping h).ascription (.native sub)
    | .forall _ _ _ nonexpansive body =>
        .forall nonexpansive
          (CTMLCore.HasType.var_in_scope (.forall _ _ _ nonexpansive body)) (nativeTyping body)
    | .constrained _ _ _ _ nonexpansive body =>
        .constrained nonexpansive body.var_in_scope (nativeTyping body)
    | .intersection left right => (nativeTyping left).intersection (nativeTyping right)
    | .ifThen scrutinee sub branch =>
        (nativeTyping scrutinee).ifThen (.native sub) (nativeTyping branch)
    | .ifElse scrutinee sub branch =>
        (nativeTyping scrutinee).ifElse (.native sub) (nativeTyping branch)
    | .fixpoint function => (nativeTyping function).fixpoint

  theorem nativeFields {s : SubtypingContext} {context : TypingContext s.typeDepth}
      {names : List FieldName} {fields : TermFields names}
      {types : List (FieldName × WFTy s.typeDepth)}
      (typing : CTMLCore.FieldsHaveType s context fields types) :
      FieldsTyping ghost s context fields types :=
    match typing with
    | .nil => .nil
    | .cons head tail => .cons (nativeTyping head) (nativeFields tail)
end

mutual
  theorem HasType.sound {s : SubtypingContext} {context : TypingContext s.typeDepth}
      {term : Term} {type : WFTy s.typeDepth} (typing : HasType ghost s context term type) :
      Typing ghost s context term type :=
    match typing with
    | .native h => nativeTyping h
    | .subsumption h sub => h.sound.subsumption sub
    | .abstraction body => body.sound.abstraction
    | .application function argument => function.sound.application argument.sound
    | .record fields => Typing.record fields.sound _
    | .projection record => record.sound.projection
    | .ascription h sub => h.sound.ascription sub
    | .forall _ _ _ nonexpansive body =>
        .forall nonexpansive
          (HasType.var_in_scope (.forall _ _ _ nonexpansive body)) body.sound
    | .constrained _ _ _ _ nonexpansive body =>
        .constrained nonexpansive body.var_in_scope body.sound
    | .intersection left right => left.sound.intersection right.sound
    | .ifThen scrutinee sub branch => scrutinee.sound.ifThen sub branch.sound
    | .ifElse scrutinee sub branch => scrutinee.sound.ifElse sub branch.sound
    | .fixpoint function => function.sound.fixpoint
    | .recursive definition body => body.sound.recursive definition
    | .recursiveSystem system body => body.sound.recursiveSystem system
    | .recursiveRecordSystem system ordinary body =>
        body.sound.recursiveRecordSystem system ordinary
    | .recursiveCarrierSystem system body => body.sound.recursiveCarrierSystem system
    | .recursiveCarrierRuntime system body => body.sound.recursiveCarrierRuntime system

  theorem FieldsHaveType.sound {s : SubtypingContext}
      {context : TypingContext s.typeDepth} {names : List FieldName} {fields : TermFields names}
      {types : List (FieldName × WFTy s.typeDepth)}
      (typing : FieldsHaveType ghost s context fields types) :
      FieldsTyping ghost s context fields types :=
    match typing with
    | .nil => .nil
    | .cons head tail => .cons head.sound tail.sound
end

theorem Typing.closed {term : Term} {type : WFTy 0}
    (typing : Typing ghost SubtypingContext.empty TypingContext.empty term type)
    (env : Indexed.Environment) (n : Nat) :
    Indexed.Computation (fun k => (interpret ghost env type.raw k).1) n term :=
  Indexed.instantiate_empty term ▸ typing env n Term.var
    (empty_validates ghost env n) (Valuation.empty env n Term.var)

theorem Typing.safe {term reached : Term} {type : WFTy 0}
    (typing : Typing ghost SubtypingContext.empty TypingContext.empty term type)
    (steps : Steps term reached) : Value reached ∨ ∃ next, Step reached next :=
  Indexed.Computation.safe (typing.closed (fun _ _ => (fun _ => False, fun _ => False))) steps

/-- Closed recursively typed programs cannot get stuck after any finite execution. -/
theorem HasType.safe {term reached : Term} {type : WFTy 0}
    (typing : HasType ghost SubtypingContext.empty TypingContext.empty term type)
    (steps : Steps term reached) : Value reached ∨ ∃ next, Step reached next :=
  typing.sound.safe steps

end CDotFCCT.CTML.Mixed
