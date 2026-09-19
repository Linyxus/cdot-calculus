import CDotFCCT.CTML.MixedCalculus
import CTMLCore.Declarative.Substitution

/-!
# Term-variable weakening for the mixed target

Inserting a term binding preserves the fixed ghost-label policy, subtyping evidence,
and all recursive scopes. This structural lemma changes neither type-variable
bindings nor recursive equations. It supports packing arbitrary typed payloads into
continuation-encoded existentials without adding an administrative evaluation step.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

variable {ghost : FieldName → Bool}

mutual
  /-- Inserting a term binding preserves typing, including underneath recursive declarations. -/
  theorem HasType.weakenAt {s : SubtypingContext} {context : TypingContext s.typeDepth}
      {term : Term} {type : WFTy s.typeDepth} (h : HasType ghost s context term type)
      (pos : Nat) (extra : WFTy s.typeDepth) :
      HasType ghost s (context.insertAt pos extra) (term.liftAt pos 1) type :=
    match h with
    | .native h => .native (h.weakenAt pos extra)
    | .subsumption h sub => .subsumption (h.weakenAt pos extra) sub
    | .abstraction (param := param) h => by
        rw [Term.liftAt_abs]
        exact .abstraction ((context.insertAt_bind_comm pos extra param).symm ▸
          h.weakenAt (pos + 1) extra)
    | .application function argument =>
        .application (function.weakenAt pos extra) (argument.weakenAt pos extra)
    | .record fields => .record (fields.weakenAt pos extra)
    | .projection record => .projection (record.weakenAt pos extra)
    | .ascription h sub => .ascription (h.weakenAt pos extra) sub
    | .forall context term body nonexpansive h => by
        refine .forall _ _ _ (nonexpansive.liftAt pos 1) ?_
        rw [← Term.liftTy_liftAt_comm]
        exact (context.insertAt_bindType_comm pos extra).symm ▸ h.weakenAt pos extra.weaken
    | .constrained guard body _ _ nonexpansive h =>
        .constrained guard body _ _ (nonexpansive.liftAt pos 1) (h.weakenAt pos extra)
    | .intersection left right =>
        .intersection (left.weakenAt pos extra) (right.weakenAt pos extra)
    | .ifThen (scrutineeType := scrutineeType) scrutinee sub branch => by
        rw [Term.liftAt_ifIs]
        exact .ifThen (scrutinee.weakenAt pos extra) sub
          ((context.insertAt_bind_comm pos extra scrutineeType).symm ▸
            branch.weakenAt (pos + 1) extra)
    | .ifElse (scrutineeType := scrutineeType) scrutinee sub branch => by
        rw [Term.liftAt_ifIs]
        exact .ifElse (scrutinee.weakenAt pos extra) sub
          ((context.insertAt_bind_comm pos extra scrutineeType).symm ▸
            branch.weakenAt (pos + 1) extra)
    | .fixpoint function => .fixpoint (function.weakenAt pos extra)
    | .recursive definition h => by
        refine .recursive definition ?_
        rw [← Term.liftTy_liftAt_comm]
        exact (context.insertAt_bindType_comm pos extra).symm ▸ h.weakenAt pos extra.weaken
    | .recursiveSystem (size := size) system h => by
        refine .recursiveSystem system ?_
        rw [← Term.liftTy_liftAt_comm]
        exact (context.insertAt_bindTypes pos size extra).symm ▸
          h.weakenAt pos (extra.weakenBy size)

    | .recursiveRecordSystem (size := size) system ordinary h => by
        refine .recursiveRecordSystem system ordinary ?_
        rw [← Term.liftTy_liftAt_comm]
        exact (context.insertAt_bindTypes pos size extra).symm ▸
          h.weakenAt pos (extra.weakenBy size)

    | .recursiveCarrierSystem (size := size) system h => by
        refine .recursiveCarrierSystem system ?_
        rw [← Term.liftTy_liftAt_comm]
        exact (context.insertAt_bindTypes pos size extra).symm ▸
          h.weakenAt pos (extra.weakenBy size)

    | .recursiveCarrierRuntime system h => by
        refine .recursiveCarrierRuntime system ?_
        rw [← Term.liftTy_liftAt_comm]
        exact (context.insertAt_bindTypes pos system.size extra).symm ▸
          h.weakenAt pos (extra.weakenBy system.size)

  theorem FieldsHaveType.weakenAt {s : SubtypingContext} {context : TypingContext s.typeDepth}
      {names : List FieldName} {fields : TermFields names}
      {types : List (FieldName × WFTy s.typeDepth)}
      (h : FieldsHaveType ghost s context fields types)
      (pos : Nat) (extra : WFTy s.typeDepth) :
      FieldsHaveType ghost s (context.insertAt pos extra) (fields.liftAt pos 1) types :=
    match h with
    | .nil => .nil
    | .cons value rest => .cons (value.weakenAt pos extra) (rest.weakenAt pos extra)
end

theorem HasType.weakenFront {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {term : Term} {type : WFTy s.typeDepth} (h : HasType ghost s context term type)
    (extra : WFTy s.typeDepth) :
    HasType ghost s (context.bind extra) (term.lift 1) type :=
  context.insertAt_zero extra ▸ h.weakenAt 0 extra

theorem FieldsHaveType.weakenFront {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {names : List FieldName} {fields : TermFields names}
    {types : List (FieldName × WFTy s.typeDepth)}
    (h : FieldsHaveType ghost s context fields types) (extra : WFTy s.typeDepth) :
    FieldsHaveType ghost s (context.bind extra) (fields.lift 1) types :=
  context.insertAt_zero extra ▸ h.weakenAt 0 extra

end CDotFCCT.CTML.Mixed
