import CDotFCCT.CTML.MixedGuardWeakening
import CDotFCCT.CTML.MixedCalculus

/-!
# Type-variable weakening through mixed recursive scopes

The fixed label policy is unchanged by type-variable insertion. Both subtyping and
term typing lift syntactically, including ghost inversion, universal constraints,
and all three forms of local recursive definitions. No semantic typing rule is added.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

variable {ghost : FieldName → Bool}

private theorem InvertingSubtype.castContextTo {s target : SubtypingContext} (equal : s = target)
    {sub sup : WFTy s.typeDepth} (targetSub targetSup : WFTy target.typeDepth)
    (subs : sub.raw = targetSub.raw) (sups : sup.raw = targetSup.raw)
    (h : InvertingSubtype ghost s sub sup) : InvertingSubtype ghost target targetSub targetSup := by
  cases equal
  exact (WFTy.eq_of_raw_eq subs) ▸ (WFTy.eq_of_raw_eq sups) ▸ h

theorem row_liftAt {depth : Nat} (labels : List FieldName) (types : FieldName → WFTy depth)
    (index : Nat) (valid : index ≤ depth) :
    (row labels types).liftAt index valid =
      row labels (fun field => (types field).liftAt index valid) := by
  induction labels with
  | nil => exact WFTy.liftAt_extremum valid _
  | cons field rest ih =>
      simp only [row, Transparent.row, WFTy.union, WFTy.liftAt_joint, WFTy.liftAt_record] at *
      exact congrArg (WFTy.joint .union (WFTy.record field ((types field).liftAt index valid))) ih

/-- Type-name insertion preserves reflective subtyping without adding any assumed bounds. -/
theorem InvertingSubtype.liftTypeAt {s : SubtypingContext} {sub sup : WFTy s.typeDepth}
    (h : InvertingSubtype ghost s sub sup) (index : Nat) (valid : index ≤ s.typeDepth) :
    InvertingSubtype ghost (s.insertTypeAt index valid)
      (sub.liftAt index valid) (sup.liftAt index valid) := by
  induction h generalizing index with
  | native h => exact .native (h.liftTypeAt index valid)
  | nativeWith guards h evidence ih =>
      refine .nativeWith _ (h.liftTypeAt index valid) ?_
      intro guard member
      obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
      dsimp only [SubtypingContext.insertTypeAt]
      rw [WFConstraint.liftAt_sub, WFConstraint.liftAt_sup]
      exact ih old present index valid
  | trans _ _ first second => exact .trans (first index valid) (second index valid)
  | inverse marked _ ih =>
      have lifted := ih index valid
      simp only [WFTy.liftAt_record] at lifted
      exact .inverse marked lifted
  | rowInverse reflective member _ ih =>
      have lifted := ih index valid
      rw [row_liftAt, row_liftAt] at lifted
      exact .rowInverse reflective member lifted
  | cut guard _ _ inferred body =>
      refine .cut (guard.liftAt index valid) ?_ ?_
      · dsimp only [SubtypingContext.insertTypeAt]
        rw [WFConstraint.liftAt_sub, WFConstraint.liftAt_sup]
        exact inferred index valid
      · exact InvertingSubtype.castContextTo
          (SubtypingContext.insertTypeAt_assume_comm _ index valid guard)
          _ _ rfl rfl (body index valid)
  | forallCovariant _ ih =>
      simp only [WFTy.liftAt_all]
      refine .forallCovariant ?_
      exact InvertingSubtype.castContextTo
        (SubtypingContext.insertTypeAt_bindType_comm _ index valid).symm
        _ _ rfl rfl (ih (index + 1) (Nat.add_le_add_right valid 1))
  | constrainedCovariant guard _ ih =>
      rename_i source sub sup bodyProof
      dsimp only [SubtypingContext.insertTypeAt]
      simp only [WFTy.liftAt_constrained]
      refine .constrainedCovariant (s := source.insertTypeAt index valid)
        (guard.liftAt index valid) ?_
      exact InvertingSubtype.castContextTo
        (SubtypingContext.insertTypeAt_assume_comm _ index valid guard)
        _ _ rfl rfl (ih index valid)

theorem InvertingSubtype.weakenType {s : SubtypingContext} {sub sup : WFTy s.typeDepth}
    (h : InvertingSubtype ghost s sub sup) :
    InvertingSubtype ghost s.bindType sub.weaken sup.weaken :=
  h.liftTypeAt 0 (Nat.zero_le s.typeDepth)

theorem InvertingSubtype.weakenTypes {s : SubtypingContext} {sub sup : WFTy s.typeDepth}
    (h : InvertingSubtype ghost s sub sup) (size : Nat) :
    InvertingSubtype ghost (s.bindTypes size) (sub.weakenBy size) (sup.weakenBy size) := by
  induction size with
  | zero =>
      exact InvertingSubtype.castContextTo s.bindTypes_zero.symm _ _
        (Ty.liftAt_zero 0 sub.raw).symm (Ty.liftAt_zero 0 sup.raw).symm h
  | succ size ih =>
      exact InvertingSubtype.castContextTo (s.bindTypes_succ size).symm _ _
        (Ty.liftAt_add sub.raw 0 size 1) (Ty.liftAt_add sup.raw 0 size 1) ih.weakenType

private theorem HasType.castContextTo {s target : SubtypingContext} (equal : s = target)
    {context : TypingContext s.typeDepth} (targetContext : TypingContext target.typeDepth)
    (contexts : HEq context targetContext) {term targetTerm : Term} (terms : term = targetTerm)
    {type : WFTy s.typeDepth} (targetType : WFTy target.typeDepth)
    (types : type.raw = targetType.raw) (h : HasType ghost s context term type) :
    HasType ghost target targetContext targetTerm targetType := by
  cases equal
  cases contexts
  cases terms
  exact (WFTy.eq_of_raw_eq types) ▸ h

mutual
  /-- A fresh type name can be inserted outside any local recursive declarations. -/
  theorem HasType.liftTypeAt {s : SubtypingContext} {context : TypingContext s.typeDepth}
      {term : Term} {type : WFTy s.typeDepth} (h : HasType ghost s context term type)
      (index : Nat) (valid : index ≤ s.typeDepth) :
      HasType ghost (s.insertTypeAt index valid) (context.insertTypeAt index valid)
        (term.liftTyAt index 1) (type.liftAt index valid) :=
    match h with
    | .native h => .native (h.liftTypeAt index valid)
    | .subsumption h sub => .subsumption (h.liftTypeAt index valid) (sub.liftTypeAt index valid)
    | .abstraction (param := param) h => by
        rw [WFTy.liftAt_arrow]
        exact .abstraction ((context.insertTypeAt_bind_comm index valid param) ▸
          h.liftTypeAt index valid)
    | .application function argument =>
        .application ((WFTy.liftAt_arrow valid _ _) ▸ function.liftTypeAt index valid)
          (argument.liftTypeAt index valid)
    | .record fields => by
        rw [recordResultType_liftAt]
        exact .record (fields.liftTypeAt index valid)
    | .projection record =>
        .projection ((WFTy.liftAt_record valid _ _) ▸ record.liftTypeAt index valid)
    | .ascription h sub => .ascription (h.liftTypeAt index valid) (sub.liftTypeAt index valid)
    | .forall context term body nonexpansive h => by
        rw [WFTy.liftAt_all]
        refine .forall _ _ _ (nonexpansive.liftTyAt index 1) ?_
        exact HasType.castContextTo
          (SubtypingContext.insertTypeAt_bindType_comm s index valid).symm
          ((context.insertTypeAt index valid).bindType)
          (heq_of_eq (TypingContext.insertTypeAt_bindType_comm context index valid).symm)
          (Term.liftTyAt_comm term index 0 (Nat.zero_le index)).symm
          (body.liftAt (index + 1) (Nat.add_le_add_right valid 1)) rfl
          (h.liftTypeAt (index + 1) (Nat.add_le_add_right valid 1))
    | .constrained guard body context term nonexpansive h => by
        rw [WFTy.liftAt_constrained]
        exact .constrained _ _ _ _ (nonexpansive.liftTyAt index 1)
          (HasType.castContextTo (SubtypingContext.insertTypeAt_assume_comm s index valid guard)
            (context.insertTypeAt index valid) HEq.rfl rfl (body.liftAt index valid) rfl
            (h.liftTypeAt index valid))
    | .intersection left right => by
        rw [WFTy.intersection, WFTy.liftAt_joint]
        exact .intersection (left.liftTypeAt index valid) (right.liftTypeAt index valid)
    | .ifThen (scrutineeType := scrutineeType) scrutinee sub branch =>
        .ifThen (scrutinee.liftTypeAt index valid)
          ((WFTy.liftAt_cls valid _) ▸ sub.liftTypeAt index valid)
          ((context.insertTypeAt_bind_comm index valid scrutineeType) ▸
            branch.liftTypeAt index valid)
    | .ifElse (scrutineeType := scrutineeType) scrutinee sub branch =>
        .ifElse (scrutinee.liftTypeAt index valid)
          ((WFTy.liftAt_neg valid _).trans (congrArg WFTy.neg (WFTy.liftAt_cls valid _)) ▸
            sub.liftTypeAt index valid)
          ((context.insertTypeAt_bind_comm index valid scrutineeType) ▸
            branch.liftTypeAt index valid)
    | .fixpoint function => by
        simp only [WFTy.liftAt_arrow] at *
        exact .fixpoint (function.liftTypeAt index valid)
    | .recursive definition h => by
        refine .recursive (definition.liftAt index valid) ?_
        exact HasType.castContextTo (Definition.openContext_liftAt s definition index valid)
          ((context.insertTypeAt index valid).bindType)
          (heq_of_eq (TypingContext.insertTypeAt_bindType_comm context index valid).symm)
          (Term.liftTyAt_comm term index 0 (Nat.zero_le index)).symm
          (type.liftAt index valid).weaken (congrArg WFTy.raw (WFTy.liftAt_weaken valid type))
          (h.liftTypeAt (index + 1) (Nat.add_le_add_right valid 1))
    | .recursiveSystem (size := size) system h => by
        refine .recursiveSystem (system.liftAt index valid) ?_
        exact HasType.castContextTo (system.openContext_liftAt s index valid)
          ((context.insertTypeAt index valid).bindTypes size)
          (context.insertTypeAt_bindTypes index size valid)
          (Term.liftTyAt_block_comm term index size).symm
          ((type.liftAt index valid).weakenBy size)
          (Ty.liftAt_block_comm type.raw index 0 size (Nat.zero_le index)).symm
          (h.liftTypeAt (index + size) (by change _ ≤ s.typeDepth + size; omega))

    | .recursiveRecordSystem (size := size) system ordinary h => by
        refine .recursiveRecordSystem (system.liftAt index valid) ordinary ?_
        exact HasType.castContextTo (system.openContext_liftAt s index valid)
          ((context.insertTypeAt index valid).bindTypes size)
          (context.insertTypeAt_bindTypes index size valid)
          (Term.liftTyAt_block_comm term index size).symm
          ((type.liftAt index valid).weakenBy size)
          (Ty.liftAt_block_comm type.raw index 0 size (Nat.zero_le index)).symm
          (h.liftTypeAt (index + size) (by change _ ≤ s.typeDepth + size; omega))

  theorem FieldsHaveType.liftTypeAt {s : SubtypingContext}
      {context : TypingContext s.typeDepth} {names : List FieldName} {fields : TermFields names}
      {types : List (FieldName × WFTy s.typeDepth)}
      (h : FieldsHaveType ghost s context fields types)
      (index : Nat) (valid : index ≤ s.typeDepth) :
      FieldsHaveType ghost (s.insertTypeAt index valid) (context.insertTypeAt index valid)
        (fields.liftTyAt index 1) (types.map fun field => (field.1, field.2.liftAt index valid)) :=
    match h with
    | .nil => .nil
    | .cons value rest => .cons (value.liftTypeAt index valid) (rest.liftTypeAt index valid)
end

theorem HasType.weakenType {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {term : Term} {type : WFTy s.typeDepth} (h : HasType ghost s context term type) :
    HasType ghost s.bindType context.bindType (term.liftTy 1) type.weaken :=
  h.liftTypeAt 0 (Nat.zero_le s.typeDepth)

theorem FieldsHaveType.weakenType {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {names : List FieldName} {fields : TermFields names}
    {types : List (FieldName × WFTy s.typeDepth)}
    (h : FieldsHaveType ghost s context fields types) :
    FieldsHaveType ghost s.bindType context.bindType (fields.liftTyAt 0 1)
      (types.map fun field => (field.1, field.2.weaken)) :=
  h.liftTypeAt 0 (Nat.zero_le s.typeDepth)

theorem HasType.weakenTypes {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {term : Term} {type : WFTy s.typeDepth} (h : HasType ghost s context term type) (size : Nat) :
    HasType ghost (s.bindTypes size) (context.bindTypes size) (term.liftTy size)
      (type.weakenBy size) := by
  induction size with
  | zero =>
      exact HasType.castContextTo s.bindTypes_zero.symm _
        (heq_of_eq context.bindTypes_zero.symm) (term.liftTyAt_zero 0).symm _
        (Ty.liftAt_zero 0 type.raw).symm h
  | succ size ih =>
      exact HasType.castContextTo (s.bindTypes_succ size).symm _
        (heq_of_eq (context.bindTypes_succ size).symm) (term.liftTyAt_add 0 size 1) _
        (type.raw.liftAt_add 0 size 1) ih.weakenType

end CDotFCCT.CTML.Mixed
