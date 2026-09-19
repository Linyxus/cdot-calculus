import CDotFCCT.CTML.MixedRecordSystems

/-!
# Native CTML with ghost inversion and ordinary record guards

One fixed label policy governs both rules: ghost fields permit subtyping inversion;
ordinary record fields guard recursive occurrences. Terms and evaluation are native.
Both scalar recursive definitions and simultaneous ordinary-record groups are scoped.
-/

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTMLCore.Indexed

set_option autoImplicit true

mutual
  /-- Native CTML typing extended with local, guarded, equirecursive definitions.
  The ordinary constructors make recursive declarations usable in arbitrary term positions. -/
  inductive HasType (ghost : FieldName → Bool) : (s : SubtypingContext) →
      TypingContext s.typeDepth → Term → WFTy s.typeDepth → Prop where
    | native : CTMLCore.HasType s context term type → HasType ghost s context term type
    | subsumption :
        HasType ghost s context term sub → InvertingSubtype ghost s sub sup →
        HasType ghost s context term sup
    | abstraction :
        HasType ghost s (context.bind param) body ret →
        HasType ghost s context (.abs body) (WFTy.arrow param ret)
    | application :
        HasType ghost s context function (WFTy.arrow param ret) →
        HasType ghost s context argument param →
        HasType ghost s context (.app function argument) ret
    | record :
        FieldsHaveType ghost s context fields fieldTypes →
        HasType ghost s context (.record className fields) (recordResultType className fieldTypes)
    | projection :
        HasType ghost s context recordTerm (WFTy.record field type) →
        HasType ghost s context (.proj recordTerm field) type
    | ascription :
        HasType ghost s context term sub → InvertingSubtype ghost s sub sup →
        HasType ghost s context (.ascribe term sup.raw) sup
    | forall (context : TypingContext s.typeDepth)
        (term : Term) (body : WFTy (s.typeDepth + 1)) :
        Nonexpansive term → HasType ghost s.bindType context.bindType (term.liftTy 1) body →
        HasType ghost s context term (WFTy.all body)
    | constrained (guard : WFConstraint s.typeDepth) (body : WFTy s.typeDepth)
        (context : TypingContext s.typeDepth) (term : Term) :
        Nonexpansive term → HasType ghost (s.assume guard) context term body →
        HasType ghost s context term (WFTy.constrained guard body)
    | intersection :
        HasType ghost s context term left → HasType ghost s context term right →
        HasType ghost s context term (WFTy.intersection left right)
    | ifThen :
        HasType ghost s context scrutinee scrutineeType →
        InvertingSubtype ghost s scrutineeType (WFTy.cls className) →
        HasType ghost s (context.bind scrutineeType) thenBranch result →
        HasType ghost s context (.ifIs scrutinee className thenBranch elseBranch) result
    | ifElse :
        HasType ghost s context scrutinee scrutineeType →
        InvertingSubtype ghost s scrutineeType (WFTy.neg (WFTy.cls className)) →
        HasType ghost s (context.bind scrutineeType) elseBranch result →
        HasType ghost s context (.ifIs scrutinee className thenBranch elseBranch) result
    | fixpoint :
        HasType ghost s context function
          (WFTy.arrow (WFTy.arrow param ret) (WFTy.arrow param ret)) →
        HasType ghost s context (.fix function) (WFTy.arrow param ret)
    /-- `type α = F(α) in term`, erased at runtime. The answer does not mention `α`. -/
    | recursive (definition : Definition ghost s.typeDepth) :
        HasType ghost (definition.native.openContext s) context.bindType
          (term.liftTy 1) type.weaken →
      HasType ghost s context term type
    /-- A finite group of ordinary record equations shares one recursive scope. -/
    | recursiveRecordSystem (system : RecursiveRecordSystem s.typeDepth size)
        (ordinary : ∀ index, ghost (system.field index) = false) :
        HasType ghost (system.openContext s) (context.bindTypes size)
          (term.liftTy size) (type.weakenBy size) → HasType ghost s context term type

  /-- Native record fields may themselves contain local recursive type definitions. -/
  inductive FieldsHaveType (ghost : FieldName → Bool) :
      {names : List FieldName} → (s : SubtypingContext) →
      TypingContext s.typeDepth → TermFields names →
      List (FieldName × WFTy s.typeDepth) → Prop where
    | nil : FieldsHaveType ghost s context .nil []
    | cons :
        HasType ghost s context value type → FieldsHaveType ghost s context tail fieldTypes →
        FieldsHaveType ghost s context (.cons name value tail fresh) ((name, type) :: fieldTypes)
end

set_option autoImplicit false

variable {ghost : FieldName → Bool}

theorem HasType.var_in_scope {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {term : Term} {type : WFTy s.typeDepth}
    (typing : HasType ghost s context term type) (index : Nat) (isVar : term = .var index) :
    index < context.entries.length :=
  match typing with
  | .native typing => typing.var_in_scope index isVar
  | .subsumption typing _ => typing.var_in_scope index isVar
  | .abstraction _ | .application _ _ | .record _ | .projection _ | .ascription _ _ =>
      Term.noConfusion isVar
  | .forall _ _ _ _ typing => by
      exact Nat.lt_of_lt_of_eq
        (typing.var_in_scope index (congrArg (Term.liftTy 1) isVar)) (List.length_map ..)
  | .constrained _ _ _ _ _ typing => typing.var_in_scope index isVar
  | .intersection left _ => left.var_in_scope index isVar
  | .ifThen _ _ _ | .ifElse _ _ _ | .fixpoint _ => Term.noConfusion isVar
  | .recursive _ typing => by
      exact Nat.lt_of_lt_of_eq
        (typing.var_in_scope index (congrArg (Term.liftTy 1) isVar)) (List.length_map ..)
  | .recursiveRecordSystem _ _ typing => by
      exact Nat.lt_of_lt_of_eq
        (typing.var_in_scope index (congrArg (Term.liftTy _) isVar)) (List.length_map ..)

end CDotFCCT.CTML.Mixed
