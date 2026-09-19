import CDotFCCT.CTML.TransparentSystems

/-!
# Experimental CTML typing with record inversion

This separate judgment combines native Core terms, Z, and the inverting subtyping
relation with function-guarded recursive declarations. It does not add a constructor
to the current target's `Recursive.HasType` or permit its weaker recursion guard.
-/

namespace CDotFCCT.CTML.Transparent

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTMLCore.Indexed

set_option autoImplicit true

mutual
  /-- Native CTML typing extended with local, guarded, equirecursive definitions.
  The ordinary constructors make recursive declarations usable in arbitrary term positions. -/
  inductive HasType : (s : SubtypingContext) →
      TypingContext s.typeDepth → Term → WFTy s.typeDepth → Prop where
    | native : CTMLCore.HasType s context term type → HasType s context term type
    | subsumption :
        HasType s context term sub → InvertingSubtype s sub sup → HasType s context term sup
    | abstraction :
        HasType s (context.bind param) body ret →
        HasType s context (.abs body) (WFTy.arrow param ret)
    | application :
        HasType s context function (WFTy.arrow param ret) →
        HasType s context argument param → HasType s context (.app function argument) ret
    | record :
        FieldsHaveType s context fields fieldTypes →
        HasType s context (.record className fields) (recordResultType className fieldTypes)
    | projection :
        HasType s context recordTerm (WFTy.record field type) →
        HasType s context (.proj recordTerm field) type
    | ascription :
        HasType s context term sub → InvertingSubtype s sub sup →
        HasType s context (.ascribe term sup.raw) sup
    | forall (context : TypingContext s.typeDepth)
        (term : Term) (body : WFTy (s.typeDepth + 1)) :
        Nonexpansive term → HasType s.bindType context.bindType (term.liftTy 1) body →
        HasType s context term (WFTy.all body)
    | constrained (guard : WFConstraint s.typeDepth) (body : WFTy s.typeDepth)
        (context : TypingContext s.typeDepth) (term : Term) :
        Nonexpansive term → HasType (s.assume guard) context term body →
        HasType s context term (WFTy.constrained guard body)
    | intersection :
        HasType s context term left → HasType s context term right →
        HasType s context term (WFTy.intersection left right)
    | ifThen :
        HasType s context scrutinee scrutineeType →
        InvertingSubtype s scrutineeType (WFTy.cls className) →
        HasType s (context.bind scrutineeType) thenBranch result →
        HasType s context (.ifIs scrutinee className thenBranch elseBranch) result
    | ifElse :
        HasType s context scrutinee scrutineeType →
        InvertingSubtype s scrutineeType (WFTy.neg (WFTy.cls className)) →
        HasType s (context.bind scrutineeType) elseBranch result →
        HasType s context (.ifIs scrutinee className thenBranch elseBranch) result
    | fixpoint :
        HasType s context function
          (WFTy.arrow (WFTy.arrow param ret) (WFTy.arrow param ret)) →
        HasType s context (.fix function) (WFTy.arrow param ret)
    /-- `type α = F(α) in term`, erased at runtime. The answer does not mention `α`. -/
    | recursive (definition : Definition s.typeDepth) :
        HasType (definition.native.openContext s) context.bindType (term.liftTy 1) type.weaken →
      HasType s context term type
    /-- A finite group of function-guarded equations shares one recursive scope. -/
    | recursiveSystem (system : RecursiveSystem s.typeDepth size) :
        HasType (system.openContext s) (context.bindTypes size)
          (term.liftTy size) (type.weakenBy size) → HasType s context term type

  /-- Native record fields may themselves contain local recursive type definitions. -/
  inductive FieldsHaveType : {names : List FieldName} → (s : SubtypingContext) →
      TypingContext s.typeDepth → TermFields names →
      List (FieldName × WFTy s.typeDepth) → Prop where
    | nil : FieldsHaveType s context .nil []
    | cons :
        HasType s context value type → FieldsHaveType s context tail fieldTypes →
        FieldsHaveType s context (.cons name value tail fresh) ((name, type) :: fieldTypes)
end

set_option autoImplicit false

theorem HasType.var_in_scope {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {term : Term} {type : WFTy s.typeDepth}
    (typing : HasType s context term type) (index : Nat) (isVar : term = .var index) :
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
  | .recursiveSystem _ typing => by
      exact Nat.lt_of_lt_of_eq
        (typing.var_in_scope index (congrArg (Term.liftTy _) isVar)) (List.length_map ..)

end CDotFCCT.CTML.Transparent
