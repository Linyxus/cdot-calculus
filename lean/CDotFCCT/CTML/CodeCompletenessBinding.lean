import CDotFCCT.CTML.CodeCompleteness
import CTMLCore.Language.WellFormedAlgebra

/-!
# Transporting finite code-completeness certificates

Insertion and substitution change ambient type names and independent leaves.
Recursive references keep their finite indices, and the same ghost records guard
them. Every generated equation and occurring-leaf requirement moves with the
certificate; no completeness assumption is introduced by transport.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CodeCompleteness

open CTMLCore CTMLCore.Syntax

variable {ghost : FieldName → Bool} {depth target size : Nat}

def mapTypes (transform : WFTy depth → WFTy target) :
    CarrierEquation.Expr ghost depth size → CarrierEquation.Expr ghost target size
  | .leaf type => .leaf (transform type)
  | .ref component => .ref component
  | .neg body => .neg (mapTypes transform body)
  | .joint kind left right => .joint kind (mapTypes transform left) (mapTypes transform right)
  | .record field marked body => .record field marked (mapTypes transform body)

theorem mapTypes_guarded (transform : WFTy depth → WFTy target)
    {expression : CarrierEquation.Expr ghost depth size} (guarded : expression.Guarded) :
    (mapTypes transform expression).Guarded :=
  match expression with
  | .leaf _ => trivial
  | .ref _ => guarded
  | .neg body => mapTypes_guarded (expression := body) transform guarded
  | .joint _ left right =>
      ⟨mapTypes_guarded (expression := left) transform guarded.1,
        mapTypes_guarded (expression := right) transform guarded.2⟩
  | .record _ _ _ => trivial

def Schema.mapTypes (schema : Schema ghost depth size) (transform : WFTy depth → WFTy target) :
    Schema ghost target size where
  system :=
    { body := fun component => CodeCompleteness.mapTypes transform (schema.system.body component)
      guarded := fun component => mapTypes_guarded transform (schema.system.guarded component) }
  names component := transform (schema.names component)

def Schema.liftAt (schema : Schema ghost depth size) (index : Nat) (valid : index ≤ depth) :
    Schema ghost (depth + 1) size := schema.mapTypes (fun type => type.liftAt index valid)

def Schema.substAtDepth (schema : Schema ghost depth size) (index : Nat) (valid : index < depth)
    (replacement : WFTy (depth - 1)) : Schema ghost (depth - 1) size :=
  schema.mapTypes (fun type => type.substAtDepth index valid replacement)

theorem instantiate_liftAt (names : Fin size → WFTy depth)
    (expression : CarrierEquation.Expr ghost depth size) (index : Nat) (valid : index ≤ depth) :
    instantiate (fun component => (names component).liftAt index valid)
        (mapTypes (fun type => type.liftAt index valid) expression) =
      (instantiate names expression).liftAt index valid := by
  induction expression with
  | leaf _ | ref _ => rfl
  | neg _ ih => exact (congrArg WFTy.neg ih).trans (WFTy.liftAt_neg valid _).symm
  | joint kind _ _ left right =>
      exact (congrArg₂ (WFTy.joint kind) left right).trans (WFTy.liftAt_joint valid _ _ _).symm
  | record field _ _ ih =>
      exact (congrArg (WFTy.record field) ih).trans (WFTy.liftAt_record valid _ _).symm

theorem instantiate_substAtDepth (names : Fin size → WFTy depth)
    (expression : CarrierEquation.Expr ghost depth size) (index : Nat) (valid : index < depth)
    (replacement : WFTy (depth - 1)) :
    instantiate (fun component => (names component).substAtDepth index valid replacement)
        (mapTypes (fun type => type.substAtDepth index valid replacement) expression) =
      (instantiate names expression).substAtDepth index valid replacement := by
  induction expression with
  | leaf _ | ref _ => rfl
  | neg _ ih => exact (congrArg WFTy.neg ih).trans (WFTy.substAtDepth_neg valid _ _).symm
  | joint kind _ _ left right =>
      exact (congrArg₂ (WFTy.joint kind) left right).trans
        (WFTy.substAtDepth_joint valid _ _ _ _).symm
  | record field _ _ ih =>
      exact (congrArg (WFTy.record field) ih).trans (WFTy.substAtDepth_record valid _ _ _).symm

theorem complementGuard_liftAt (type : WFTy depth) (index : Nat) (valid : index ≤ depth) :
    ComplementedProduct.complementGuard (type.liftAt index valid) =
      (ComplementedProduct.complementGuard type).liftAt index valid :=
  WFConstraint.eq_of_raw_eq rfl

theorem complementGuard_substAtDepth (type : WFTy depth) (index : Nat) (valid : index < depth)
    (replacement : WFTy (depth - 1)) :
    ComplementedProduct.complementGuard (type.substAtDepth index valid replacement) =
      (ComplementedProduct.complementGuard type).substAtDepth index valid replacement :=
  WFConstraint.eq_of_raw_eq rfl

theorem leafGuards_liftAt (expression : CarrierEquation.Expr ghost depth size)
    (index : Nat) (valid : index ≤ depth) :
    leafGuards (mapTypes (fun type => type.liftAt index valid) expression) =
      (leafGuards expression).map (fun guard => guard.liftAt index valid) := by
  induction expression with
  | leaf type => exact congrArg List.singleton (complementGuard_liftAt type index valid)
  | ref _ => rfl
  | neg _ ih | record _ _ _ ih => exact ih
  | joint _ _ _ left right =>
      exact (congrArg₂ List.append left right).trans List.map_append.symm

theorem leafGuards_substAtDepth (expression : CarrierEquation.Expr ghost depth size)
    (index : Nat) (valid : index < depth) (replacement : WFTy (depth - 1)) :
    leafGuards (mapTypes (fun type => type.substAtDepth index valid replacement) expression) =
      (leafGuards expression).map (fun guard => guard.substAtDepth index valid replacement) := by
  induction expression with
  | leaf type =>
      exact congrArg List.singleton (complementGuard_substAtDepth type index valid replacement)
  | ref _ => rfl
  | neg _ ih | record _ _ _ ih => exact ih
  | joint _ _ _ left right =>
      exact (congrArg₂ List.append left right).trans List.map_append.symm

namespace Schema

theorem body_liftAt (schema : Schema ghost depth size) (index : Nat) (valid : index ≤ depth)
    (component : Fin size) :
    (schema.liftAt index valid).body component = (schema.body component).liftAt index valid :=
  instantiate_liftAt schema.names (schema.system.body component) index valid

theorem body_substAtDepth (schema : Schema ghost depth size) (index : Nat) (valid : index < depth)
    (replacement : WFTy (depth - 1)) (component : Fin size) :
    (schema.substAtDepth index valid replacement).body component =
      (schema.body component).substAtDepth index valid replacement :=
  instantiate_substAtDepth schema.names (schema.system.body component) index valid replacement

theorem unfoldGuard_liftAt (schema : Schema ghost depth size) (index : Nat) (valid : index ≤ depth)
    (component : Fin size) :
    (schema.liftAt index valid).unfoldGuard component =
      (schema.unfoldGuard component).liftAt index valid := by
  unfold unfoldGuard
  rw [body_liftAt]
  exact WFConstraint.eq_of_raw_eq rfl

theorem foldGuard_liftAt (schema : Schema ghost depth size) (index : Nat) (valid : index ≤ depth)
    (component : Fin size) :
    (schema.liftAt index valid).foldGuard component =
      (schema.foldGuard component).liftAt index valid := by
  unfold foldGuard
  rw [body_liftAt]
  exact WFConstraint.eq_of_raw_eq rfl

theorem unfoldGuard_substAtDepth (schema : Schema ghost depth size)
    (index : Nat) (valid : index < depth) (replacement : WFTy (depth - 1)) (component : Fin size) :
    (schema.substAtDepth index valid replacement).unfoldGuard component =
      (schema.unfoldGuard component).substAtDepth index valid replacement := by
  unfold unfoldGuard
  rw [body_substAtDepth]
  exact WFConstraint.eq_of_raw_eq rfl

theorem foldGuard_substAtDepth (schema : Schema ghost depth size)
    (index : Nat) (valid : index < depth) (replacement : WFTy (depth - 1)) (component : Fin size) :
    (schema.substAtDepth index valid replacement).foldGuard component =
      (schema.foldGuard component).substAtDepth index valid replacement := by
  unfold foldGuard
  rw [body_substAtDepth]
  exact WFConstraint.eq_of_raw_eq rfl

theorem equations_liftAt (schema : Schema ghost depth size) (index : Nat) (valid : index ≤ depth) :
    (schema.liftAt index valid).equations =
      schema.equations.map (fun guard => guard.liftAt index valid) := by
  simp only [equations, List.map_append, List.map_ofFn, Function.comp_def]
  exact congrArg₂ List.append
    (congrArg List.ofFn (funext (schema.unfoldGuard_liftAt index valid)))
    (congrArg List.ofFn (funext (schema.foldGuard_liftAt index valid)))

theorem equations_substAtDepth (schema : Schema ghost depth size)
    (index : Nat) (valid : index < depth) (replacement : WFTy (depth - 1)) :
    (schema.substAtDepth index valid replacement).equations =
      schema.equations.map (fun guard => guard.substAtDepth index valid replacement) := by
  simp only [equations, List.map_append, List.map_ofFn, Function.comp_def]
  exact congrArg₂ List.append
    (congrArg List.ofFn (funext (schema.unfoldGuard_substAtDepth index valid replacement)))
    (congrArg List.ofFn (funext (schema.foldGuard_substAtDepth index valid replacement)))

/-- Insertion maps exactly the original equation and occurring-leaf requirements. -/
theorem requirements_liftAt (schema : Schema ghost depth size)
    (index : Nat) (valid : index ≤ depth) :
    (schema.liftAt index valid).requirements =
      schema.requirements.map (fun guard => guard.liftAt index valid) := by
  simp only [requirements, equations_liftAt]
  simp only [Schema.liftAt, Schema.mapTypes,
    leafGuards_liftAt, List.map_append, List.map_flatten, List.map_ofFn, Function.comp_def]

/-- Substitution maps every certificate requirement, including the ambient name equations. -/
theorem requirements_substAtDepth (schema : Schema ghost depth size)
    (index : Nat) (valid : index < depth) (replacement : WFTy (depth - 1)) :
    (schema.substAtDepth index valid replacement).requirements =
      schema.requirements.map (fun guard => guard.substAtDepth index valid replacement) := by
  simp only [requirements, equations_substAtDepth]
  simp only [Schema.substAtDepth, Schema.mapTypes,
    leafGuards_substAtDepth, List.map_append, List.map_flatten, List.map_ofFn, Function.comp_def]

theorem conclusion_liftAt (schema : Schema ghost depth size) (index : Nat) (valid : index ≤ depth)
    (component : Fin size) :
    (schema.liftAt index valid).conclusion component =
      (schema.conclusion component).liftAt index valid :=
  complementGuard_liftAt (schema.names component) index valid

theorem conclusion_substAtDepth (schema : Schema ghost depth size)
    (index : Nat) (valid : index < depth) (replacement : WFTy (depth - 1)) (component : Fin size) :
    (schema.substAtDepth index valid replacement).conclusion component =
      (schema.conclusion component).substAtDepth index valid replacement :=
  complementGuard_substAtDepth (schema.names component) index valid replacement

end Schema

end CDotFCCT.CTML.Mixed.CodeCompleteness
