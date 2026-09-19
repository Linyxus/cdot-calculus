import CDotFCCT.CTML.CarrierEquationInterpretation
import CTMLCore.Language.RecursiveSystemBinding

/-!
# Moving outer variables across a finite carrier scope

Insertion affects only independent outer leaves. Recursive references and record
guards remain unchanged, so the generated equations can move beneath type binders.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierEquation

open CTMLCore CTMLCore.Syntax

variable {ghost : FieldName → Bool} {depth size : Nat}

def Expr.liftAt (expression : Expr ghost depth size) (index : Nat) (valid : index ≤ depth) :
    Expr ghost (depth + 1) size :=
  match expression with
  | .leaf type => .leaf (type.liftAt index valid)
  | .ref component => .ref component
  | .neg body => .neg (body.liftAt index valid)
  | .joint kind left right => .joint kind (left.liftAt index valid) (right.liftAt index valid)
  | .record field marked body => .record field marked (body.liftAt index valid)

theorem Expr.guarded_liftAt {expression : Expr ghost depth size}
    (guarded : expression.Guarded) (index : Nat) (valid : index ≤ depth) :
    (expression.liftAt index valid).Guarded :=
  match expression with
  | .leaf _ => trivial
  | .ref _ => guarded
  | .neg body => Expr.guarded_liftAt (expression := body) guarded index valid
  | .joint _ left right =>
      ⟨Expr.guarded_liftAt (expression := left) guarded.1 index valid,
        Expr.guarded_liftAt (expression := right) guarded.2 index valid⟩
  | .record _ _ _ => trivial

theorem Expr.compile_liftAt (expression : Expr ghost depth size)
    (index : Nat) (valid : index ≤ depth) :
    (expression.liftAt index valid).compile.raw =
      expression.compile.raw.liftAt (index + size) 1 := by
  induction expression with
  | leaf type => exact Ty.liftAt_block_comm type.raw index 0 size (Nat.zero_le index)
  | ref component =>
      simp [liftAt, compile, WFTy.var, Ty.liftAt, show ¬ index + size ≤ component by omega]
  | neg _ ih => exact congrArg Ty.neg ih
  | joint kind _ _ left right => exact congrArg₂ (Ty.joint kind) left right
  | record field _ _ ih => exact congrArg (Ty.record field) ih

def System.liftAt (system : System ghost depth size) (index : Nat) (valid : index ≤ depth) :
    System ghost (depth + 1) size where
  body component := (system.body component).liftAt index valid
  guarded component := Expr.guarded_liftAt (system.guarded component) index valid

theorem System.compile_liftAt (system : System ghost depth size) (index : Nat)
    (valid : index ≤ depth) (component : Fin size) :
    ((system.liftAt index valid).compile component).raw =
      (system.compile component).raw.liftAt (index + size) 1 :=
  (system.body component).compile_liftAt index valid

theorem System.openContext_liftAt (s : SubtypingContext)
    (system : System ghost s.typeDepth size) (index : Nat) (valid : index ≤ s.typeDepth) :
    (system.openContext s).insertTypeAt (index + size) (by change _ ≤ s.typeDepth + size; omega) =
      (system.liftAt index valid).openContext (s.insertTypeAt index valid) := by
  apply SubtypingContext.ext_raw (by
    simp only [System.openContext, SubtypingContext.insertTypeAt]
    omega)
  simp only [System.openContext, SubtypingContext.insertTypeAt, List.map_append, List.map_map,
    System.equations, List.map_ofFn, Function.comp_def]
  congr 1
  · congr 1
    all_goals refine congrArg List.ofFn (funext fun component => ?_)
    all_goals simp [System.unfoldGuard, System.foldGuard, System.name,
      WFConstraint.constr, WFConstraint.liftAt, WFTy.var, Constraint.liftAt,
      System.compile_liftAt, Ty.liftAt, show ¬ index + size ≤ component by omega]
  · exact List.map_congr_left fun guard _ =>
      (Constraint.liftAt_block_comm guard.raw index 0 size (Nat.zero_le index)).symm

end CDotFCCT.CTML.Mixed.CarrierEquation
