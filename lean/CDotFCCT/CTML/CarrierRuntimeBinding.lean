import CDotFCCT.CTML.CarrierRuntimeScopes
import CDotFCCT.CTML.CarrierEquationBinding
import CDotFCCT.CTML.MixedGuardWeakening

/-!
# Moving outer variables across coupled carrier and runtime scopes

The insertion lies outside both recursive blocks. It shifts carrier parameters
and runtime bodies while retaining their indices, ghost labels and mixed guards.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierRuntime

open CTMLCore CTMLCore.Syntax

variable {ghost : FieldName → Bool} {depth runtimeSize carrierSize : Nat}

private def castCarriers {source target size : Nat} (equal : source = target)
    (system : CarrierEquation.System ghost source size) :
    CarrierEquation.System ghost target size := equal ▸ system

private theorem compile_castCarriers {source target size : Nat} (equal : source = target)
    (system : CarrierEquation.System ghost source size) (component : Fin size) :
    ((castCarriers equal system).compile component).raw = (system.compile component).raw := by
  cases equal
  rfl

/-- Insert one fresh outer variable, outside all carrier and runtime names. -/
def System.liftAt (system : System ghost depth runtimeSize carrierSize)
    (index : Nat) (valid : index ≤ depth) : System ghost (depth + 1) runtimeSize carrierSize where
  carriers := castCarriers (by omega)
    (system.carriers.liftAt (index + runtimeSize) (Nat.add_le_add_right valid runtimeSize))
  body component :=
    ((system.body component).liftAt (index + system.size) (by simp only [System.size]; omega))
      |>.castDepth (by omega)
  guarded component name := by
    rw [WFTy.raw_castDepth]
    exact (system.guarded component name).liftAbove (by
      have within := name.isLt
      simp only [System.size]
      omega) 1

@[simp] theorem System.size_liftAt (system : System ghost depth runtimeSize carrierSize)
    (index : Nat) (valid : index ≤ depth) : (system.liftAt index valid).size = system.size := rfl

theorem System.carrier_compile_liftAt (system : System ghost depth runtimeSize carrierSize)
    (index : Nat) (valid : index ≤ depth) (component : Fin carrierSize) :
    ((system.liftAt index valid).carriers.compile component).raw =
      (system.carriers.compile component).raw.liftAt (index + system.size) 1 := by
  simp only [System.liftAt, compile_castCarriers, CarrierEquation.System.compile_liftAt,
    System.size, Nat.add_assoc]

theorem System.body_liftAt (system : System ghost depth runtimeSize carrierSize)
    (index : Nat) (valid : index ≤ depth) (component : Fin runtimeSize) :
    ((system.liftAt index valid).body component).raw =
      (system.body component).raw.liftAt (index + system.size) 1 := by
  simp only [System.liftAt, WFTy.raw_castDepth, WFTy.liftAt]

theorem System.bodyAt_liftAt (system : System ghost depth runtimeSize carrierSize)
    (index : Nat) (valid : index ≤ depth) (component : Fin system.size) :
    ((system.liftAt index valid).bodyAt component).raw =
      (system.bodyAt component).raw.liftAt (index + system.size) 1 := by
  by_cases carrier : component.val < carrierSize
  · simp only [System.bodyAt, dite_eq_left carrier, WFTy.raw_castDepth,
      System.carrier_compile_liftAt]
  · simp only [System.bodyAt, dite_eq_right carrier, WFTy.raw_castDepth, System.body_liftAt]

theorem System.openContext_liftAt (s : SubtypingContext)
    (system : System ghost s.typeDepth runtimeSize carrierSize)
    (index : Nat) (valid : index ≤ s.typeDepth) :
    (system.openContext s).insertTypeAt (index + system.size)
        (by change _ ≤ s.typeDepth + system.size; omega) =
      (system.liftAt index valid).openContext (s.insertTypeAt index valid) := by
  apply SubtypingContext.ext_raw (by
    simp only [System.openContext, SubtypingContext.insertTypeAt, System.size]
    omega)
  simp only [System.openContext, SubtypingContext.insertTypeAt, System.equations,
    List.map_append, List.map_map, List.map_ofFn, Function.comp_def]
  congr 1
  · congr 1
    all_goals refine congrArg List.ofFn (funext fun component => ?_)
    all_goals simp [System.unfoldGuard, System.foldGuard, System.name,
      WFConstraint.constr, WFConstraint.liftAt, WFTy.var, Constraint.liftAt,
      System.bodyAt_liftAt, Ty.liftAt,
      show ¬ index + system.size ≤ component from by omega]
  · exact List.map_congr_left fun guard _ =>
      (Constraint.liftAt_block_comm guard.raw index 0 system.size (Nat.zero_le index)).symm

end CDotFCCT.CTML.Mixed.CarrierRuntime
