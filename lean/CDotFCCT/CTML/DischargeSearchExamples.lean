import CDotFCCT.CTML.DischargeSearch

/-! # Constraint discharge distinguishes proofs from deferred obligations -/

set_option autoImplicit false

namespace CDotFCCT.CTML.DischargeSearchExamples

open CTMLCore
open DischargeSearch

def name : WFTy 1 := WFTy.var 0 (by decide)
def cycle : SubtypingContext := ⟨1, [WFConstraint.constr name name]⟩
def impossible : WFConstraint 1 := WFConstraint.constr name WFTy.bottom

theorem originalDefers :
    (solveCut 40 (rigid cycle) impossible).map (fun delta => delta.fresh.map (·.raw)) =
      .ok [impossible.raw] := by decide +kernel

theorem rejectsDeferred :
    dischargeUsing (solveCut 40) (solveCut_sound 40) cycle impossible = .failed := by decide +kernel

theorem rejectsCycle : discharge 40 cycle impossible = .failed := by decide +kernel

def recordBound : WFTy 1 := WFTy.record "field" (WFTy.cls "Unit")
def alternative : SubtypingContext :=
  ⟨1, [WFConstraint.constr name name, WFConstraint.constr name recordBound]⟩
def fieldGoal : WFConstraint 1 := WFConstraint.constr name (WFTy.record "field" WFTy.top)

/-- Rejecting the cyclic attempt lets the next, usable bound establish the field type. -/
theorem triesAlternative :
    (discharge 40 alternative fieldGoal).map (fun _ => true) = .ok true := by decide +kernel

theorem preservesFuelExhaustion :
    dischargeAll 0 alternative [fieldGoal] = .fuelOut := by decide +kernel

def universalGoal : WFConstraint 0 :=
  WFConstraint.constr (WFTy.all name) (WFTy.cls "Unit")

theorem originalIntroducesName :
    (solveCut 40 (rigid SubtypingContext.empty) universalGoal).map (·.target) = .ok 1 := by
  decide +kernel

theorem rejectsFreshName :
    dischargeUsing (solveCut 40) (solveCut_sound 40) SubtypingContext.empty universalGoal =
      .failed := by decide +kernel

end CDotFCCT.CTML.DischargeSearchExamples
