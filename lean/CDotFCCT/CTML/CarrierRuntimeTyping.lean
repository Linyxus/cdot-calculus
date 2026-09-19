import CDotFCCT.CTML.CarrierRuntimeScopes
import CDotFCCT.CTML.MixedRecordSystems

/-! # Closing mutually dependent runtime and carrier equations -/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTMLCore.Indexed

variable {ghost : FieldName → Bool}

theorem Typing.recursiveCarrierRuntime {runtimeSize carrierSize : Nat} {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {term : Term} {type : WFTy s.typeDepth}
    (system : CarrierRuntime.System ghost s.typeDepth runtimeSize carrierSize)
    (typing : Typing ghost (system.openContext s) (context.bindTypes system.size)
      (term.liftTy system.size) (type.weakenBy system.size)) : Typing ghost s context term type := by
  intro env n substitute valid valuation
  simpa only [system.environment_eq_prepend env, Ty.lift,
    interpret_liftAt ghost type.raw (env.prepend_lifted (system.values env)),
    instantiate_liftTypes] using
    (show Computation (fun k =>
      (interpret ghost (system.environment env) (type.raw.lift system.size) k).1) n
      (instantiate (s.typeDepth + system.size) substitute (term.liftTy system.size)) from
        typing (system.environment env) n substitute (system.validates valid)
          (system.environment_eq_prepend env ▸ valuation.bindTypes (system.values env)))

end CDotFCCT.CTML.Mixed
