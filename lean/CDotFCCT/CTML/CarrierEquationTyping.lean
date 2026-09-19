import CDotFCCT.CTML.CarrierEquationInterpretation
import CDotFCCT.CTML.MixedRecordSystems

/-!
# Closing a solved pure carrier scope

Both directions of each equation are generated from the finite structural solver.
The rule erases its local names and keeps the outer type and runtime term unchanged.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTMLCore.Indexed

variable {ghost : FieldName → Bool}

theorem Typing.recursiveCarrierSystem {size : Nat} {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {term : Term} {type : WFTy s.typeDepth}
    (system : CarrierEquation.System ghost s.typeDepth size)
    (typing : Typing ghost (system.openContext s) (context.bindTypes size)
      (term.liftTy size) (type.weakenBy size)) : Typing ghost s context term type := by
  intro env n substitute valid valuation
  simpa only [CarrierEquation.System.environment, Ty.lift,
    interpret_liftAt ghost type.raw (env.prepend_lifted (system.interpretation env)),
    instantiate_liftTypes] using
    (show Computation (fun k =>
      (interpret ghost (system.environment env) (type.raw.lift size) k).1) n
      (instantiate (s.typeDepth + size) substitute (term.liftTy size)) from
        typing (system.environment env) n substitute (system.validates valid)
          (valuation.bindTypes _))

end CDotFCCT.CTML.Mixed
