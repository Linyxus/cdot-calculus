import CDotFCCT.FieldNames
import CDotFCCT.CTML.MixedCarrierBounds

/-!
# Generated runtime fields are disjoint from ghost carrier labels

The CPS pass uses nonempty strings of `f` for runtime fields. CarrierLayout uses
strings of `m`, including the empty string. Their separation holds independently
of either finite support, and therefore survives nested objects and member views.
-/

set_option autoImplicit false

namespace CDotFCCT.TermCPS

variable [CDot.Signature]

universe u

/-- Every generated runtime field is ordinary under the fixed mixed target policy. -/
theorem fieldName_ordinary (labels : CDot.Fields) (label : CDot.Signature.TrmLabel) :
    CTML.Mixed.carrierPolicy (fieldName labels label) = false := by
  simp [fieldName, CTML.Mixed.carrierPolicy]

/-- This separates a runtime field from every possible carrier code, regardless of support. -/
theorem fieldName_ne_carrierCode (labels : CDot.Fields) (label : CDot.Signature.TrmLabel)
    (index : Nat) (upper : Bool) :
    fieldName labels label ≠ CTML.Transparent.CarrierLayout.code index upper := by
  intro equal
  have conflict := congrArg CTML.Mixed.carrierPolicy equal
  simp only [fieldName_ordinary, CTML.Mixed.carrierPolicy_code] at conflict
  exact Bool.noConfusion conflict

theorem fieldName_ne_carrierName {Label : Type u} [DecidableEq Label]
    (labels : CDot.Fields) (label : CDot.Signature.TrmLabel)
    (support : List Label) (member : Label) (upper : Bool) :
    fieldName labels label ≠ CTML.Transparent.CarrierLayout.name support member upper :=
  fieldName_ne_carrierCode labels label (support.idxOf member) upper

/-- All runtime fields allocated by the actual program environment remain recursion guards. -/
theorem programEnv_ordinary (free : CDot.Var → Nat) (term : CDot.Trm)
    (label : CDot.Signature.TrmLabel) :
    CTML.Mixed.carrierPolicy ((programEnv free term).fieldName label) = false :=
  fieldName_ordinary (termLabels term) label

theorem programEnv_fieldName_injective (free : CDot.Var → Nat) (term : CDot.Trm)
    {left right : CDot.Signature.TrmLabel} (leftMember : left ∈ termLabels term)
    (equal : (programEnv free term).fieldName left = (programEnv free term).fieldName right) :
    left = right := fieldName_injective leftMember equal

theorem programEnv_ne_carrierName {Label : Type u} [DecidableEq Label]
    (free : CDot.Var → Nat) (term : CDot.Trm) (label : CDot.Signature.TrmLabel)
    (support : List Label) (member : Label) (upper : Bool) :
    (programEnv free term).fieldName label ≠
      CTML.Transparent.CarrierLayout.name support member upper :=
  fieldName_ne_carrierName (termLabels term) label support member upper

end CDotFCCT.TermCPS
