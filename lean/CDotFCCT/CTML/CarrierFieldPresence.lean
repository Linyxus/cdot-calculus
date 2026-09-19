import CDotFCCT.CTML.MixedCarrierPackages

/-!
# Runtime field bounds activated by explicit presence witnesses

The presence component is independent of the child carrier. Every allocated field
gets one constrained runtime bound: absent fields discharge it under `Top ≤ Bottom`,
while present fields use the shape of the generated runtime payload. Opening a field
requires evidence for its presence component, in addition to its child-carrier bound.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierFieldPresence

open CTMLCore CTMLCore.Syntax

universe u
variable {Label : Type u} [DecidableEq Label] {ghost : FieldName → Bool}

/-- The separate presence witness activates the runtime requirement. -/
def guard {depth : Nat} (presence : WFTy depth) : WFConstraint depth :=
  WFConstraint.constr WFTy.top presence

def invariant {depth : Nat} (presence shape : WFTy depth) : WFTy depth :=
  WFTy.constrained (guard presence) shape

/-- The field contains a complete package tied to the parent's fixed child carrier. -/
def runtimeShape {depth : Nat} (support : List Label) (payload : Label)
    (child : WFTy depth) (field : FieldName) (answer : WFTy depth) : WFTy depth :=
  WFTy.arrow (WFTy.cls "$Unit")
    (WFTy.record field ((CarrierLayout.interface support payload child).package answer))

/-- An absent field places no requirement on the actual runtime payload. -/
theorem absentNative {s : SubtypingContext} (payload shape : WFTy s.typeDepth) :
    Subtype s payload (invariant WFTy.bottom shape) := by
  refine .trans (.constrainedRight (guard WFTy.bottom) payload)
    (.constrainedCovariant (guard WFTy.bottom) payload shape ?_)
  exact .trans (.extremum .top) (.trans
    (@Subtype.hyp (s.assume (guard WFTy.bottom)) (guard WFTy.bottom) List.mem_cons_self)
    (.extremum .bottom))

/-- Absence is computed as `Bottom`; no runtime field bound is supplied by the caller. -/
theorem absent {s : SubtypingContext} (payload shape : WFTy s.typeDepth) :
    InvertingSubtype ghost s payload (invariant WFTy.bottom shape) :=
  .native (absentNative payload shape)

/-- The producer's actual field shape provides its conditional runtime invariant. -/
theorem fromShape {s : SubtypingContext} {payload shape : WFTy s.typeDepth}
    (presence : WFTy s.typeDepth) (actual : InvertingSubtype ghost s payload shape) :
    InvertingSubtype ghost s payload (invariant presence shape) :=
  actual.trans (.native (.constrainedRight (guard presence) shape))

/-- Presence is computed as `Top` when the producer supplies the runtime field. -/
theorem present {s : SubtypingContext} {payload shape : WFTy s.typeDepth}
    (actual : InvertingSubtype ghost s payload shape) :
    InvertingSubtype ghost s payload (invariant WFTy.top shape) :=
  fromShape WFTy.top actual

/-- Opening combines the separately extracted presence and uniform runtime bounds. -/
theorem extract {s : SubtypingContext} {payload presence shape : WFTy s.typeDepth}
    (uniform : InvertingSubtype ghost s payload (invariant presence shape))
    (present : InvertingSubtype ghost s WFTy.top presence) :
    InvertingSubtype ghost s payload shape :=
  uniform.trans (.constrainedLeft shape present)

/-- A producer allocates the marker independently of the chosen child carrier. -/
def marker {depth : Nat} (present : Bool) : WFTy depth :=
  if present then WFTy.top else WFTy.bottom

/-- Generate one invariant per allocated label; only actual fields need shape derivations. -/
theorem generate {s : SubtypingContext} (present : Bool) (payload shape : WFTy s.typeDepth)
    (actual : present = true → InvertingSubtype ghost s payload shape) :
    InvertingSubtype ghost s payload (invariant (marker present) shape) := by
  cases present with
  | false => exact absent payload shape
  | true => exact CarrierFieldPresence.present (actual rfl)

end CDotFCCT.CTML.Mixed.CarrierFieldPresence
