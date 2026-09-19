import CDotFCCT.CarrierSharedWitness
import CDotFCCT.CTML.MixedCarrierBounds

/-!
# Shared witnesses coexist with record-guarded recursion

The exact two source-binding guards from CarrierSharedWitness are reused here.
One fixed ghost-label policy recovers both bounds on the same `p.A` witness, while
ordinary `next` fields guard recursive types directly. No new member-bound
assumptions or function guards are inserted into either check.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.SharedWitness

open CTMLCore CTMLCore.Syntax CDotFCCT.CarrierSharedWitness

/-- Every slot allocated for the source labels is reflective under the same fixed policy. -/
theorem reflective : ∀ field ∈ labels, carrierPolicy field = true :=
  carrierPolicy_names support

theorem qTyping : InvertingSubtype carrierPolicy context preciseQ ownerType :=
  .native (@CTMLCore.Subtype.hyp context qBinding
    (List.mem_cons_of_mem pBinding List.mem_cons_self))

theorem pTyping : InvertingSubtype carrierPolicy context preciseP selectedX :=
  .native (@CTMLCore.Subtype.hyp context pBinding List.mem_cons_self)

theorem qAsSlot : InvertingSubtype carrierPolicy context
    (memberX.precise selectedX (Transparent.CarrierLayout.components support support qWitness))
    ownerType :=
  Transparent.CarrierLayout.precise_eq_slot (support := support) (label := "X")
    (by decide) qWitness ▸ qTyping

theorem pAsSlot : InvertingSubtype carrierPolicy context
    (memberA.precise selectedA (Transparent.CarrierLayout.components support support pWitness))
    selectedX :=
  Transparent.CarrierLayout.precise_eq_slot (support := support) (label := "A")
    (by decide) pWitness ▸ pTyping

/-- Both views go through one abstract `q.X`, exactly as in the original source context. -/
theorem upperTopView : InvertingSubtype carrierPolicy context selectedX topView :=
  memberUpperBound memberX reflective (.native .refl) (qAsSlot.trans (.native .interLeft))

theorem upperBottomView : InvertingSubtype carrierPolicy context selectedX bottomView :=
  memberUpperBound memberX reflective (.native .refl) (qAsSlot.trans (.native .interRight))

theorem selectedLower : InvertingSubtype carrierPolicy context WFTy.top selectedA :=
  memberLowerBound memberA reflective pAsSlot upperTopView

theorem selectedUpper : InvertingSubtype carrierPolicy context selectedA WFTy.bottom :=
  memberUpperBound memberA reflective pAsSlot upperBottomView

/-- The two bounds mention exactly one witness, and require only qBinding and pBinding. -/
theorem sharedBounds :
    InvertingSubtype carrierPolicy context WFTy.top selectedA ∧
      InvertingSubtype carrierPolicy context selectedA WFTy.bottom :=
  ⟨selectedLower, selectedUpper⟩

theorem collapse : InvertingSubtype carrierPolicy context WFTy.top WFTy.bottom :=
  selectedLower.trans selectedUpper

theorem noValidEnvironment (env : Indexed.Environment) (n : Nat) :
    ¬ Validates carrierPolicy context env n := fun valid => Mixed.noCollapse valid collapse

/-- The policy used for carrier extraction still permits ordinary unsuspended record cycles. -/
def ordinaryNode : Definition carrierPolicy 0 :=
  .record "next" (by decide) (WFTy.var 0 (by decide))

/-- Closing a genuine record-recursive equation adds no contradictory assumptions. -/
theorem ordinaryScopeConsistent :
    ¬ InvertingSubtype carrierPolicy
      (ordinaryNode.native.openContext SubtypingContext.empty) WFTy.top WFTy.bottom :=
  ordinaryNode.noCollapse

/-- A ghost-labelled wrapper around the ordinary recursive record is allowed as well. -/
def carrierNode : Definition carrierPolicy 0 :=
  .ghostRecord (Transparent.CarrierLayout.code 0 true) (carrierPolicy_code 0 true) ordinaryNode

theorem carrierScopeConsistent :
    ¬ InvertingSubtype carrierPolicy
      (carrierNode.native.openContext SubtypingContext.empty) WFTy.top WFTy.bottom :=
  carrierNode.noCollapse

end CDotFCCT.CTML.Mixed.SharedWitness
