import CDotFCCT.CTML.MixedCarrierPackages
import CDotFCCT.CTML.CarrierOpening

/-!
# Opening the existing carrier telescope in the record-guarded target

The scope computation is shared with the existing syntax. This module changes only
its typing predicate and proves the same packing/elimination correspondence for the
mixed target. The client receives one common scope for all member and payload names.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierLayout

open CTMLCore CTMLCore.Syntax

export Transparent.CarrierLayout (Opening openComponents opening openComponents_depth
  openComponents_view openComponents_answer)

universe u
variable {Label : Type u} [DecidableEq Label] {ghost : FieldName → Bool}

namespace Opening

export Transparent.CarrierLayout.Opening (guard subtypingContext typingContext)

def Check (ghost : FieldName → Bool) (support : List Label) (payload : Label)
    (opened : Opening Label) : Prop :=
  HasType ghost (opened.subtypingContext support) (opened.typingContext payload)
    opened.body opened.answer

end Opening

theorem openComponents_iff (support : List Label) (payload : Label) (remaining : List Label)
    {depth : Nat} (types : Label → WFTy depth) (view : WFTy depth)
    (assumptions : List (WFConstraint depth)) (context : TypingContext depth)
    (body : Term) (answer : WFTy depth) :
    InterfaceOpened ghost (telescope support payload remaining types view)
        assumptions context body answer ↔
      Opening.Check ghost support payload
        (openComponents remaining types view assumptions context body answer) := by
  induction remaining generalizing depth body with
  | nil => rfl
  | cons label rest ih =>
      exact ih (bindComponent types label) view.weaken
        (assumptions.map WFConstraint.weaken) context.bindType (body.liftTy 1) answer.weaken

/-- The generated scope suffices to construct a consumer of the complete package. -/
theorem consumerTyping {s : SubtypingContext} (support : List Label) (payload : Label)
    {view answer : WFTy s.typeDepth} {context : TypingContext s.typeDepth} {body : Term}
    (typing : Opening.Check ghost support payload
      (opening support view s.assumptions context body answer)) :
    HasType ghost s context (.abs body) ((interface support payload view).consumer answer) :=
  interfaceConsumerTyping _
    ((openComponents_iff support payload support _ view s.assumptions context body answer).mpr
      typing)

/-- Elimination closes every newly introduced witness around the continuation body. -/
theorem unpackTyping {s : SubtypingContext} (support : List Label) (payload : Label)
    {view answer : WFTy s.typeDepth} {context : TypingContext s.typeDepth} {value body : Term}
    (producer : HasType ghost s context value ((interface support payload view).package answer))
    (consumer : Opening.Check ghost support payload
      (opening support view s.assumptions context body answer)) :
    HasType ghost s context (.app value (.abs body)) answer :=
  .application producer (consumerTyping support payload consumer)

end CDotFCCT.CTML.Mixed.CarrierLayout
