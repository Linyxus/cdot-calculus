import CDotFCCT.CTML.CarrierPackages
import CTMLCore.Language.TypeBlocks

/-!
# Opening a carrier package for a continuation

The computed scope contains the fresh component types, weakened outer context,
single carrier guard, payload binding and lifted continuation body. The equivalence
below identifies its typing obligation with ordinary existential elimination.
No witness names or target derivations are provided when computing the scope.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Transparent.CarrierLayout

open CTMLCore CTMLCore.Syntax

universe u
variable {Label : Type u} [DecidableEq Label]

/-- All syntax needed to check a continuation after opening the witness telescope. -/
structure Opening (Label : Type u) where
  depth : Nat
  types : Label → WFTy depth
  view : WFTy depth
  assumptions : List (WFConstraint depth)
  context : TypingContext depth
  body : Term
  answer : WFTy depth

def Opening.guard (support : List Label) (opened : Opening Label) : WFConstraint opened.depth :=
  WFConstraint.constr (precise support opened.types) opened.view

def Opening.subtypingContext (support : List Label) (opened : Opening Label) : SubtypingContext :=
  ⟨opened.depth, opened.guard support :: opened.assumptions⟩

def Opening.typingContext (payload : Label) (opened : Opening Label) : TypingContext opened.depth :=
  opened.context.bind (opened.types payload)

def Opening.Check (support : List Label) (payload : Label) (opened : Opening Label) : Prop :=
  HasType (opened.subtypingContext support) (opened.typingContext payload) opened.body opened.answer

/-- Opening moves ambient names under every new binder, preserving their identity. -/
def openComponents : (remaining : List Label) → {depth : Nat} →
    (Label → WFTy depth) → WFTy depth → List (WFConstraint depth) → TypingContext depth →
    Term → WFTy depth → Opening Label
  | [], depth, types, view, assumptions, context, body, answer =>
      ⟨depth, types, view, assumptions, context, body, answer⟩
  | label :: rest, _, types, view, assumptions, context, body, answer =>
      openComponents rest (bindComponent types label) view.weaken
        (assumptions.map WFConstraint.weaken) context.bindType (body.liftTy 1) answer.weaken

theorem openComponents_iff (support : List Label) (payload : Label) (remaining : List Label)
    {depth : Nat} (types : Label → WFTy depth) (view : WFTy depth)
    (assumptions : List (WFConstraint depth)) (context : TypingContext depth)
    (body : Term) (answer : WFTy depth) :
    InterfaceOpened (telescope support payload remaining types view)
        assumptions context body answer ↔
      (openComponents remaining types view assumptions context body answer).Check
        support payload := by
  induction remaining generalizing depth body with
  | nil => rfl
  | cons label rest ih =>
      exact ih (bindComponent types label) view.weaken
        (assumptions.map WFConstraint.weaken) context.bindType (body.liftTy 1) answer.weaken

def opening {depth : Nat} (support : List Label) (view : WFTy depth)
    (assumptions : List (WFConstraint depth)) (context : TypingContext depth)
    (body : Term) (answer : WFTy depth) : Opening Label :=
  openComponents support (fun _ => WFTy.top) view assumptions context body answer

theorem openComponents_depth (remaining : List Label) {depth : Nat}
    (types : Label → WFTy depth) (view : WFTy depth)
    (assumptions : List (WFConstraint depth)) (context : TypingContext depth)
    (body : Term) (answer : WFTy depth) :
    (openComponents remaining types view assumptions context body answer).depth =
      depth + remaining.length := by
  induction remaining generalizing depth body with
  | nil => rfl
  | cons label rest ih =>
      simpa only [openComponents, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using
        ih (bindComponent types label) view.weaken
          (assumptions.map WFConstraint.weaken) context.bindType (body.liftTy 1) answer.weaken

/-- The requested view retains the same outer names after the witness block is opened. -/
theorem openComponents_view (remaining : List Label) {depth : Nat}
    (types : Label → WFTy depth) (view : WFTy depth)
    (assumptions : List (WFConstraint depth)) (context : TypingContext depth)
    (body : Term) (answer : WFTy depth) :
    (openComponents remaining types view assumptions context body answer).view.raw =
      view.raw.lift remaining.length := by
  induction remaining generalizing depth body with
  | nil => simp [openComponents, Ty.lift]
  | cons label rest ih =>
      simpa only [openComponents, WFTy.raw_weaken, Ty.lift, Ty.liftAt_add,
        List.length_cons, Nat.add_comm 1] using
        ih (bindComponent types label) view.weaken
          (assumptions.map WFConstraint.weaken) context.bindType (body.liftTy 1) answer.weaken

/-- The answer cannot acquire a reference to one of the newly hidden witnesses. -/
theorem openComponents_answer (remaining : List Label) {depth : Nat}
    (types : Label → WFTy depth) (view : WFTy depth)
    (assumptions : List (WFConstraint depth)) (context : TypingContext depth)
    (body : Term) (answer : WFTy depth) :
    (openComponents remaining types view assumptions context body answer).answer.raw =
      answer.raw.lift remaining.length := by
  induction remaining generalizing depth body with
  | nil => simp [openComponents, Ty.lift]
  | cons label rest ih =>
      simpa only [openComponents, WFTy.raw_weaken, Ty.lift, Ty.liftAt_add,
        List.length_cons, Nat.add_comm 1] using
        ih (bindComponent types label) view.weaken
          (assumptions.map WFConstraint.weaken) context.bindType (body.liftTy 1) answer.weaken

/-- The generated scope suffices to construct a consumer of the complete package. -/
theorem consumerTyping {s : SubtypingContext} (support : List Label) (payload : Label)
    {view answer : WFTy s.typeDepth} {context : TypingContext s.typeDepth} {body : Term}
    (typing : (opening support view s.assumptions context body answer).Check support payload) :
    HasType s context (.abs body) ((interface support payload view).consumer answer) :=
  interfaceConsumerTyping _
    ((openComponents_iff support payload support _ view s.assumptions context body answer).mpr
      typing)

/-- Elimination closes every newly introduced witness around the continuation body. -/
theorem unpackTyping {s : SubtypingContext} (support : List Label) (payload : Label)
    {view answer : WFTy s.typeDepth} {context : TypingContext s.typeDepth} {value body : Term}
    (producer : HasType s context value ((interface support payload view).package answer))
    (consumer : (opening support view s.assumptions context body answer).Check support payload) :
    HasType s context (.app value (.abs body)) answer :=
  .application producer (consumerTyping support payload consumer)

end CDotFCCT.CTML.Transparent.CarrierLayout
