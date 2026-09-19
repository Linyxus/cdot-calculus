import CDotFCCT.CTML.CarrierEquationInterpretation
import CDotFCCT.CTML.CarrierFieldViews
import CDotFCCT.CTML.MixedSafety
import CDotFCCT.CTML.RecursivePackages

/-!
# Exporting solved pure carrier equations

Each package hides its solved carrier names, exposes the original equations in
both directions, and returns the identity function at both corresponding arrow
types. The examples use the existing precise-row and member-view syntax.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierEquationExamples

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation
open CarrierEquation

variable {ghost : FieldName → Bool}

def identity : Term := .abs (.var 0)

def equationPayload {depth size : Nat} (system : System ghost depth size) (index : Fin size) :
    WFTy (depth + size) :=
  WFTy.intersection (WFTy.arrow (system.name index) (system.compile index))
    (WFTy.arrow (system.compile index) (system.name index))

def interface {depth size : Nat} (system : System ghost depth size) (index : Fin size) :
    Interface depth := Interface.closeGuards size system.equations (equationPayload system index)

theorem identityTyping {s : SubtypingContext} {size : Nat}
    (system : System ghost s.typeDepth size) (index : Fin size)
    (context : TypingContext (s.typeDepth + size)) :
    HasType ghost (system.openContext s) context identity (equationPayload system index) :=
  .intersection
    (.abstraction ((HasType.native (.var _ 0 _ .here)).subsumption
      (.native (system.unfold s index))))
    (.abstraction ((HasType.native (.var _ 0 _ .here)).subsumption
      (.native (system.fold s index))))

theorem consumerSubtype {s : SubtypingContext} {size : Nat}
    (system : System ghost s.typeDepth size) (index : Fin size) (answer : WFTy s.typeDepth) :
    Subtype (system.openContext s) (((interface system index).consumer answer).weakenBy size)
      (WFTy.arrow (equationPayload system index) (answer.weakenBy size)) := by
  have opened := (Interface.bindBlock_open s size
    (Interface.guards system.equations (.payload (equationPayload system index)))
    answer).mapAssumptions
      (target := (system.openContext s).assumptions)
      (fun guard member => @Subtype.hyp (system.openContext s) guard
        (List.mem_append_right _ member))
  exact opened.trans (Interface.guards_open _ _ _ (fun guard member =>
    @Subtype.hyp (system.openContext s) guard (List.mem_append_left _ member)))

/-- Packing uses the solved names and original equation guards, without external evidence. -/
theorem packTyping {s : SubtypingContext} {size : Nat}
    (system : System ghost s.typeDepth size) (index : Fin size)
    (context : TypingContext s.typeDepth) (answer : WFTy s.typeDepth) :
    HasType ghost s context (pack identity) ((interface system index).package answer) := by
  refine .recursiveCarrierSystem system ?_
  rw [RecursivePackage.pack_liftTypes]
  exact .abstraction (.application
    ((HasType.native (.var _ 0 _ .here)).subsumption
      (.native (consumerSubtype system index answer))) (identityTyping system index _))

/-- Every generated pure carrier scope remains consistent under the mixed inversion rules. -/
theorem scope_noCollapse {size : Nat} (system : System ghost 0 size) :
    ¬ InvertingSubtype ghost (system.openContext SubtypingContext.empty) WFTy.top WFTy.bottom :=
  Mixed.noCollapse (system.validates
    (empty_validates ghost (fun _ _ => (fun _ => False, fun _ => False)) 0))

theorem packSafe {size : Nat} (system : System ghost 0 size) (index : Fin size)
    {reached : Term} (steps : Steps (pack identity) reached) :
    Value reached ∨ ∃ next, Step reached next :=
  (packTyping system index TypingContext.empty (WFTy.cls "$Unit")).safe steps

/-- Slot zero is the payload, slot one a type member, and slot two a child carrier. -/
def support : List Nat := [0, 1, 2]

def outerComponents (slot : Nat) : WFTy 0 :=
  if slot = 0 then WFTy.arrow (WFTy.cls "$Unit") (WFTy.cls "DOT") else WFTy.top

def childSlot : Transparent.MemberSlot (CarrierLayout.names support) :=
  CarrierLayout.slot support 2 (by decide)

def memberSlot : Transparent.MemberSlot (CarrierLayout.names support) :=
  CarrierLayout.slot support 1 (by decide)

def wholeChild : System carrierPolicy 0 1 where
  body _ := Expr.wholeChild support (carrierPolicy_names support) 2 0 outerComponents
  guarded _ := Expr.wholeChild_guarded support (carrierPolicy_names support) 2 0 outerComponents

def fieldSelf : System carrierPolicy 0 1 where
  body _ := Expr.fieldSelf childSlot (carrierPolicy_names support) 0
  guarded _ := Expr.fieldSelf_guarded childSlot (carrierPolicy_names support) 0

def memberSelf : System carrierPolicy 0 1 where
  body _ := Expr.memberSelf memberSlot (carrierPolicy_names support) 0
  guarded _ := Expr.memberSelf_guarded memberSlot (carrierPolicy_names support) 0

theorem wholeChild_exact : wholeChild.compile 0 =
    CarrierLayout.precise support (fun slot =>
      if slot = 2 then wholeChild.name 0 else (outerComponents slot).weakenBy 1) :=
  Expr.compile_wholeChild support (carrierPolicy_names support) 2 0 outerComponents

theorem fieldSelf_exact : fieldSelf.compile 0 =
    childSlot.view WFTy.bottom (fieldSelf.name 0) (fun _ => WFTy.top) :=
  Expr.compile_fieldSelf childSlot (carrierPolicy_names support) 0

theorem memberSelf_exact : memberSelf.compile 0 =
    memberSlot.view (memberSelf.name 0) (memberSelf.name 0) (fun _ => WFTy.top) :=
  Expr.compile_memberSelf memberSlot (carrierPolicy_names support) 0

/-- An opaque field view transports through the solved self-child carrier in both directions. -/
theorem wholeChild_view_iff (target : WFTy 1) :
    InvertingSubtype carrierPolicy (wholeChild.openContext SubtypingContext.empty)
        (wholeChild.name 0) (childSlot.view WFTy.bottom target (fun _ => WFTy.top)) ↔
      InvertingSubtype carrierPolicy (wholeChild.openContext SubtypingContext.empty)
        (wholeChild.name 0) target := by
  have view := CarrierFieldViews.whole_child_iff
    (s := wholeChild.openContext SubtypingContext.empty) (support := support) (child := 2)
    (by decide)
    (fun slot => if slot = 2 then wholeChild.name 0 else (outerComponents slot).weakenBy 1) target
  exact ⟨fun bound => view.mp
      ((InvertingSubtype.native (wholeChild.fold SubtypingContext.empty 0)).trans bound),
    fun bound => (InvertingSubtype.native (wholeChild.unfold SubtypingContext.empty 0)).trans
      (view.mpr bound)⟩

/-- This interface contains the solved whole-child carrier and both original equations. -/
theorem wholeChildTyping :
    HasType carrierPolicy SubtypingContext.empty TypingContext.empty (pack identity)
      ((interface wholeChild 0).package (WFTy.cls "$Unit")) :=
  packTyping (s := SubtypingContext.empty) wholeChild 0 TypingContext.empty (WFTy.cls "$Unit")

theorem fieldSelfTyping :
    HasType carrierPolicy SubtypingContext.empty TypingContext.empty (pack identity)
      ((interface fieldSelf 0).package (WFTy.cls "$Unit")) :=
  packTyping (s := SubtypingContext.empty) fieldSelf 0 TypingContext.empty (WFTy.cls "$Unit")

theorem memberSelfTyping :
    HasType carrierPolicy SubtypingContext.empty TypingContext.empty (pack identity)
      ((interface memberSelf 0).package (WFTy.cls "$Unit")) :=
  packTyping (s := SubtypingContext.empty) memberSelf 0 TypingContext.empty (WFTy.cls "$Unit")

theorem wholeChildSafe {reached : Term} (steps : Steps (pack identity) reached) :
    Value reached ∨ ∃ next, Step reached next := wholeChildTyping.safe steps

theorem fieldSelfSafe {reached : Term} (steps : Steps (pack identity) reached) :
    Value reached ∨ ∃ next, Step reached next := fieldSelfTyping.safe steps

theorem memberSelfSafe {reached : Term} (steps : Steps (pack identity) reached) :
    Value reached ∨ ∃ next, Step reached next := memberSelfTyping.safe steps

end CDotFCCT.CTML.Mixed.CarrierEquationExamples
