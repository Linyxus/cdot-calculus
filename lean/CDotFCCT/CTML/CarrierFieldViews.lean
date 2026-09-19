import CDotFCCT.CTML.MixedCarrierLayout
import CDotFCCT.CoreDerivation

/-!
# Structural field views and the opaque-selection obligation

A visible member declaration can use a flat `(field, member)` coordinate in the
parent carrier. Reindexing that coordinate into the child's carrier preserves
both directions of field typing, since both carriers use exactly the same
witness. This result does not reindex an opaque selected type: the source
regression at the end isolates that remaining obligation.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierFieldViews

open CTMLCore CTMLCore.Syntax CarrierLayout

universe u v

/-- A visible member view constrains exactly its shared witness. -/
theorem precise_member_iff {Label : Type u} [DecidableEq Label]
    {s : SubtypingContext} {support : List Label} {label : Label}
    (present : label ∈ support) (types : Label → WFTy s.typeDepth)
    (lower upper : WFTy s.typeDepth) :
    InvertingSubtype carrierPolicy s (precise support types)
        ((slot support label present).view lower upper (fun _ => WFTy.top)) ↔
      InvertingSubtype carrierPolicy s lower (types label) ∧
        InvertingSubtype carrierPolicy s (types label) upper := by
  rw [precise_eq_slot present types]
  constructor
  · intro included
    exact ⟨memberLowerBound _ (carrierPolicy_names support) (.native .refl) included,
      memberUpperBound _ (carrierPolicy_names support) (.native .refl) included⟩
  · rintro ⟨low, high⟩
    exact memberVariance _ low high (fun _ _ => .native .leTop)

/-- A whole-child slot transports an opaque type without inspecting or relabeling it. -/
theorem whole_child_iff {Label : Type u} [DecidableEq Label]
    {s : SubtypingContext} {support : List Label} {child : Label}
    (present : child ∈ support) (types : Label → WFTy s.typeDepth)
    (target : WFTy s.typeDepth) :
    InvertingSubtype carrierPolicy s (precise support types)
        ((slot support child present).view WFTy.bottom target (fun _ => WFTy.top)) ↔
      InvertingSubtype carrierPolicy s (types child) target :=
  (precise_member_iff present types WFTy.bottom target).trans
    ⟨And.right, fun bound => ⟨.native .botLe, bound⟩⟩

/-- A flattened field-member coordinate and its child view constrain the same witness. -/
theorem flattened_member_iff {Field : Type u} {Label : Type v}
    [DecidableEq Field] [DecidableEq Label] {s : SubtypingContext}
    {parentSupport : List (Field × Label)} {childSupport : List Label}
    {field : Field} {label : Label} (parentPresent : (field, label) ∈ parentSupport)
    (childPresent : label ∈ childSupport) (types : Field × Label → WFTy s.typeDepth)
    (lower upper : WFTy s.typeDepth) :
    InvertingSubtype carrierPolicy s (precise parentSupport types)
        ((slot parentSupport (field, label) parentPresent).view
          lower upper (fun _ => WFTy.top)) ↔
      InvertingSubtype carrierPolicy s
        (precise childSupport (fun member => types (field, member)))
        ((slot childSupport label childPresent).view lower upper (fun _ => WFTy.top)) :=
  (precise_member_iff parentPresent types lower upper).trans
    (precise_member_iff childPresent (fun member => types (field, member)) lower upper).symm

end CDotFCCT.CTML.Mixed.CarrierFieldViews

namespace CDotFCCT.CarrierFieldViews.OpaqueSelection

open CDot

local instance : Signature where
  TypLabel := String
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

def selected : Typ := .path (.var 1) "X"
def fieldView : Typ := .rcd (.trm "a" selected)
def ownerType : Typ :=
  .and (.rcd (.typ "X" .bot .top)) (.rcd (.typ "Y" .bot fieldView))
def context : Ctx := [(0, .path (.var 1) "Y"), (1, ownerType)]

/-- The field view is obtained through a selected upper bound, without an object origin. -/
def parentView : Core.Typing context (.var 0) fieldView :=
  .sub (.var .here) (.selHi (.sub (.var (.there (by decide) .here)) .andRight))

/-- Field elimination must transport an opaque selected type into the child view. -/
def eliminated : Core.Typing context (.path ((Path.var 0).selectField "a")) selected :=
  .newElim parentView

/-- Record introduction must support the converse transport for the same opaque type. -/
def introduced : Core.Typing context (.var 0) fieldView := .rcdIntro eliminated

theorem eliminated_source : Typed context (.path ((Path.var 0).selectField "a")) selected :=
  eliminated.source

theorem introduced_source : Typed context (.var 0) fieldView := introduced.source

end CDotFCCT.CarrierFieldViews.OpaqueSelection
