import CDot.Weakening
import CDotFCCT.CTML.PackageSubtyping
import CTMLCore.Declarative.Lattice

/-!
# Translation of open DOT types and subtyping derivations

This fragment works under already-opened member witnesses. It includes records,
intersections, bounded members, selections and nondependent arrows. The finite
derivation datatype is in `Type`; `source` checks its erasure against `CDot.Subtyp`,
and `translate` constructs a CTML Core payload-subtyping proof. Member declarations
have no runtime payload; their bounds are separate constraints on shared witnesses,
abstracted by the enclosing CPS consumer. It does not assume a
subtyping-preservation theorem. Recursive self types and dependent arrow binders
are deliberately absent from this intermediate fragment.
-/

set_option autoImplicit false

namespace CDotFCCT.OpenCore

open CTMLCore

variable [CDot.Signature]

/-- A stable, free source path. Field lists have DOT's inside-out order. -/
structure Path where
  root : CDot.Var
  fields : CDot.Fields
  deriving DecidableEq

def Path.source (p : Path) : CDot.Path := .select (.free p.root) p.fields

def Path.field (p : Path) (label : CDot.Signature.TrmLabel) : Path :=
  ⟨p.root, label :: p.fields⟩

/-- The key, rather than the occurrence of a selection, determines its witness. -/
structure Member where
  path : Path
  label : CDot.Signature.TypLabel
  deriving DecidableEq

inductive Typ where
  | top
  | bottom
  | selection (member : Member)
  | field (label : CDot.Signature.TrmLabel) (body : Typ)
  | member (label : CDot.Signature.TypLabel) (lower upper : Typ)
  | inter (left right : Typ)
  | arrow (param result : Typ)

def Typ.source : Typ → CDot.Typ
  | .top => .top
  | .bottom => .bot
  | .selection m => .path m.path.source m.label
  | .field label body => .rcd (.trm label body.source)
  | .member label lower upper => .rcd (.typ label lower.source upper.source)
  | .inter left right => .and left.source right.source
  | .arrow param result => .all param.source result.source

/-- A witness environment may map keys to variables or to concrete types. -/
structure Witnesses (n : Nat) where
  get : Member → WFTy n
  fieldName : CDot.Signature.TrmLabel → CTMLCore.Syntax.FieldName
  answer : WFTy n

def Typ.translate {n : Nat} (w : Witnesses n) : Typ → WFTy n
  | .top => WFTy.top
  | .bottom => WFTy.bottom
  | .selection m => w.get m
  | .field label body => WFTy.record (w.fieldName label) (body.translate w)
  | .member _ _ _ => WFTy.top
  | .inter left right => WFTy.intersection (left.translate w) (right.translate w)
  | .arrow param result => WFTy.arrow (param.translate w) (result.translate w)

theorem Typ.source_openRec (type : Typ) (index : Nat) (x : CDot.Var) :
    type.source.openRec index x = type.source := by
  induction type generalizing index <;>
    simp_all only [source, CDot.Typ.openRec, CDot.Dec.openRec, Path.source,
      CDot.Path.openRec, CDot.AVar.openRec]

theorem Typ.source_openRecPath (type : Typ) (index : Nat) (path : CDot.Path) :
    type.source.openRecPath index path = type.source := by
  induction type generalizing index <;>
    simp_all only [source, CDot.Typ.openRecPath, CDot.Dec.openRecPath, Path.source,
      CDot.Path.openRecPath]

structure Bound where
  key : Member
  lower : Typ
  upper : Typ

def Bound.guards {n : Nat} (w : Witnesses n) (b : Bound) : List (WFConstraint n) :=
  [WFConstraint.constr (b.lower.translate w) (w.get b.key),
   WFConstraint.constr (w.get b.key) (b.upper.translate w)]

def boundsContext {n : Nat} (w : Witnesses n) (bounds : List Bound) : SubtypingContext :=
  ⟨n, bounds.flatMap (Bound.guards w)⟩

/-- The source-side meaning of the opened bounds; no target proofs are assumed. -/
def SourceBounds (context : CDot.Ctx) (bounds : List Bound) : Prop :=
  ∀ b ∈ bounds, CDot.Typed context (.path b.key.path.source)
    (.rcd (.typ b.key.label b.lower.source b.upper.source))

inductive Subtyping (bounds : List Bound) : Typ → Typ → Type where
  | refl {type} : Subtyping bounds type type
  | trans {left middle right} :
      Subtyping bounds left middle → Subtyping bounds middle right → Subtyping bounds left right
  | top {type} : Subtyping bounds type .top
  | bottom {type} : Subtyping bounds .bottom type
  | interLeft {left right} : Subtyping bounds (.inter left right) left
  | interRight {left right} : Subtyping bounds (.inter left right) right
  | interIntro {type left right} :
      Subtyping bounds type left → Subtyping bounds type right →
      Subtyping bounds type (.inter left right)
  | field {left right} (label) :
      Subtyping bounds left right → Subtyping bounds (.field label left) (.field label right)
  | member {lower₁ upper₁ lower₂ upper₂} (label) :
      Subtyping bounds lower₂ lower₁ → Subtyping bounds upper₁ upper₂ →
      Subtyping bounds (.member label lower₁ upper₁) (.member label lower₂ upper₂)
  | arrow {param₁ result₁ param₂ result₂} :
      Subtyping bounds param₂ param₁ → Subtyping bounds result₁ result₂ →
      Subtyping bounds (.arrow param₁ result₁) (.arrow param₂ result₂)
  | lower (b : Bound) : b ∈ bounds → Subtyping bounds b.lower (.selection b.key)
  | upper (b : Bound) : b ∈ bounds → Subtyping bounds (.selection b.key) b.upper

private theorem sourceArrow {context : CDot.Ctx}
    {param₁ result₁ param₂ result₂ : Typ}
    (param : CDot.Subtyp context param₂.source param₁.source)
    (result : CDot.Subtyp context result₁.source result₂.source) :
    CDot.Subtyp context (.all param₁.source result₁.source)
      (.all param₂.source result₂.source) := by
  refine .all context.dom param (fun x hx => ?_)
  simpa only [CDot.Typ.open, Typ.source_openRec] using
    result.mono (CDot.Env.Extends.pushRight hx param₂.source)

/-- Erasure proves that every input derivation is an actual DOT subtyping derivation. -/
theorem Subtyping.source {bounds : List Bound} {left right : Typ}
    (h : Subtyping bounds left right) {context : CDot.Ctx}
    (members : SourceBounds context bounds) : CDot.Subtyp context left.source right.source :=
  match h with
  | .refl => .refl
  | .trans left right => .trans (left.source members) (right.source members)
  | .top => .top
  | .bottom => .bot
  | .interLeft => .andLeft
  | .interRight => .andRight
  | .interIntro left right => .andIntro (left.source members) (right.source members)
  | .field _ body => .fld (body.source members)
  | .member _ lowerProof upperProof => .typ (lowerProof.source members) (upperProof.source members)
  | .arrow param result => sourceArrow (param.source members) (result.source members)
  | .lower b membership => .selLo (members b membership)
  | .upper b membership => .selHi (members b membership)

private theorem lowerBound {n : Nat} (w : Witnesses n) {bounds : List Bound}
    (b : Bound) (membership : b ∈ bounds) :
    Subtype (boundsContext w bounds) (b.lower.translate w) (w.get b.key) := by
  exact @Subtype.hyp (boundsContext w bounds)
    (WFConstraint.constr (b.lower.translate w) (w.get b.key))
    (List.mem_flatMap.mpr ⟨b, membership, List.mem_cons_self⟩)

private theorem upperBound {n : Nat} (w : Witnesses n) {bounds : List Bound}
    (b : Bound) (membership : b ∈ bounds) :
    Subtype (boundsContext w bounds) (w.get b.key) (b.upper.translate w) := by
  exact @Subtype.hyp (boundsContext w bounds)
    (WFConstraint.constr (w.get b.key) (b.upper.translate w))
    (List.mem_flatMap.mpr ⟨b, membership, List.mem_cons_of_mem _ List.mem_cons_self⟩)

/-- Translate the payload subtyping. Member declarations have no runtime payload;
their guards belong to the enclosing object's package, not to an intersection of
independently packaged declarations. -/
theorem Subtyping.translate {n : Nat} (w : Witnesses n) {bounds : List Bound}
    {left right : Typ} (h : Subtyping bounds left right) :
    Subtype (boundsContext w bounds) (left.translate w) (right.translate w) :=
  match h with
  | .refl => .refl
  | .trans left right => .trans (left.translate w) (right.translate w)
  | .top => .leTop
  | .bottom => .botLe
  | .interLeft => .interLeft
  | .interRight => .interRight
  | .interIntro left right => .leInter (left.translate w) (right.translate w)
  | .field _ body => .record (body.translate w)
  | .member _ _ _ => .refl
  | .arrow param result => .arrow (param.translate w) (result.translate w)
  | .lower b membership => lowerBound w b membership
  | .upper b membership => upperBound w b membership

/-- Member-bound variance is retained at the enclosing package's guard boundary. -/
theorem Subtyping.memberPackage {n : Nat} (w : Witnesses n) {bounds : List Bound}
    {lower₁ upper₁ lower₂ upper₂ : Typ}
    (lower : Subtyping bounds lower₂ lower₁) (upper : Subtyping bounds upper₁ upper₂)
    (payload : WFTy (n + 1)) :
    Subtype (boundsContext w bounds)
      (CTML.existsCPS (CTML.bounds (lower₁.translate w) (upper₁.translate w)) payload w.answer)
      (CTML.existsCPS (CTML.bounds (lower₂.translate w) (upper₂.translate w)) payload w.answer) :=
  CTML.boundedSubtype (lower.translate w) (upper.translate w)

end CDotFCCT.OpenCore
