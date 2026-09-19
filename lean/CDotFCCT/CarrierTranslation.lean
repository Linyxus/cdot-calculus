import CDotFCCT.CoreDerivation
import CDotFCCT.MemberUses
import CDotFCCT.CTML.MixedCarrierLayout
import CDotFCCT.CTML.MixedSafety

/-!
# Derivation-directed translation of shared member bounds

This is the constraint-producing part of the experimental carrier translation.
Its input is the actual core-DOT judgment. Context assumptions come exclusively
from source bindings; selection rules must recover their bounds from those
assumptions using the translated source derivation.

The present pass handles member declarations, intersections, selections and
singleton transport between paths. Unsupported source rules return `none`.
The payload type has its own paired slot, so a runtime view yields a bound usable
by ordinary term typing. `CarrierRuntime` uses this layout for environment values;
the general term compiler is unfinished.
-/

set_option autoImplicit false

namespace CDotFCCT.CarrierTranslation

open CDot CTMLCore CTML.Mixed
open CTML.Transparent (MemberSlot)

variable [Signature]

/-- Syntactic witness allocation, with no supplied subtyping or typing proofs. -/
structure Layout where
  depth : Nat
  labels : List Signature.TypLabel
  witness : Path → Signature.TypLabel → Option (WFTy depth)
  payload : Path → Option (WFTy depth)

def Layout.slots (layout : Layout) : List (Option Signature.TypLabel) :=
  none :: layout.labels.map some

def Layout.component (layout : Layout) (path : Path) :
    Option Signature.TypLabel → Option (WFTy layout.depth)
  | none => layout.payload path
  | some label => layout.witness path label

theorem Layout.memberPresent {layout : Layout} {label : Signature.TypLabel}
    (present : label ∈ layout.labels) : some label ∈ layout.slots :=
  List.mem_cons_of_mem none (List.mem_map.mpr ⟨label, present, rfl⟩)

def Layout.memberSlot (layout : Layout) (label : Signature.TypLabel)
    (present : label ∈ layout.labels) : MemberSlot (CarrierLayout.names layout.slots) :=
  CarrierLayout.slot layout.slots (some label) (Layout.memberPresent present)

def Layout.payloadSlot (layout : Layout) : MemberSlot (CarrierLayout.names layout.slots) :=
  CarrierLayout.slot layout.slots none List.mem_cons_self

theorem Layout.memberSlot_congr {layout : Layout} {left right : Signature.TypLabel}
    (equal : left = right) (leftPresent : left ∈ layout.labels)
    (rightPresent : right ∈ layout.labels) :
    layout.memberSlot left leftPresent = layout.memberSlot right rightPresent :=
  CarrierLayout.slot_congr (congrArg some equal)
    (Layout.memberPresent leftPresent) (Layout.memberPresent rightPresent)

def Layout.completeAt (layout : Layout) (path : Path) : Bool :=
  layout.slots.all (fun slot => (layout.component path slot).isSome)

theorem Layout.completeAt_member {layout : Layout} {path : Path}
    (complete : layout.completeAt path = true) {label : Signature.TypLabel}
    (present : label ∈ layout.labels) : (layout.witness path label).isSome = true :=
  List.all_eq_true.mp complete (some label) (Layout.memberPresent present)

theorem Layout.completeAt_payload {layout : Layout} {path : Path}
    (complete : layout.completeAt path = true) : (layout.payload path).isSome = true :=
  List.all_eq_true.mp complete none List.mem_cons_self

def Layout.precise (layout : Layout) (path : Path) : WFTy layout.depth :=
  CarrierLayout.precise layout.slots
    (fun slot => (layout.component path slot).getD WFTy.top)

def Layout.runtimeView (layout : Layout) (type : WFTy layout.depth) : WFTy layout.depth :=
  layout.payloadSlot.view WFTy.bottom type (fun _ => WFTy.top)

/-- A certificate that the source type has a supported, non-erased encoding. -/
inductive TypeCode (layout : Layout) : Typ → WFTy layout.depth → Type where
  | top : TypeCode layout .top WFTy.top
  | bot : TypeCode layout .bot WFTy.bottom
  | selection {path : Path} {label : Signature.TypLabel} {witness : WFTy layout.depth} :
      layout.witness path label = some witness → TypeCode layout (.path path label) witness
  | singleton {path : Path} : path.Named → layout.completeAt path = true →
      TypeCode layout (.sngl path) (layout.precise path)
  | inter {left right : Typ} {leftType rightType : WFTy layout.depth} :
      TypeCode layout left leftType → TypeCode layout right rightType →
      TypeCode layout (.and left right) (WFTy.intersection leftType rightType)
  | member {label : Signature.TypLabel} {lower upper : Typ}
      {lowerType upperType : WFTy layout.depth} (present : label ∈ layout.labels) :
      TypeCode layout lower lowerType → TypeCode layout upper upperType →
      TypeCode layout (.rcd (.typ label lower upper))
        ((layout.memberSlot label present).view
          lowerType upperType (fun _ => WFTy.top))

def encode (layout : Layout) (type : Typ) :
    Option (Sigma (TypeCode layout type)) :=
  match type with
  | .top => some ⟨_, .top⟩
  | .bot => some ⟨_, .bot⟩
  | .path path label =>
      match found : layout.witness path label with
      | some witness => some ⟨witness, .selection found⟩
      | none => none
  | .sngl (.select (.free name) fields) =>
      if complete : layout.completeAt (.select (.free name) fields) = true then
        some ⟨_, .singleton ⟨name, rfl⟩ complete⟩
      else none
  | .and left right => do
      let ⟨_, leftCode⟩ ← encode layout left
      let ⟨_, rightCode⟩ ← encode layout right
      return ⟨_, .inter leftCode rightCode⟩
  | .rcd (.typ label lower upper) =>
      if present : label ∈ layout.labels then do
        let ⟨_, lowerCode⟩ ← encode layout lower
        let ⟨_, upperCode⟩ ← encode layout upper
        return ⟨_, .member present lowerCode upperCode⟩
      else none
  | .rcd (.trm _ _) | .bnd _ | .all _ _ | .sngl (.select (.bound _) _) => none

theorem TypeCode.unique {layout : Layout} {source : Typ} {left right : WFTy layout.depth}
    (first : TypeCode layout source left) (second : TypeCode layout source right) :
    left = right := by
  induction first generalizing right with
  | top => cases second; rfl
  | bot => cases second; rfl
  | selection found =>
      cases second with
      | selection other => exact Option.some.inj (found.symm.trans other)
  | singleton _ _ => cases second; rfl
  | inter firstLeft firstRight ihLeft ihRight =>
      cases second with
      | inter secondLeft secondRight =>
          exact congrArg₂ WFTy.intersection (ihLeft secondLeft) (ihRight secondRight)
  | member present firstLower firstUpper ihLower ihUpper =>
      cases second with
      | member _ secondLower secondUpper =>
          exact congrArg₂
            (fun lower upper =>
              (layout.memberSlot _ present).view lower upper (fun _ => WFTy.top))
            (ihLower secondLower) (ihUpper secondUpper)

/-- Each generated guard has exactly one source-context binding as its origin. -/
inductive ContextCode (layout : Layout) : Ctx → List (WFConstraint layout.depth) → Type where
  | nil : ContextCode layout [] []
  | cons {context : Ctx} {guards : List (WFConstraint layout.depth)}
      (name : Var) {source : Typ} {type : WFTy layout.depth} :
      layout.completeAt (.var name) = true → TypeCode layout source type →
      ContextCode layout context guards →
      ContextCode layout ((name, source) :: context)
        (WFConstraint.constr (layout.precise (.var name)) type :: guards)

def encodeContext (layout : Layout) (context : Ctx) :
    Option (Sigma (ContextCode layout context)) :=
  match context with
  | [] => some ⟨[], .nil⟩
  | (name, type) :: rest =>
      if complete : layout.completeAt (.var name) = true then do
        let ⟨_, code⟩ ← encode layout type
        let ⟨_, contextCode⟩ ← encodeContext layout rest
        return ⟨_, .cons name complete code contextCode⟩
      else none

theorem ContextCode.contains {layout : Layout} {context : Ctx}
    {guards : List (WFConstraint layout.depth)} (translated : ContextCode layout context guards)
    {name : Var} {source : Typ} (lookup : Env.Binds name source context)
    {type : WFTy layout.depth} (code : TypeCode layout source type) :
    WFConstraint.constr (layout.precise (.var name)) type ∈ guards := by
  induction translated with
  | nil => cases lookup
  | cons name complete entry rest ih =>
      cases lookup with
      | here => exact (entry.unique code) ▸ List.mem_cons_self
      | there different found => exact List.mem_cons_of_mem _ (ih found)

theorem ContextCode.length {layout : Layout} {context : Ctx}
    {guards : List (WFConstraint layout.depth)} (translated : ContextCode layout context guards) :
    guards.length = context.length := by
  induction translated <;> simp_all

omit [Signature] in
theorem interIntro {s : SubtypingContext} {source left right : WFTy s.typeDepth}
    (first : InvertingSubtype carrierPolicy s source left)
    (second : InvertingSubtype carrierPolicy s source right) :
    InvertingSubtype carrierPolicy s source (WFTy.intersection left right) := by
  refine .nativeWith [WFConstraint.constr source left, WFConstraint.constr source right]
    (.leInter
      (@CTMLCore.Subtype.hyp
        ⟨s.typeDepth, [WFConstraint.constr source left, WFConstraint.constr source right]⟩
        (WFConstraint.constr source left) List.mem_cons_self)
      (@CTMLCore.Subtype.hyp
        ⟨s.typeDepth, [WFConstraint.constr source left, WFConstraint.constr source right]⟩
        (WFConstraint.constr source right) (List.mem_cons_of_mem _ List.mem_cons_self))) ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro guard (rfl | rfl) <;> assumption

theorem Layout.asSlot {layout : Layout} {guards : List (WFConstraint layout.depth)}
    {path : Path} {label : Signature.TypLabel}
    (present : label ∈ layout.labels) {witness target : WFTy layout.depth}
    (found : layout.witness path label = some witness)
    (typing : InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩ (layout.precise path) target) :
    InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩
      ((layout.memberSlot label present).precise witness
        (CarrierLayout.components layout.slots layout.slots
          (fun slot => (layout.component path slot).getD WFTy.top)))
      target := by
  simpa only [Layout.precise, Layout.memberSlot,
    CarrierLayout.precise_eq_slot (Layout.memberPresent present), Layout.component,
    found, Option.getD_some] using typing

theorem Layout.payloadBound {layout : Layout} {guards : List (WFConstraint layout.depth)}
    {path : Path} {payload target : WFTy layout.depth}
    (found : layout.payload path = some payload)
    (typing : InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩
      (layout.precise path) (layout.runtimeView target)) :
    InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩ payload target := by
  have atSlot : InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩
      (layout.payloadSlot.precise payload
        (CarrierLayout.components layout.slots layout.slots
          (fun slot => (layout.component path slot).getD WFTy.top)))
      (layout.runtimeView target) := by
    simpa only [Layout.precise, Layout.payloadSlot,
      CarrierLayout.precise_eq_slot (support := layout.slots) (label := none) List.mem_cons_self,
      Layout.component, found, Option.getD_some] using typing
  exact memberUpperBound layout.payloadSlot (carrierPolicy_names layout.slots)
    (.native .refl) atSlot

theorem Layout.memberView_intro {layout : Layout} {guards : List (WFConstraint layout.depth)}
    {path : Path} {label : Signature.TypLabel} (present : label ∈ layout.labels)
    {witness lower upper : WFTy layout.depth}
    (found : layout.witness path label = some witness)
    (lowerBound : InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩ lower witness)
    (upperBound : InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩ witness upper) :
    InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩ (layout.precise path)
      ((layout.memberSlot label present).view lower upper (fun _ => WFTy.top)) := by
  have evidence : InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩
      ((layout.memberSlot label present).precise witness
        (CarrierLayout.components layout.slots layout.slots
          (fun slot => (layout.component path slot).getD WFTy.top)))
      ((layout.memberSlot label present).view lower upper (fun _ => WFTy.top)) :=
    memberVariance (layout.memberSlot label present) lowerBound upperBound
      (fun _ _ => .native .leTop)
  simpa only [Layout.precise, Layout.memberSlot,
    CarrierLayout.precise_eq_slot (Layout.memberPresent present), Layout.component,
    found, Option.getD_some] using evidence

theorem Layout.runtimeView_intro {layout : Layout} {guards : List (WFConstraint layout.depth)}
    {path : Path} {payload target : WFTy layout.depth}
    (found : layout.payload path = some payload)
    (upperBound : InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩ payload target) :
    InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩
      (layout.precise path) (layout.runtimeView target) := by
  have evidence : InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩
      (layout.payloadSlot.precise payload
        (CarrierLayout.components layout.slots layout.slots
          (fun slot => (layout.component path slot).getD WFTy.top)))
      (layout.runtimeView target) :=
    memberVariance layout.payloadSlot (.native .botLe) upperBound (fun _ _ => .native .leTop)
  simpa only [Layout.precise, Layout.payloadSlot,
    CarrierLayout.precise_eq_slot (support := layout.slots) (label := none) List.mem_cons_self,
    Layout.component, found, Option.getD_some] using evidence

structure SubtypingResult (layout : Layout) (guards : List (WFConstraint layout.depth))
    (sourceSub sourceSup : Typ) where
  sub : WFTy layout.depth
  sup : WFTy layout.depth
  subCode : TypeCode layout sourceSub sub
  supCode : TypeCode layout sourceSup sup
  proof : InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩ sub sup

structure PathResult (layout : Layout) (guards : List (WFConstraint layout.depth))
    (path : Path) (source : Typ) where
  type : WFTy layout.depth
  code : TypeCode layout source type
  proof : InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩ (layout.precise path) type

structure Equivalence (s : SubtypingContext) (left right : WFTy s.typeDepth) : Type where
  forward : InvertingSubtype carrierPolicy s left right
  backward : InvertingSubtype carrierPolicy s right left

def Equivalence.ofEq {s : SubtypingContext} {left right : WFTy s.typeDepth}
    (equal : left = right) : Equivalence s left right :=
  match equal with
  | rfl => ⟨.native .refl, .native .refl⟩

def Equivalence.castRight {s : SubtypingContext} {left right target : WFTy s.typeDepth}
    (typing : Equivalence s left right) (equal : right = target) : Equivalence s left target :=
  equal ▸ typing

def Equivalence.inter {s : SubtypingContext} {left₁ left₂ right₁ right₂ : WFTy s.typeDepth}
    (left : Equivalence s left₁ left₂) (right : Equivalence s right₁ right₂) :
    Equivalence s (WFTy.intersection left₁ right₁) (WFTy.intersection left₂ right₂) :=
  ⟨interIntro ((InvertingSubtype.native .interLeft).trans left.forward)
      ((InvertingSubtype.native .interRight).trans right.forward),
    interIntro ((InvertingSubtype.native .interLeft).trans left.backward)
      ((InvertingSubtype.native .interRight).trans right.backward)⟩

def comparePaths {layout : Layout} {guards : List (WFConstraint layout.depth)}
    {original replacement : Path}
    (related : InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩
      (layout.precise original) (layout.precise replacement)) (left right : Path) :
    Option (Equivalence ⟨layout.depth, guards⟩ (layout.precise left) (layout.precise right)) :=
  if same : left = right then some (.ofEq (congrArg layout.precise same))
  else if first : left = original then
    if second : right = replacement then
      some ⟨first.symm ▸ second.symm ▸ related,
        first.symm ▸ second.symm ▸ CarrierLayout.precise_symmetric related⟩
    else none
  else if first : left = replacement then
    if second : right = original then
      some ⟨first.symm ▸ second.symm ▸ CarrierLayout.precise_symmetric related,
        first.symm ▸ second.symm ▸ related⟩
    else none
  else none

theorem Layout.aliasBounds {layout : Layout} {guards : List (WFConstraint layout.depth)}
    {left right : Path} {label : Signature.TypLabel} (present : label ∈ layout.labels)
    {leftWitness rightWitness : WFTy layout.depth}
    (leftFound : layout.witness left label = some leftWitness)
    (rightFound : layout.witness right label = some rightWitness)
    (related : InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩
      (layout.precise left) (layout.precise right)) :
    InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩ leftWitness rightWitness ∧
      InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩ rightWitness leftWitness := by
  simpa only [Layout.component, leftFound, rightFound, Option.getD_some] using
    CarrierLayout.precise_bounds (Layout.memberPresent present) related

/-- Check replacement structurally, deriving witness equalities from the alias row.
General field extensions and unsupported type constructors are rejected. -/
def TypeCode.transport {layout : Layout} {guards : List (WFConstraint layout.depth)}
    {original replacement : Path}
    (related : InvertingSubtype carrierPolicy ⟨layout.depth, guards⟩
      (layout.precise original) (layout.precise replacement))
    {leftSource rightSource : Typ} {leftType rightType : WFTy layout.depth}
    (left : TypeCode layout leftSource leftType) (right : TypeCode layout rightSource rightType) :
    Option (Equivalence ⟨layout.depth, guards⟩ leftType rightType) :=
  if same : leftSource = rightSource then
    some (.ofEq ((same ▸ left).unique right))
  else
    match left, right with
    | @TypeCode.selection _ _ leftPath leftLabel _ leftFound,
        @TypeCode.selection _ _ rightPath rightLabel _ rightFound =>
        if sameLabel : rightLabel = leftLabel then
          if present : leftLabel ∈ layout.labels then do
            let paths ← comparePaths related leftPath rightPath
            let bounds := Layout.aliasBounds present leftFound
              (sameLabel ▸ rightFound) paths.forward
            return ⟨bounds.1, bounds.2⟩
          else none
        else none
    | @TypeCode.singleton _ _ leftPath _ _, @TypeCode.singleton _ _ rightPath _ _ =>
        comparePaths related leftPath rightPath
    | .inter left₁ right₁, .inter left₂ right₂ => do
        let lower ← left₁.transport related left₂
        let upper ← right₁.transport related right₂
        return lower.inter upper
    | @TypeCode.member _ _ leftLabel _ _ _ _ present leftLower leftUpper,
        @TypeCode.member _ _ rightLabel _ _ rightLo rightHi rightPresent rightLower rightUpper =>
        if sameLabel : rightLabel = leftLabel then do
          let lower ← leftLower.transport related rightLower
          let upper ← leftUpper.transport related rightUpper
          let combined : Equivalence ⟨layout.depth, guards⟩ _ _ :=
            ⟨memberVariance (layout.memberSlot _ present)
                lower.backward upper.forward (fun _ _ => .native .refl),
              memberVariance (layout.memberSlot _ present)
                lower.forward upper.backward (fun _ _ => .native .refl)⟩
          let aligned := congrArg (fun slot => slot.view rightLo rightHi (fun _ => WFTy.top))
            (Layout.memberSlot_congr sameLabel rightPresent present)
          return combined.castRight aligned.symm
        else none
    | _, _ => none
termination_by structural left

mutual
  /-- Follow a source path derivation; no requested bound is added to the context. -/
  def pathTyping {layout : Layout} {context : Ctx}
      {guards : List (WFConstraint layout.depth)} (translated : ContextCode layout context guards)
      {path : Path} {source : Typ} (derivation : Core.Typing context (.path path) source) :
      Option (PathResult layout guards path source) :=
    match derivation with
    | .var lookup => do
        let ⟨target, code⟩ ← encode layout source
        return ⟨target, code,
          .native (@CTMLCore.Subtype.hyp ⟨layout.depth, guards⟩
            (WFConstraint.constr (layout.precise _) target) (translated.contains lookup code))⟩
    | .andIntro first second => do
        let left ← pathTyping translated first
        let right ← pathTyping translated second
        return ⟨_, .inter left.code right.code, interIntro left.proof right.proof⟩
    | .sub value bound => do
        let valueCode ← pathTyping translated value
        let boundCode ← subtyping translated bound
        return ⟨boundCode.sup, boundCode.supCode,
          valueCode.proof.trans ((valueCode.code.unique boundCode.subCode).symm ▸ boundCode.proof)⟩
    | .self _ => do
        let ⟨_, .singleton named complete⟩ ← encode layout (.sngl path)
        return ⟨_, .singleton named complete, .native .refl⟩
    | .sngl equality value => do
        let ⟨_, .singleton _ _, aliasProof⟩ ← pathTyping translated equality
        let valueCode ← pathTyping translated value
        return ⟨_, valueCode.code, aliasProof.trans valueCode.proof⟩
    | .newElim _ | .rcdIntro _ | .pathElim _ _ |
      .recIntro _ | .recElim _ => none

  /-- Translate the bound-related cases of the actual core-DOT subtyping derivation. -/
  def subtyping {layout : Layout} {context : Ctx}
      {guards : List (WFConstraint layout.depth)} (translated : ContextCode layout context guards)
      {sourceSub sourceSup : Typ} (derivation : Core.Subtyping context sourceSub sourceSup) :
      Option (SubtypingResult layout guards sourceSub sourceSup) :=
    match derivation with
    | .top => do
        let ⟨_, code⟩ ← encode layout sourceSub
        return ⟨_, _, code, .top, .native .leTop⟩
    | .bot => do
        let ⟨_, code⟩ ← encode layout sourceSup
        return ⟨_, _, .bot, code, .native .botLe⟩
    | .refl => do
        let ⟨_, code⟩ ← encode layout sourceSub
        return ⟨_, _, code, code, .native .refl⟩
    | .trans first second => do
        let left ← subtyping translated first
        let right ← subtyping translated second
        return ⟨left.sub, right.sup, left.subCode, right.supCode,
          left.proof.trans ((left.supCode.unique right.subCode).symm ▸ right.proof)⟩
    | @Core.Subtyping.andLeft _ _ leftSource rightSource => do
        let ⟨_, left⟩ ← encode layout leftSource
        let ⟨_, right⟩ ← encode layout rightSource
        return ⟨_, _, .inter left right, left, .native .interLeft⟩
    | @Core.Subtyping.andRight _ _ leftSource rightSource => do
        let ⟨_, left⟩ ← encode layout leftSource
        let ⟨_, right⟩ ← encode layout rightSource
        return ⟨_, _, .inter left right, right, .native .interRight⟩
    | .andIntro first second => do
        let left ← subtyping translated first
        let right ← subtyping translated second
        return ⟨left.sub, _, left.subCode, .inter left.supCode right.supCode,
          interIntro left.proof ((left.subCode.unique right.subCode).symm ▸ right.proof)⟩
    | @Core.Subtyping.typ _ _ _ _ _ _ label lower upper =>
        if present : label ∈ layout.labels then do
          let lowerCode ← subtyping translated lower
          let upperCode ← subtyping translated upper
          return ⟨_, _, .member present lowerCode.supCode upperCode.subCode,
            .member present lowerCode.subCode upperCode.supCode,
            memberVariance (layout.memberSlot label present)
              lowerCode.proof upperCode.proof (fun _ _ => .native .refl)⟩
        else none
    | .selLo member => do
        let value ← pathTyping translated member
        match value with
        | ⟨_, .member present lower _, proof⟩ =>
            match found : layout.witness _ _ with
            | none => none
            | some witness =>
                return ⟨_, witness, lower, .selection found,
                  memberLowerBound (layout.memberSlot _ present) (carrierPolicy_names layout.slots)
                    (.native .refl) (Layout.asSlot present found proof)⟩
    | .selHi member => do
        let value ← pathTyping translated member
        match value with
        | ⟨_, .member present _ upper, proof⟩ =>
            match found : layout.witness _ _ with
            | none => none
            | some witness =>
                return ⟨witness, _, .selection found, upper,
                  memberUpperBound (layout.memberSlot _ present) (carrierPolicy_names layout.slots)
                    (.native .refl) (Layout.asSlot present found proof)⟩
    | .snglPQ equality _ _ | .snglQP equality _ _ => do
        let ⟨_, .singleton _ _, equalityProof⟩ ← pathTyping translated equality
        let ⟨_, subCode⟩ ← encode layout sourceSub
        let ⟨_, supCode⟩ ← encode layout sourceSup
        let replacement ← subCode.transport equalityProof supCode
        return ⟨_, _, subCode, supCode, replacement.forward⟩
    | .fld _ | .all _ _ _ => none
end

def typeLabels : Typ → List Signature.TypLabel
  | .top | .bot | .sngl _ => []
  | .path _ label => [label]
  | .and left right | .all left right => typeLabels left ++ typeLabels right
  | .bnd body | .rcd (.trm _ body) => typeLabels body
  | .rcd (.typ label lower upper) => label :: (typeLabels lower ++ typeLabels upper)

def eventLabels : MemberUses.Event → List Signature.TypLabel
  | .typeUse use => typeLabels use.type
  | event => event.support.map MemberUses.MemberKey.label

def namedPath (scope : MemberUses.Scope) : Path → List MemberUses.PathKey
  | .select (.bound _) _ => []
  | .select (.free name) fields => [⟨scope.owner name, fields⟩]

def typePaths (scope : MemberUses.Scope) : Typ → List MemberUses.PathKey
  | .top | .bot => []
  | .path path _ | .sngl path => namedPath scope path
  | .and left right | .all left right => typePaths scope left ++ typePaths scope right
  | .bnd body | .rcd (.trm _ body) => typePaths scope body
  | .rcd (.typ _ lower upper) => typePaths scope lower ++ typePaths scope upper

def eventPaths (event : MemberUses.Event) : List MemberUses.PathKey :=
  (event.context.flatMap (fun binding =>
    ⟨event.scope.owner binding.1, []⟩ :: typePaths event.scope binding.2)) ++
  match event with
  | .typeUse use => typePaths use.scope use.type
  | .alias equality => [equality.leftKey, equality.rightKey]
  | other => other.support.map MemberUses.MemberKey.path

def labels (events : List MemberUses.Event) : List Signature.TypLabel :=
  (events.flatMap eventLabels).eraseDups

def paths (events : List MemberUses.Event) : List MemberUses.PathKey :=
  (events.flatMap eventPaths).eraseDups

structure Key where
  path : MemberUses.PathKey
  slot : Option Signature.TypLabel
  deriving DecidableEq

def slots (events : List MemberUses.Event) : List (Option Signature.TypLabel) :=
  none :: (labels events).map some

/-- Allocate the runtime type and every member of each relevant precise row. -/
def keys (events : List MemberUses.Event) : List Key :=
  (paths events).flatMap (fun path => (slots events).map (fun slot => ⟨path, slot⟩))

theorem key_present {events : List MemberUses.Event} {path : MemberUses.PathKey}
    {slot : Option Signature.TypLabel} (pathPresent : path ∈ paths events)
    (slotPresent : slot ∈ slots events) : (⟨path, slot⟩ : Key) ∈ keys events :=
  List.mem_flatMap.mpr ⟨path, pathPresent, List.mem_map.mpr ⟨slot, slotPresent, rfl⟩⟩

def witnessAt (events : List MemberUses.Event) (scope : MemberUses.Scope) (path : Path)
    (slot : Option Signature.TypLabel) : Option (WFTy (keys events).length) :=
  match path with
  | .select (.bound _) _ => none
  | .select (.free name) fields =>
      let key : Key := ⟨⟨scope.owner name, fields⟩, slot⟩
      if present : key ∈ keys events then
        some (WFTy.var ((keys events).idxOf key) (List.idxOf_lt_length_of_mem present))
      else none

/-- Source selections use one scoped allocation shared by all their views. -/
def Layout.ofEvents (events : List MemberUses.Event) (scope : MemberUses.Scope) : Layout where
  depth := (keys events).length
  labels := CarrierTranslation.labels events
  witness path label := witnessAt events scope path (some label)
  payload path := witnessAt events scope path none

theorem Layout.ofEvents_complete {events : List MemberUses.Event} {scope : MemberUses.Scope}
    {name : Var} {fields : Fields}
    (present : (⟨scope.owner name, fields⟩ : MemberUses.PathKey) ∈ paths events) :
    (Layout.ofEvents events scope).completeAt (.select (.free name) fields) = true := by
  apply List.all_eq_true.mpr
  intro label labelPresent
  cases label
  all_goals
    simp only [Layout.component, Layout.ofEvents, witnessAt,
      dite_eq_left (key_present present labelPresent), Option.isSome_some]

def contextEvents (context : Ctx) : List MemberUses.Event :=
  context.map (fun binding => .typeUse ⟨[], context, binding.2⟩)

structure CompiledSubtyping (context : Ctx) (sourceSub sourceSup : Typ) where
  layout : Layout
  guards : List (WFConstraint layout.depth)
  contextCode : ContextCode layout context guards
  result : SubtypingResult layout guards sourceSub sourceSup

/-- Generate the layout and guards, then check the actual source derivation. -/
def compileSubtyping {context : Ctx} {sourceSub sourceSup : Typ}
    (derivation : Core.Subtyping context sourceSub sourceSup) :
    Option (CompiledSubtyping context sourceSub sourceSup) := do
  let layout := Layout.ofEvents
    (contextEvents context ++ MemberUses.subtyping derivation [] []) []
  let ⟨guards, contextCode⟩ ← encodeContext layout context
  let result ← subtyping contextCode derivation
  return ⟨layout, guards, contextCode, result⟩

/-- A generated ghost bound has the corresponding checked identity coercion. -/
theorem SubtypingResult.identityTyping {layout : Layout}
    {guards : List (WFConstraint layout.depth)} {sourceSub sourceSup : Typ}
    (result : SubtypingResult layout guards sourceSub sourceSup) :
    CTML.Mixed.HasType carrierPolicy ⟨layout.depth, guards⟩ TypingContext.empty
      (.abs (.var 0)) (WFTy.arrow result.sub result.sup) :=
  .abstraction (.subsumption (.native (.var _ _ _ .here)) result.proof)

omit [Signature] in
def abstractGuards {depth : Nat} (guards : List (WFConstraint depth))
    (body : WFTy depth) : WFTy depth :=
  guards.foldl (fun type guard => WFTy.constrained guard type) body

omit [Signature] in
theorem abstractGuards_typing {depth : Nat} (guards : List (WFConstraint depth))
    {body : WFTy depth}
    (typing : CTML.Mixed.HasType carrierPolicy ⟨depth, guards⟩ TypingContext.empty
      (.abs (.var 0)) body) :
    CTML.Mixed.HasType carrierPolicy ⟨depth, []⟩ TypingContext.empty (.abs (.var 0))
      (abstractGuards guards body) :=
  match guards with
  | [] => typing
  | guard :: rest => abstractGuards_typing rest
      (.constrained (s := ⟨depth, rest⟩) guard _ _ _ (.value (.abs _)) typing)

omit [Signature] in
def abstractTypes : (depth : Nat) → WFTy depth → WFTy 0
  | 0, type => type
  | depth + 1, type => abstractTypes depth (WFTy.all type)

omit [Signature] in
theorem abstractTypes_typing {depth : Nat} {type : WFTy depth}
    (typing : CTML.Mixed.HasType carrierPolicy ⟨depth, []⟩ TypingContext.empty
      (.abs (.var 0)) type) :
    CTML.Mixed.HasType carrierPolicy SubtypingContext.empty TypingContext.empty (.abs (.var 0))
      (abstractTypes depth type) :=
  match depth with
  | 0 => typing
  | predecessor + 1 => abstractTypes_typing (depth := predecessor) (type := WFTy.all type)
      (.forall (s := ⟨predecessor, []⟩) TypingContext.empty (.abs (.var 0)) type
        (.value (.abs _)) typing)

def CompiledSubtyping.closedType {context : Ctx} {sourceSub sourceSup : Typ}
    (compiled : CompiledSubtyping context sourceSub sourceSup) : WFTy 0 :=
  abstractTypes compiled.layout.depth
    (abstractGuards compiled.guards (WFTy.arrow compiled.result.sub compiled.result.sup))

/-- Both witness and constraint abstractions are generated from the source context. -/
theorem CompiledSubtyping.closedTyping {context : Ctx} {sourceSub sourceSup : Typ}
    (compiled : CompiledSubtyping context sourceSub sourceSup) :
    CTML.Mixed.HasType carrierPolicy SubtypingContext.empty TypingContext.empty (.abs (.var 0))
      compiled.closedType :=
  abstractTypes_typing (abstractGuards_typing compiled.guards compiled.result.identityTyping)

end CDotFCCT.CarrierTranslation
