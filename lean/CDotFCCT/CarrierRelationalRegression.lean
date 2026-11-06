import CDotFCCT.RecursiveCarrierBoundObstruction
import CDotFCCT.CTML.CarrierRelationSlots
import CDotFCCT.CTML.CarrierEquationInterpretation

/-!
# An opaque recursive upper bound with a computed correlation slot

The source derivation is exactly the earlier `q.X` regression: the upper bound
`μself.({A:Bottom..Top} & {a:self.A})` makes the unknown subject's child lie below
its own member. The augmented code row adds `relation = ¬child ∪ member`.
The recursive view requires `Top` in that slot and independently requires field
presence. The relation is computed; it is not another independent witness.

The target scope below separates the two source-binding constraints, a generated
pure equation for the relation name, and a code-completeness constraint on the
child. It never assumes `child ≤ member`. This is a checked representation test
for the existing source derivation, not a general recursive source-type compiler.
-/

set_option autoImplicit false

namespace CDotFCCT.CarrierRelationalRegression

open CTMLCore CTMLCore.Syntax CTML.Mixed CTML.Mixed.CarrierRelationSlots
open CTML.Mixed.CarrierLayout

local instance : CDot.Signature where
  TypLabel := String
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

/-- Reuse the actual source typing derivation from the previous obstruction. -/
def sourceDerivation := RecursiveCarrierBoundObstruction.dependentField

theorem sourceJudgment :
    CDot.Typed RecursiveCarrierBoundObstruction.sourceContext
      (.path ((CDot.Path.var 1).selectField "a")) (.path (.var 1) "A") := sourceDerivation.source

inductive Label where
  | memberX | memberA | presence | child | relation
  deriving DecidableEq

def support : List Label := [.memberX, .memberA, .presence, .child, .relation]

theorem present (label : Label) : label ∈ support := by cases label <;> simp [support]

def memberSlot (label : Label) : CTML.Transparent.MemberSlot (names support) :=
  slot support label (present label)

def subjectComponents {depth : Nat} (member child presence relation : WFTy depth) :
    Label → WFTy depth
  | .memberX => WFTy.top
  | .memberA => member
  | .presence => presence
  | .child => child
  | .relation => relation

def ownerComponents {depth : Nat} (selected : WFTy depth) : Label → WFTy depth
  | .memberX => selected
  | .memberA => WFTy.top
  | .presence => WFTy.bottom
  | .child => WFTy.top
  | .relation => residual WFTy.top WFTy.top

def subjectCode {depth : Nat} (member child presence relation : WFTy depth) : WFTy depth :=
  precise support (subjectComponents member child presence relation)

def ownerCode {depth : Nat} (selected : WFTy depth) : WFTy depth :=
  precise support (ownerComponents selected)

/-- The code of the recursive body is uniform in the subject's unknown witnesses. -/
def recursiveView {depth : Nat} : WFTy depth :=
  WFTy.intersection
    ((memberSlot .memberA).view WFTy.bottom WFTy.top (fun _ => WFTy.top))
    (WFTy.intersection
      ((memberSlot .presence).view WFTy.top WFTy.top (fun _ => WFTy.top))
      ((memberSlot .relation).view WFTy.top WFTy.top (fun _ => WFTy.top)))

def ownerView {depth : Nat} : WFTy depth :=
  (memberSlot .memberX).view WFTy.bottom recursiveView (fun _ => WFTy.top)

def ownerBinding {depth : Nat} (selected : WFTy depth) : WFConstraint depth :=
  WFConstraint.constr (ownerCode selected) ownerView

def subjectBinding {depth : Nat} (member child presence relation selected : WFTy depth) :
    WFConstraint depth := WFConstraint.constr (subjectCode member child presence relation) selected

theorem upperFromOwner {s : SubtypingContext} {selected : WFTy s.typeDepth}
    (owner : InvertingSubtype carrierPolicy s (ownerCode selected) ownerView) :
    InvertingSubtype carrierPolicy s selected recursiveView := by
  change InvertingSubtype carrierPolicy s (precise support (ownerComponents selected)) _ at owner
  exact memberUpperBound (memberSlot .memberX) (carrierPolicy_names support) (.native .refl)
    (precise_eq_slot (present .memberX) (ownerComponents selected) ▸ owner)

/-- The two original source bindings expose presence and the computed residual of one subject. -/
theorem expose {s : SubtypingContext}
    {member child presence relation selected : WFTy s.typeDepth}
    (owner : InvertingSubtype carrierPolicy s (ownerCode selected) ownerView)
    (subject : InvertingSubtype carrierPolicy s
      (subjectCode member child presence relation) selected) :
    InvertingSubtype carrierPolicy s WFTy.top presence ∧
      InvertingSubtype carrierPolicy s WFTy.top relation := by
  have view := subject.trans (upperFromOwner owner)
  have presenceView := view.trans (.native (.trans .interRight .interLeft))
  have relationView := view.trans (.native (.trans .interRight .interRight))
  change InvertingSubtype carrierPolicy s
    (precise support (subjectComponents member child presence relation)) _
    at presenceView relationView
  exact ⟨memberLowerBound (memberSlot .presence) (carrierPolicy_names support) (.native .refl)
      (precise_eq_slot (present .presence)
        (subjectComponents member child presence relation) ▸ presenceView),
    memberLowerBound (memberSlot .relation) (carrierPolicy_names support) (.native .refl)
      (precise_eq_slot (present .relation)
        (subjectComponents member child presence relation) ▸ relationView)⟩

theorem extract {s : SubtypingContext}
    {member child presence relation selected : WFTy s.typeDepth}
    (owner : InvertingSubtype carrierPolicy s (ownerCode selected) ownerView)
    (subject : InvertingSubtype carrierPolicy s
      (subjectCode member child presence relation) selected)
    (completeChild : InvertingSubtype carrierPolicy s WFTy.top (complete child))
    (computed : InvertingSubtype carrierPolicy s relation (residual child member)) :
    InvertingSubtype carrierPolicy s child member ∧
      InvertingSubtype carrierPolicy s WFTy.top presence :=
  let visible := expose owner subject
  ⟨elimResidual completeChild (visible.2.trans computed), visible.1⟩

private theorem meet {s : SubtypingContext} {sub left right : WFTy s.typeDepth}
    (first : InvertingSubtype carrierPolicy s sub left)
    (second : InvertingSubtype carrierPolicy s sub right) :
    InvertingSubtype carrierPolicy s sub (WFTy.intersection left right) :=
  .nativeWith [WFConstraint.constr sub left, WFConstraint.constr sub right]
    (.leInter
      (@Subtype.hyp ⟨s.typeDepth,
        [WFConstraint.constr sub left, WFConstraint.constr sub right]⟩ _ List.mem_cons_self)
      (@Subtype.hyp ⟨s.typeDepth,
        [WFConstraint.constr sub left, WFConstraint.constr sub right]⟩ _
        (List.mem_cons_of_mem _ List.mem_cons_self)))
    (fun _ member => (List.mem_cons.mp member).elim (fun equal => equal.symm ▸ first)
      (fun tail => (List.mem_singleton.mp tail).symm ▸ second))

/-- Producer introduction uses the same generated slot convention as elimination. -/
theorem ownerIntro {s : SubtypingContext} {selected : WFTy s.typeDepth}
    (upper : InvertingSubtype carrierPolicy s selected recursiveView) :
    InvertingSubtype carrierPolicy s (ownerCode selected) ownerView := by
  rw [ownerCode, precise_eq_slot (label := Label.memberX) (present .memberX)]
  exact memberVariance (memberSlot .memberX) (.native .botLe) upper
    (fun _ _ => .native .leTop)

theorem subjectIntro {s : SubtypingContext}
    (member child presence relation : WFTy s.typeDepth)
    (fieldPresent : InvertingSubtype carrierPolicy s WFTy.top presence)
    (related : InvertingSubtype carrierPolicy s WFTy.top relation) :
    InvertingSubtype carrierPolicy s (subjectCode member child presence relation)
      recursiveView := by
  have memberView : InvertingSubtype carrierPolicy s
      (subjectCode member child presence relation)
      ((memberSlot .memberA).view WFTy.bottom WFTy.top (fun _ => WFTy.top)) := by
    rw [subjectCode, precise_eq_slot (label := Label.memberA) (present .memberA)]
    exact memberVariance (memberSlot .memberA) (.native .botLe) (.native .leTop)
      (fun _ _ => .native .leTop)
  have presenceView : InvertingSubtype carrierPolicy s
      (subjectCode member child presence relation)
      ((memberSlot .presence).view WFTy.top WFTy.top (fun _ => WFTy.top)) := by
    rw [subjectCode, precise_eq_slot (label := Label.presence) (present .presence)]
    exact memberVariance (memberSlot .presence) fieldPresent (.native .leTop)
      (fun _ _ => .native .leTop)
  have relationView : InvertingSubtype carrierPolicy s
      (subjectCode member child presence relation)
      ((memberSlot .relation).view WFTy.top WFTy.top (fun _ => WFTy.top)) := by
    rw [subjectCode, precise_eq_slot (label := Label.relation) (present .relation)]
    exact memberVariance (memberSlot .relation) related (.native .leTop)
      (fun _ _ => .native .leTop)
  exact meet memberView (meet presenceView relationView)

/-- The extra slot is a computed pure equation, not an independently chosen scalar. -/
def relationSystem {depth : Nat} (member child : WFTy depth) :
    CarrierEquation.System carrierPolicy depth 1 where
  body _ := .union (.neg (.leaf child)) (.leaf member)
  guarded _ := ⟨trivial, trivial⟩

def relationName {depth : Nat} (member child : WFTy depth) : WFTy (depth + 1) :=
  (relationSystem member child).name ⟨0, by decide⟩

theorem relationSystem_compile {depth : Nat} (member child : WFTy depth) :
    ((relationSystem member child).compile ⟨0, by decide⟩) =
      residual child.weaken member.weaken := by
  change WFTy.union (WFTy.neg (child.weakenBy 1)) (member.weakenBy 1) = _
  simp only [WFTy.weakenBy_succ, WFTy.weakenBy_zero]
  rfl

/-- Completeness is code-universe metadata, separated from both source bindings. -/
def codeContext (s : SubtypingContext) (child : WFTy s.typeDepth) : SubtypingContext :=
  s.assume (WFConstraint.constr WFTy.top (complete child))

def equationContext (s : SubtypingContext) (member child : WFTy s.typeDepth) : SubtypingContext :=
  (relationSystem member child).openContext (codeContext s child)

/-- Only the two source bindings are added after the generated code/equation scope. -/
def context (s : SubtypingContext) (member child presence selected : WFTy s.typeDepth) :
    SubtypingContext :=
  ((equationContext s member child).assume (ownerBinding selected.weaken)).assume
    (subjectBinding member.weaken child.weaken presence.weaken
      (relationName member child) selected.weaken)

theorem generatedOwner (s : SubtypingContext)
    (member child presence selected : WFTy s.typeDepth) :
    Subtype (context s member child presence selected) (ownerCode selected.weaken) ownerView :=
  @Subtype.hyp (context s member child presence selected) (ownerBinding selected.weaken)
    (List.mem_cons_of_mem _ List.mem_cons_self)

theorem generatedSubject (s : SubtypingContext)
    (member child presence selected : WFTy s.typeDepth) :
    Subtype (context s member child presence selected)
      (subjectCode member.weaken child.weaken presence.weaken (relationName member child))
      selected.weaken :=
  @Subtype.hyp (context s member child presence selected)
    (subjectBinding member.weaken child.weaken presence.weaken
      (relationName member child) selected.weaken) List.mem_cons_self

/-- The computed relation is unfolded from the actual pure-system equation list. -/
theorem generatedRelation (s : SubtypingContext)
    (member child presence selected : WFTy s.typeDepth) :
    Subtype (context s member child presence selected)
      (relationName member child) (residual child.weaken member.weaken) := by
  have base := (relationSystem member child).unfold (codeContext s child) ⟨0, by decide⟩
  have unfolded := (base.weakenAssumption (ownerBinding selected.weaken)).weakenAssumption
      (subjectBinding member.weaken child.weaken presence.weaken
        (relationName member child) selected.weaken)
  change Subtype (context s member child presence selected) (relationName member child)
    ((relationSystem member child).compile ⟨0, by decide⟩) at unfolded
  rw [relationSystem_compile] at unfolded
  exact unfolded

/-- The only additional bound is the weakened code-completeness guard, not the sought relation. -/
theorem generatedCompleteness (s : SubtypingContext)
    (member child presence selected : WFTy s.typeDepth) :
    Subtype (context s member child presence selected) WFTy.top (complete child.weaken) := by
  let guard := WFConstraint.constr WFTy.top (complete child)
  have membership : guard.weakenBy 1 ∈ (equationContext s member child).assumptions :=
    List.mem_append_right _ (List.mem_map.mpr ⟨guard, List.mem_cons_self, rfl⟩)
  have base := @Subtype.hyp (equationContext s member child) (guard.weakenBy 1) membership
  have lifted := (base.weakenAssumption (ownerBinding selected.weaken)).weakenAssumption
      (subjectBinding member.weaken child.weaken presence.weaken
        (relationName member child) selected.weaken)
  change Subtype (context s member child presence selected)
    (WFTy.top.weakenBy 1) ((complete child).weakenBy 1) at lifted
  rw [WFTy.weakenBy_succ, WFTy.weakenBy_zero,
    WFTy.weakenBy_succ, WFTy.weakenBy_zero] at lifted
  exact lifted

/-- The opaque recursive source bound yields the same subject's child/member relation and presence.
No target `child ≤ member` or `Top ≤ residual` premise is an input to this theorem. -/
theorem dependentFieldCode (s : SubtypingContext)
    (member child presence selected : WFTy s.typeDepth) :
    InvertingSubtype carrierPolicy (context s member child presence selected)
        child.weaken member.weaken ∧
      InvertingSubtype carrierPolicy (context s member child presence selected)
        WFTy.top presence.weaken :=
  extract (.native (generatedOwner s member child presence selected))
    (.native (generatedSubject s member child presence selected))
    (.native (generatedCompleteness s member child presence selected))
    (.native (generatedRelation s member child presence selected))

private theorem equationCompleteness (s : SubtypingContext) (member child : WFTy s.typeDepth) :
    Subtype (equationContext s member child) WFTy.top (complete child.weaken) := by
  let guard := WFConstraint.constr WFTy.top (complete child)
  have membership : guard.weakenBy 1 ∈ (equationContext s member child).assumptions :=
    List.mem_append_right _ (List.mem_map.mpr ⟨guard, List.mem_cons_self, rfl⟩)
  have lifted := @Subtype.hyp (equationContext s member child) (guard.weakenBy 1) membership
  change Subtype (equationContext s member child)
    (WFTy.top.weakenBy 1) ((complete child).weakenBy 1) at lifted
  rw [WFTy.weakenBy_succ, WFTy.weakenBy_zero,
    WFTy.weakenBy_succ, WFTy.weakenBy_zero] at lifted
  exact lifted

private theorem equationFold (s : SubtypingContext) (member child : WFTy s.typeDepth) :
    Subtype (equationContext s member child)
      (residual child.weaken member.weaken) (relationName member child) := by
  have folded := (relationSystem member child).fold (codeContext s child) ⟨0, by decide⟩
  change Subtype (equationContext s member child)
    ((relationSystem member child).compile ⟨0, by decide⟩) (relationName member child) at folded
  rw [relationSystem_compile] at folded
  exact folded

/-- An exact child/member alias discharges both source guards before either is assumed.
The member remains arbitrary; only its code-completeness guard and generated equation are used. -/
theorem diagonalBindings (s : SubtypingContext) (member : WFTy s.typeDepth) :
    InvertingSubtype carrierPolicy (equationContext s member member)
        (ownerCode recursiveView) ownerView ∧
      InvertingSubtype carrierPolicy (equationContext s member member)
        (subjectCode member.weaken member.weaken WFTy.top (relationName member member))
        recursiveView := by
  have complemented : InvertingSubtype carrierPolicy (equationContext s member member)
      WFTy.top (complete member.weaken) := .native (equationCompleteness s member member)
  have residualBound : InvertingSubtype carrierPolicy (equationContext s member member)
      WFTy.top (residual member.weaken member.weaken) :=
    introResidual (s := equationContext s member member) complemented (.native .refl)
  have related : InvertingSubtype carrierPolicy (equationContext s member member)
      WFTy.top (relationName member member) :=
    residualBound.trans (.native (equationFold s member member))
  exact ⟨ownerIntro (s := equationContext s member member) (.native .refl),
    subjectIntro (s := equationContext s member member) member.weaken member.weaken WFTy.top
      (relationName member member) (.native .refl) related⟩

end CDotFCCT.CarrierRelationalRegression
