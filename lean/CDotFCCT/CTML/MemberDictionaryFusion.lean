import CDotFCCT.CTML.MemberDictionaryPrototype

/-!
# Separate dictionary packages still lose a member's identity

The same closed record containing two identity functions supports both exact
member views, using `Top` in one existential and `Bottom` in the other. The record
therefore provides genuine administrative dictionaries, yet separate packaging
does not synchronize their witnesses. It cannot be converted, while retaining
that value, to a package with one witness between `Top` and `Bottom`.

This is the member-only opaque-selection case from `SharedWitnessRegression`.
The `a : C` and `asA : C → A` fields of the earlier prototype cannot be required
for arbitrary member-only source views. A successful compiler needs a canonical
witness scope preserved by both upper-bound views, not merely typed dictionaries.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.MemberDictionaryFusion

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

def boundsType {depth : Nat} (lower witness upper : WFTy depth) : WFTy depth :=
  recordResultType "$MemberBounds"
    [("lo", WFTy.arrow lower witness), ("hi", WFTy.arrow witness upper)]

def dictionary : Term :=
  .record "$MemberBounds" (.cons "lo" MemberDictionaryPrototype.identity
    (.cons "hi" MemberDictionaryPrototype.identity .nil (by decide)) (by decide))

def exactView {depth : Nat} (endpoint : WFTy depth) : Interface depth :=
  .bind (.payload (boundsType endpoint.weaken (WFTy.var 0 (by omega)) endpoint.weaken))

theorem boundsType_substAt {depth : Nat} (lower witness upper : WFTy (depth + 1))
    (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (boundsType lower witness upper).substAt index valid replacement =
      boundsType (lower.substAt index valid replacement) (witness.substAt index valid replacement)
        (upper.substAt index valid replacement) := by
  simp only [boundsType, recordResultType, List.foldl_cons, List.foldl_nil,
    WFTy.intersection, WFTy.substAt_joint, WFTy.substAt_record, WFTy.substAt_arrow]
  rfl

/-- Both functions are identity casts; no looping or arbitrary dictionary input is used. -/
theorem dictionaryTyping {s : SubtypingContext} (context : TypingContext s.typeDepth)
    (witness : WFTy s.typeDepth) :
    HasType s context dictionary (boundsType witness witness witness) :=
  .record (.cons (MemberDictionaryPrototype.identityTyping .refl)
    (.cons (MemberDictionaryPrototype.identityTyping .refl) .nil))

def exactInstance (s : SubtypingContext) (endpoint : WFTy s.typeDepth) :
    Interface.Instance s (exactView endpoint) (boundsType endpoint endpoint endpoint) := by
  refine .bind endpoint ?_
  simp only [Interface.instantiate, Interface.substAt, boundsType_substAt]
  change Interface.Instance s
    (.payload (boundsType (endpoint.weaken.instantiate endpoint) endpoint
      (endpoint.weaken.instantiate endpoint))) (boundsType endpoint endpoint endpoint)
  rw [WFTy.weaken_instantiate_cancel]
  exact .payload _

def independentlyPacked : Term := pack dictionary

def independentViews (answer : WFTy 0) : WFTy 0 :=
  WFTy.intersection ((exactView WFTy.top).package answer)
    ((exactView WFTy.bottom).package answer)

/-- One and the same generated native dictionary supplies both independent packages. -/
theorem bothPackageViews (answer : WFTy 0) :
    HasType SubtypingContext.empty TypingContext.empty independentlyPacked
      (independentViews answer) :=
  .intersection
    (Interface.packTyping (exactInstance _ WFTy.top) (dictionaryTyping _ WFTy.top))
    (Interface.packTyping (exactInstance _ WFTy.bottom) (dictionaryTyping _ WFTy.bottom))

/-- The selected opaque type carries two independent upper-bound coercions. -/
def ownerType {depth : Nat} (selected first second : WFTy depth) : WFTy depth :=
  recordResultType "$OpaqueOwner"
    [("loX", WFTy.arrow WFTy.bottom selected), ("hi1X", WFTy.arrow selected first),
      ("hi2X", WFTy.arrow selected second)]

def owner : Term :=
  .record "$OpaqueOwner" (.cons "loX" MemberDictionaryPrototype.identity
    (.cons "hi1X" MemberDictionaryPrototype.identity
      (.cons "hi2X" MemberDictionaryPrototype.identity .nil (by decide)) (by decide)) (by decide))

def environmentType {depth : Nat} (selected first second : WFTy depth) : WFTy depth :=
  recordResultType "$OpaqueContext" [("owner", ownerType selected first second), ("q", selected)]

def environment : Term :=
  .record "$OpaqueContext" (.cons "owner" owner
    (.cons "q" independentlyPacked .nil (by decide)) (by decide))

def opaqueInterface {depth : Nat} (first second : WFTy depth) : Interface depth :=
  .bind (.payload (environmentType (WFTy.var 0 (by omega)) first.weaken second.weaken))

theorem environmentType_substAt {depth : Nat} (selected first second : WFTy (depth + 1))
    (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (environmentType selected first second).substAt index valid replacement =
      environmentType (selected.substAt index valid replacement)
        (first.substAt index valid replacement) (second.substAt index valid replacement) := by
  simp only [environmentType, ownerType, recordResultType, List.foldl_cons, List.foldl_nil,
    WFTy.intersection, WFTy.substAt_joint, WFTy.substAt_record, WFTy.substAt_arrow,
    WFTy.bottom, WFTy.substAt_extremum]
  rfl

def opaqueInstance (s : SubtypingContext) (selected first second : WFTy s.typeDepth) :
    Interface.Instance s (opaqueInterface first second)
      (environmentType selected first second) := by
  refine .bind selected ?_
  simp only [Interface.instantiate, Interface.substAt, environmentType_substAt]
  change Interface.Instance s
    (.payload (environmentType selected (first.weaken.instantiate selected)
      (second.weaken.instantiate selected))) (environmentType selected first second)
  rw [WFTy.weaken_instantiate_cancel, WFTy.weaken_instantiate_cancel]
  exact .payload _

/-- Both owner-bound coercions are generated identities on the same chosen `X`. -/
theorem ownerTyping {s : SubtypingContext} (context : TypingContext s.typeDepth)
    (first second : WFTy s.typeDepth) :
    HasType s context owner (ownerType (WFTy.intersection first second) first second) :=
  .record (.cons (MemberDictionaryPrototype.identityTyping (.extremum .bottom))
    (.cons (MemberDictionaryPrototype.identityTyping .interLeft)
      (.cons (MemberDictionaryPrototype.identityTyping .interRight) .nil)))

theorem environmentTyping (answer : WFTy 0) :
    HasType SubtypingContext.empty TypingContext.empty environment
      (environmentType (independentViews answer)
        ((exactView WFTy.top).package answer) ((exactView WFTy.bottom).package answer)) :=
  .record (.cons (ownerTyping _ _ _) (.cons (bothPackageViews answer) .nil))

/-- Even hiding `X` once does not synchronize `A` inside its independently hidden upper views. -/
theorem opaqueEnvironmentPackage (answer result : WFTy 0) :
    HasType SubtypingContext.empty TypingContext.empty (pack environment)
      ((opaqueInterface ((exactView WFTy.top).package answer)
        ((exactView WFTy.bottom).package answer)).package result) :=
  @Interface.packTyping SubtypingContext.empty TypingContext.empty
    (opaqueInterface ((exactView WFTy.top).package answer)
      ((exactView WFTy.bottom).package answer))
    (environmentType (independentViews answer) ((exactView WFTy.top).package answer)
      ((exactView WFTy.bottom).package answer)) result environment
    (opaqueInstance SubtypingContext.empty (independentViews answer)
      ((exactView WFTy.top).package answer) ((exactView WFTy.bottom).package answer))
    (environmentTyping answer)

def upperView (field : FieldName) (object : Term) : Term :=
  .app (.proj (.proj object "owner") field) (.proj object "q")

theorem upperFirstTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {object : Term} {selected first second : WFTy s.typeDepth}
    (typing : HasType s context object (environmentType selected first second)) :
    HasType s context (upperView "hi1X" object) first :=
  .application
    (.projection ((HasType.projection
      (typing.subsumption (.trans .interLeft .interRight))).subsumption
        (.trans .interLeft .interRight))) (.projection (typing.subsumption .interRight))

theorem upperSecondTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {object : Term} {selected first second : WFTy s.typeDepth}
    (typing : HasType s context object (environmentType selected first second)) :
    HasType s context (upperView "hi2X" object) second :=
  .application
    (.projection ((HasType.projection
      (typing.subsumption (.trans .interLeft .interRight))).subsumption .interRight))
    (.projection (typing.subsumption .interRight))

theorem ownerValue : Value owner :=
  .record _ _ (.cons (.abs _) (.cons (.abs _) (.cons (.abs _) .nil)))

theorem environmentValue : Value environment :=
  .record _ _ (.cons ownerValue (.cons (.abs _) .nil))

/-- Each opaque-bound coercion returns exactly the same selected value `q`. -/
theorem upperFirstSteps : Steps (upperView "hi1X" environment) independentlyPacked := by
  refine .trans (.appHead _ (.projHead _ (.proj environmentValue .here))) ?_
  refine .trans (.appHead _ (.proj ownerValue (.there .here))) ?_
  refine .trans (.appArg (.abs _) (.proj environmentValue (.there .here))) ?_
  exact .single (MemberDictionaryPrototype.identityStep (.abs _))

theorem upperSecondSteps : Steps (upperView "hi2X" environment) independentlyPacked := by
  refine .trans (.appHead _ (.projHead _ (.proj environmentValue .here))) ?_
  refine .trans (.appHead _ (.proj ownerValue (.there (.there .here)))) ?_
  refine .trans (.appArg (.abs _) (.proj environmentValue (.there .here))) ?_
  exact .single (MemberDictionaryPrototype.identityStep (.abs _))

def sharedView : Interface 0 :=
  .bind (.payload (boundsType WFTy.top (WFTy.var 0 (by decide)) WFTy.bottom))

def through (object value : Term) : Term :=
  .app (.proj object "hi") (.app (.proj object "lo") value)

theorem throughTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {object value : Term} {lower witness upper : WFTy s.typeDepth}
    (objectTyping : HasType s context object (boundsType lower witness upper))
    (valueTyping : HasType s context value lower) :
    HasType s context (through object value) upper :=
  .application (.projection (objectTyping.subsumption .interRight))
    (.application (.projection (objectTyping.subsumption (.trans .interLeft .interRight)))
      valueTyping)

def unit : Term := .record "$Unit" .nil

def reject : Term := .abs (.app (through (.var 0) unit) unit)

/-- A single witness lets a client compose the two dictionaries from `Top` to `Bottom`. -/
theorem rejectTyping (answer : WFTy 0) :
    HasType SubtypingContext.empty TypingContext.empty reject (sharedView.consumer answer) := by
  apply Interface.consumerTyping
  change HasType SubtypingContext.empty.bindType
    (TypingContext.empty.bind (boundsType WFTy.top (WFTy.var 0 (by decide)) WFTy.bottom))
    (.app (through (.var 0) unit) unit) answer.weaken
  exact .application
    ((throughTyping (.var _ 0 _ .here)
      ((HasType.record .nil).subsumption (.extremum .top))).subsumption (.extremum .bottom))
    ((HasType.record .nil).subsumption (.extremum .top))

theorem dictionaryValue : Value dictionary :=
  .record _ _ (.cons (.abs _) (.cons (.abs _) .nil))

/-- The two bound dictionaries are actual administrative identities, even before packaging. -/
theorem throughSteps {value : Term} (isValue : Value value) :
    Steps (through dictionary value) value := by
  refine .trans (.appHead _ (.proj dictionaryValue (.there .here))) ?_
  refine .trans (.appArg (.abs _) (.appHead _ (.proj dictionaryValue .here))) ?_
  refine .trans (.appArg (.abs _) (MemberDictionaryPrototype.identityStep isValue)) ?_
  exact .single (MemberDictionaryPrototype.identityStep isValue)

theorem rejectSteps : Steps (.app independentlyPacked reject) (.app unit unit) := by
  refine .trans (.appBeta _ _ (.abs _)) ?_
  change Steps (.app reject ((dictionary.lift 1).substAt 0 reject)) _
  rw [Term.lift_substAt_cancel]
  refine .trans (.appBeta _ _ dictionaryValue) ?_
  exact (throughSteps (.record _ _ .nil)).appHead unit

private theorem unitApplicationNoStep {term : Term} : ¬ Step (.app unit unit) term := by
  intro step
  cases step with
  | appHead _ step => exact (Value.record _ _ .nil).not_step step
  | appArg _ step => exact (Value.record _ _ .nil).not_step step

/-- Independent witnesses cannot be identified even though all dictionaries are identities. -/
theorem noSharedPackage (answer : WFTy 0) :
    ¬ HasType SubtypingContext.empty TypingContext.empty independentlyPacked
      (sharedView.package answer) := by
  intro typing
  have program := HasType.application typing (rejectTyping answer)
  rcases (program.soundness rejectSteps).2 with value | ⟨_, step⟩
  · cases value
  · exact unitApplicationNoStep step

theorem noValuePreservingFusion (answer : WFTy 0) {convert : Term}
    (typing : HasType SubtypingContext.empty TypingContext.empty convert
      (WFTy.arrow (independentViews answer) (sharedView.package answer)))
    (identity : Steps (.app convert independentlyPacked) independentlyPacked) : False :=
  noSharedPackage answer
    ((HasType.application typing (bothPackageViews answer)).soundness identity).1

end CDotFCCT.CTML.MemberDictionaryFusion
