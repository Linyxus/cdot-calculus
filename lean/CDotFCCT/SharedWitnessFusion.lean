import CDotFCCT.SharedWitnessRegression
import CTMLCore.Declarative.IndexedFundamental

/-!
# Independent existential views cannot be fused by native subtyping

The obstruction persists inside native records. It is not just a failure to
choose a packing witness: the proposed package-fusion subtyping rule itself
contradicts CTML soundness, at every answer type. This rules out repairing this
particular encoding by adding sound subtyping inversions alone.
-/

set_option autoImplicit false

namespace CDotFCCT.SharedWitnessFusion

open CTMLCore CTML CTMLCore.Syntax CTMLCore.Evaluation SharedWitnessRegression

def sharedMember : Interface 0 :=
  .bind (.guard (WFConstraint.constr WFTy.top (WFTy.var 0 (by decide)))
    (.guard (WFConstraint.constr (WFTy.var 0 (by decide)) WFTy.bottom)
      (.payload WFTy.top)))

def reject : Term := .abs (.app (.var 0) (.var 0))

private def sharedName : WFTy 1 := WFTy.var 0 (by decide)

private abbrev sharedContext : SubtypingContext :=
  ⟨1, [WFConstraint.constr sharedName WFTy.bottom,
    WFConstraint.constr WFTy.top sharedName]⟩

private theorem sharedCollapse : Subtype sharedContext WFTy.top WFTy.bottom :=
  .trans (context := sharedContext) (middle := sharedName)
    (@Subtype.hyp sharedContext (WFConstraint.constr WFTy.top sharedName)
      (List.mem_cons_of_mem _ List.mem_cons_self))
    (@Subtype.hyp sharedContext (WFConstraint.constr sharedName WFTy.bottom)
      List.mem_cons_self)

/-- This consumer is legal only because it assumes both bounds on the same witness. -/
theorem rejectTyping (answer : WFTy 0) :
    HasType SubtypingContext.empty TypingContext.empty reject (sharedMember.consumer answer) := by
  apply Interface.consumerTyping
  change HasType sharedContext (TypingContext.empty.bind WFTy.top)
    (.app (.var 0) (.var 0)) answer.weaken
  exact .application ((HasType.var _ 0 _ .here).subsumption
    (.trans (context := sharedContext) sharedCollapse
      (Subtype.botLe (context := sharedContext) (type := WFTy.arrow WFTy.top answer.weaken))))
    (.var _ 0 _ .here)

theorem rejectSteps :
    Steps (.app independentlyPacked reject) (.app payload payload) :=
  .trans (.appBeta _ _ (.abs _)) (.trans (.appBeta _ _ (.record _ _ .nil)) .refl)

private theorem unitApplicationNoStep {term : Term} : ¬ Step (.app payload payload) term := by
  intro step
  cases step with
  | appHead _ step => exact (Value.record _ _ .nil).not_step step
  | appArg _ step => exact (Value.record _ _ .nil).not_step step

/-- The obstruction also holds when the producer uses scoped recursive types and Z. -/
theorem noRecursiveSharedPackage (answer : WFTy 0)
    (typing : Recursive.HasType SubtypingContext.empty TypingContext.empty independentlyPacked
      (sharedMember.package answer)) : False := by
  have program := Recursive.HasType.application typing (.native (rejectTyping answer))
  exact (program.safe rejectSteps).elim (fun value => nomatch value)
    (fun ⟨_, step⟩ => unitApplicationNoStep step)

/-- The shared package type cannot be assigned to the independently packed value. -/
theorem noSharedPackage (answer : WFTy 0)
    (typing : HasType SubtypingContext.empty TypingContext.empty independentlyPacked
      (sharedMember.package answer)) : False := by
  have program := HasType.application typing (rejectTyping answer)
  rcases (program.soundness rejectSteps).2 with value | ⟨_, step⟩
  · cases value
  · exact unitApplicationNoStep step

def independentViews (answer : WFTy 0) : WFTy 0 :=
  WFTy.intersection ((exactMember WFTy.top).package answer)
    ((exactMember WFTy.bottom).package answer)

/-- There is no native subtyping rule that merges these independently hidden witnesses. -/
theorem noPackageFusion (answer : WFTy 0) :
    ¬ Subtype SubtypingContext.empty (independentViews answer) (sharedMember.package answer) :=
  fun fusion => noSharedPackage answer ((bothPackageViews answer).subsumption fusion)

/-- An identity conversion cannot rescue the same independently packaged representation. -/
theorem noValuePreservingFusion (answer : WFTy 0) {convert : Term}
    (typing : HasType SubtypingContext.empty TypingContext.empty convert
      (WFTy.arrow (independentViews answer) (sharedMember.package answer)))
    (identity : Steps (.app convert independentlyPacked) independentlyPacked) : False :=
  noSharedPackage answer
    ((HasType.application typing (bothPackageViews answer)).soundness identity).1

/-- A conversion cannot evade witness sharing by adding local recursive declarations.
The argument uses operational safety of the whole client, without syntactic preservation. -/
theorem noRecursiveValuePreservingFusion (answer : WFTy 0) {convert : Term}
    (typing : Recursive.HasType SubtypingContext.empty TypingContext.empty convert
      (WFTy.arrow (independentViews answer) (sharedMember.package answer)))
    (identity : Steps (.app convert independentlyPacked) independentlyPacked) : False := by
  have program := Recursive.HasType.application
    (.application typing (.native (bothPackageViews answer))) (.native (rejectTyping answer))
  exact (program.safe ((identity.appHead reject).trans' rejectSteps)).elim
    (fun value => nomatch value) (fun ⟨_, step⟩ => unitApplicationNoStep step)

def fieldRecord : Term :=
  .record "Container" (.cons "child" independentlyPacked .nil (by decide))

def fieldViews (answer : WFTy 0) : WFTy 0 :=
  WFTy.intersection (WFTy.record "child" ((exactMember WFTy.top).package answer))
    (WFTy.record "child" ((exactMember WFTy.bottom).package answer))

theorem fieldRecordTyping (answer : WFTy 0) :
    HasType SubtypingContext.empty TypingContext.empty fieldRecord (fieldViews answer) :=
  (HasType.record (.cons (bothPackageViews answer) .nil)).subsumption
    (.trans .interRight (.leInter (.record .interLeft) (.record .interRight)))

/-- Native record intersections do not repair the independently packaged field encoding. -/
theorem noFieldFusion (answer : WFTy 0) :
    ¬ Subtype SubtypingContext.empty (fieldViews answer)
      (WFTy.record "child" (sharedMember.package answer)) := by
  intro fusion
  have projection := HasType.projection ((fieldRecordTyping answer).subsumption fusion)
  exact noSharedPackage answer
    (projection.preservation (.proj (.record _ _ (.cons (.abs _) .nil)) .here))

local instance : CDot.Signature where
  TypLabel := String
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

def sourceFieldContext : CDot.Ctx :=
  [(0, .and (.rcd (.trm "child" topView)) (.rcd (.trm "child" bottomView)))]

/-- DOT shares `p.child.A` across the two field views, even with no outer type member. -/
def sourceFieldCollapse : Core.Subtyping sourceFieldContext .top .bot :=
  .trans (.selLo (.newElim (.sub (.var .here) .andLeft)))
    (.selHi (.newElim (.sub (.var .here) .andRight)))

theorem sourceFieldCollapse_checked : CDot.Subtyp sourceFieldContext .top .bot :=
  sourceFieldCollapse.source

end CDotFCCT.SharedWitnessFusion
