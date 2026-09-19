import CDotFCCT.CTML.TransparentSafety
import CTMLCore.Declarative.RecursiveInversionObstruction

/-! # Regression checks for the experimental record-inversion calculus -/

set_option autoImplicit false

namespace CDotFCCT.CTML.Transparent.Examples

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

def alpha : WFTy 1 := WFTy.var 0 (by decide)

/-- Native recursive records remain available when their fields suspend the cycle. -/
def node : Definition 0 := .record "next" (.arrow WFTy.top alpha)

/-- Guardedness does not impose positivity on recursive occurrences. -/
def negativeNode : Definition 0 := .record "consume" (.arrow alpha WFTy.top)

theorem rejectsOldCounterexample :
    ¬ RecursiveInversionCounterexample.definition.body.raw.ArrowGuardedAt 0 :=
  fun guarded => guarded.1.2 rfl

theorem nodeConsistent :
    ¬ InvertingSubtype (node.native.openContext SubtypingContext.empty) WFTy.top WFTy.bottom :=
  node.noCollapse

def first : WFTy 2 := WFTy.var 1 (by decide)
def second : WFTy 2 := WFTy.var 0 (by decide)
def fieldBound : WFConstraint 2 :=
  WFConstraint.constr (WFTy.record "member" first) (WFTy.record "member" second)
def castType : WFTy 0 :=
  WFTy.all (WFTy.all (WFTy.constrained fieldBound (WFTy.arrow first second)))
def identity : Term := .abs (.var 0)

/-- The guarded identity uses record inversion under both type and constraint binders. -/
theorem castTyping : HasType SubtypingContext.empty TypingContext.empty identity castType :=
  .forall _ _ _ (.value (.abs _))
    (.forall _ _ _ (.value (.abs _))
      (.constrained (s := SubtypingContext.empty.bindType.bindType)
        fieldBound _ _ _ (.value (.abs _))
        (.abstraction (.subsumption (.native (.var _ _ _ .here))
          (.inverse (.native (@CTMLCore.Subtype.hyp
            (SubtypingContext.empty.bindType.bindType.assume fieldBound)
            fieldBound List.mem_cons_self)))))))

def unit : Term := .record "Unit" .nil

def unitCast : WFTy 1 := WFTy.constrained
  (WFConstraint.constr (WFTy.record "member" (WFTy.cls "Unit"))
    (WFTy.record "member" alpha)) (WFTy.arrow (WFTy.cls "Unit") alpha)

theorem castUnitTyping : HasType SubtypingContext.empty TypingContext.empty identity
    (WFTy.arrow (WFTy.cls "Unit") WFTy.top) :=
  .subsumption
    (.subsumption
      (.subsumption castTyping (.native (.forallLeft (context := SubtypingContext.empty)
        (body := WFTy.all (WFTy.constrained fieldBound (WFTy.arrow first second)))
        (argument := WFTy.cls "Unit"))))
      (.native (.forallLeft (context := SubtypingContext.empty)
        (body := unitCast) (argument := WFTy.top))))
    (.native (.constrainedLeft (context := SubtypingContext.empty)
      (WFConstraint.constr (WFTy.record "member" (WFTy.cls "Unit"))
        (WFTy.record "member" WFTy.top))
      (WFTy.arrow (WFTy.cls "Unit") WFTy.top) (.record .leTop)))

theorem castProgramTyping :
    HasType SubtypingContext.empty TypingContext.empty (.app identity unit) WFTy.top :=
  .application castUnitTyping (.native (.record .nil))

theorem castProgramSteps : Steps (.app identity unit) unit :=
  .trans (.appBeta _ _ (.record _ _ .nil)) .refl

def nodeFields (next : Term) : TermFields ["next"] := .cons "next" next .nil (by simp)
def nodeRecord (next : Term) : Term := .record "Node" (nodeFields next)
def functional : Term := .abs (.abs (nodeRecord (.var 1)))
def maker : Term := .fix functional
def program : Term := .app maker unit
def produced : Term := nodeRecord (delayedFix functional)

def inside : SubtypingContext := node.native.openContext SubtypingContext.empty

/-- One unfolding constructs a native record; its recursive field is already a function value. -/
theorem makerTyping : HasType inside TypingContext.empty maker (WFTy.arrow WFTy.top alpha) :=
  .fixpoint (.abstraction (.abstraction
    (.subsumption
      (.record (.cons (.native (.var _ _ _ (.there .here))) .nil))
      (.native (CTMLCore.Subtype.trans .interRight
        (node.native.fold SubtypingContext.empty))))))

theorem programTyping :
    HasType SubtypingContext.empty TypingContext.empty program WFTy.top :=
  .recursive node (.subsumption
    (.application makerTyping (.native ((CTMLCore.HasType.record .nil).subsumption .leTop)))
    (.native .leTop))

theorem programSafe {reached : Term} (steps : Steps program reached) :
    Value reached ∨ ∃ next, Step reached next := programTyping.safe steps

theorem producedValue : Value produced := .record _ _ (.cons (.abs _) .nil)

theorem programSteps : Steps program produced := by
  refine .trans (.appHead unit (.fixUnfold (.abs _))) ?_
  refine .trans (.unfoldFix_beta (.record _ _ .nil)) ?_
  refine .trans (.appHead unit (.appBeta _ _ (.abs _))) ?_
  exact .trans (.appBeta _ _ (.record _ _ .nil)) .refl

end CDotFCCT.CTML.Transparent.Examples
