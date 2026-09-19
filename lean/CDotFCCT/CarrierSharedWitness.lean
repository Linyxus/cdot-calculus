import CDotFCCT.SharedWitnessRegression
import CDotFCCT.CTML.CarrierLayout

/-!
# Recovering the shared-witness regression through labelled carriers

The only two guards below describe the two bindings in the original source
context: `q` has its declared intersection type and `p` has type `q.X`.
Member bounds are derived from those guards, not separately assumed.

This checks the carrier representation on the existing difficult source example.
It is not yet a compiler for arbitrary source contexts or typing derivations.
-/

set_option autoImplicit false

namespace CDotFCCT.CarrierSharedWitness

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTML.Transparent

def support : List String := ["A", "X"]
def labels : List FieldName := CarrierLayout.names support

def memberA : MemberSlot labels :=
  CarrierLayout.slot support "A" (by decide)

def memberX : MemberSlot labels :=
  CarrierLayout.slot support "X" (by decide)

def selectedX : WFTy 2 := WFTy.var 1 (by decide)
def selectedA : WFTy 2 := WFTy.var 0 (by decide)
def unused : FieldName → WFTy 2 := fun _ => WFTy.top

def topView : WFTy 2 := memberA.view WFTy.top WFTy.top unused
def bottomView : WFTy 2 := memberA.view WFTy.bottom WFTy.bottom unused

def qWitness (label : String) : WFTy 2 := if label = "X" then selectedX else WFTy.top
def pWitness (label : String) : WFTy 2 := if label = "A" then selectedA else WFTy.top
def preciseQ : WFTy 2 := CarrierLayout.precise support qWitness
def preciseP : WFTy 2 := CarrierLayout.precise support pWitness

def ownerType : WFTy 2 := WFTy.intersection
  (memberX.view WFTy.bottom topView unused)
  (memberX.view WFTy.bottom bottomView unused)

def qBinding : WFConstraint 2 := WFConstraint.constr preciseQ ownerType
def pBinding : WFConstraint 2 := WFConstraint.constr preciseP selectedX
def context : SubtypingContext :=
  (SubtypingContext.empty.bindType.bindType.assume qBinding).assume pBinding

theorem qTyping : InvertingSubtype context preciseQ ownerType :=
  .native (@CTMLCore.Subtype.hyp context qBinding
    (List.mem_cons_of_mem pBinding List.mem_cons_self))

theorem pTyping : InvertingSubtype context preciseP selectedX :=
  .native (@CTMLCore.Subtype.hyp context pBinding List.mem_cons_self)

theorem qAsSlot : InvertingSubtype context
    (memberX.precise selectedX (CarrierLayout.components support support qWitness)) ownerType :=
  CarrierLayout.precise_eq_slot (support := support) (label := "X") (by decide) qWitness ▸ qTyping

theorem pAsSlot : InvertingSubtype context
    (memberA.precise selectedA (CarrierLayout.components support support pWitness)) selectedX :=
  CarrierLayout.precise_eq_slot (support := support) (label := "A") (by decide) pWitness ▸ pTyping

/-- Both views are obtained through the same abstract `q.X`. -/
theorem upperTopView : InvertingSubtype context selectedX topView :=
  memberX.upperBound (.native .refl) (qAsSlot.trans (.native .interLeft))

theorem upperBottomView : InvertingSubtype context selectedX bottomView :=
  memberX.upperBound (.native .refl) (qAsSlot.trans (.native .interRight))

theorem selectedLower : InvertingSubtype context WFTy.top selectedA :=
  memberA.lowerBound pAsSlot upperTopView

theorem selectedUpper : InvertingSubtype context selectedA WFTy.bottom :=
  memberA.upperBound pAsSlot upperBottomView

/-- The conclusion of the existing checked `Core.Subtyping` regression is retained. -/
theorem collapse : InvertingSubtype context WFTy.top WFTy.bottom :=
  selectedLower.trans selectedUpper

theorem noValidEnvironment (env : Indexed.Environment) (n : Nat) :
    ¬ Validates context env n := fun valid => CTML.Transparent.noCollapse valid collapse

def client : Term := .abs (.var 0)
def clientType : WFTy 0 := WFTy.all (WFTy.all
  (WFTy.constrained qBinding (WFTy.constrained pBinding (WFTy.arrow WFTy.top WFTy.bottom))))

/-- A closed FCCT-style constraint abstraction proves the recovered implication. -/
theorem clientTyping : CTML.Transparent.HasType SubtypingContext.empty TypingContext.empty
    client clientType :=
  .forall _ _ _ (.value (.abs _))
    (.forall _ _ _ (.value (.abs _))
      (.constrained (s := SubtypingContext.empty.bindType.bindType)
        qBinding _ _ _ (.value (.abs _))
        (.constrained (s := SubtypingContext.empty.bindType.bindType.assume qBinding)
          pBinding _ _ _ (.value (.abs _))
          (.abstraction (.subsumption (.native (.var _ _ _ .here)) collapse)))))

theorem clientSafe {reached : Term} (steps : Steps client reached) :
    Value reached ∨ ∃ next, Step reached next := clientTyping.safe steps

end CDotFCCT.CarrierSharedWitness
