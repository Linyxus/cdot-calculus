import CDotFCCT.CTML.MixedFieldSharing
import CDotFCCT.TermCPSLookup

/-!
# Reading one member through a recursive field package

The client opens its existential package once, reads `head`, follows `next`, reads
`head` again at the same hidden member type, and returns the first value. The
producer stores Unit, but no Unit bound on the hidden member is supplied to the
client. Both object fields and recursive self use the existing CPS runtime syntax.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.MixedFieldSharingExamples

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation Mixed

def unit : Term := .record "Unit" .nil

def forceUnit : Term := TermCPS.unit

def packed : Term := pack (MixedFieldSharing.object unit)

def readHead (object continuation : Term) : Term :=
  .app (.proj (.app object forceUnit) "head") continuation

def readNext (object continuation : Term) : Term :=
  .app (.proj (.app object forceUnit) "next") continuation

def clientBody : Term :=
  readHead (.var 0) (.abs
    (readNext (.var 1) (.abs (readHead (.var 0) (.abs (.var 2))))))

def client : Term := .abs clientBody

def program : Term := .app packed client

def member : WFTy 2 := NativeFieldSharing.memberName

def row : WFTy 2 := NativeFieldSharing.rowName

def opened : SubtypingContext :=
  ⟨2, [WFConstraint.constr (NativeFieldSharing.body member row WFTy.top) row,
    WFConstraint.constr row (NativeFieldSharing.body member row WFTy.top)]⟩

theorem rowUnfold : Subtype opened row (NativeFieldSharing.body member row WFTy.top) :=
  @Subtype.hyp opened _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem headView :
    Subtype opened row (WFTy.record "head" (Coercion.observation member WFTy.top)) :=
  .trans rowUnfold .interLeft

theorem nextView : Subtype opened row
    (WFTy.record "next" (Coercion.observation (NativeFieldSharing.objectType row) WFTy.top)) :=
  .trans rowUnfold .interRight

theorem packedTyping : Mixed.HasType carrierPolicy SubtypingContext.empty TypingContext.empty
    packed ((NativeFieldSharing.interface WFTy.top).package WFTy.top) :=
  MixedFieldSharing.packTyping (.native (.record .nil))

theorem readHeadTyping {ctx : TypingContext 2} {object continuation : Term}
    (producer : Mixed.HasType carrierPolicy opened ctx object (NativeFieldSharing.objectType row))
    (consumer : Mixed.HasType carrierPolicy opened ctx continuation (WFTy.arrow member WFTy.top)) :
    Mixed.HasType carrierPolicy opened ctx (readHead object continuation) WFTy.top :=
  .application (.projection ((Mixed.HasType.application producer
    (.native ((CTMLCore.HasType.record .nil).subsumption .leTop)))
      |>.subsumption (.native headView))) consumer

theorem readNextTyping {ctx : TypingContext 2} {object continuation : Term}
    (producer : Mixed.HasType carrierPolicy opened ctx object (NativeFieldSharing.objectType row))
    (consumer : Mixed.HasType carrierPolicy opened ctx continuation
      (WFTy.arrow (NativeFieldSharing.objectType row) WFTy.top)) :
    Mixed.HasType carrierPolicy opened ctx (readNext object continuation) WFTy.top :=
  .application (.projection ((Mixed.HasType.application producer
    (.native ((CTMLCore.HasType.record .nil).subsumption .leTop)))
      |>.subsumption (.native nextView))) consumer

/-- The two `head` continuations bind exactly the same existential member name. -/
theorem clientOpened :
    InterfaceOpened carrierPolicy (NativeFieldSharing.interface (WFTy.top : WFTy 0)) []
      TypingContext.empty clientBody WFTy.top := by
  change Mixed.HasType carrierPolicy opened
    (TypingContext.empty.bind (NativeFieldSharing.objectType row)) clientBody WFTy.top
  exact readHeadTyping (.native (.var _ 0 _ .here)) (.abstraction
    (readNextTyping (.native (.var _ 1 _ (.there .here))) (.abstraction
      (readHeadTyping (.native (.var _ 0 _ .here)) (.abstraction
        ((Mixed.HasType.native (.var _ 2 _ (.there (.there .here))))
          |>.subsumption (.native .leTop)))))))

theorem programTyping :
    Mixed.HasType carrierPolicy SubtypingContext.empty TypingContext.empty program WFTy.top :=
  interfaceUnpackTyping packedTyping clientOpened

theorem programSafe {reached : Term} (steps : Steps program reached) :
    Value reached ∨ ∃ next, Step reached next := programTyping.safe steps

def contents : TermFields ["head", "next"] :=
  .cons "head" (.abs (.app (.var 0) unit))
    (.cons "next" (.abs (.app (.var 0) (.var 2))) .nil (by decide)) (by decide)

def functional : Term := .abs (.abs (.record "DOT" contents))

def thunk : Term := unfoldFix functional

def self : Term := TermCPS.objectSelf contents

def closedRecord : Term := .record "DOT" (TermCPS.closeObjectFields contents)

theorem closedRecordValue : Value closedRecord :=
  .record _ _ (TermCPS.closeObjectFields_values (.cons (.abs _) (.cons (.abs _) .nil)))

theorem thunkForces : Steps (.app thunk forceUnit) closedRecord := by
  refine .trans (.appBeta _ _ (.record _ _ .nil)) ?_
  change Steps (.app (.app (functional.lift 1 |>.substAt 0 forceUnit) self) forceUnit) _
  rw [Term.lift_substAt_cancel]
  refine .trans (.appHead _ (.appBeta _ _ (.abs _))) ?_
  rw [Term.substAt_abs]
  exact .trans (.appBeta _ _ (.record _ _ .nil)) .refl

theorem thunkHeadSteps {continuation : Term} (hk : Value continuation) :
    Steps (readHead thunk continuation) (.app continuation unit) := by
  refine ((thunkForces.projHead "head").appHead continuation).trans' ?_
  refine .trans (.appHead _ (.proj closedRecordValue
    (TermCPS.closeObjectFields_lookup (TermFields.Lookup.here (tail := _))))) ?_
  exact .trans (.appBeta _ _ hk) .refl

theorem thunkNextSteps {continuation : Term} (hk : Value continuation) :
    Steps (readNext thunk continuation) (.app continuation self) := by
  refine ((thunkForces.projHead "next").appHead continuation).trans' ?_
  refine .trans (.appHead _ (.proj closedRecordValue
    (TermCPS.closeObjectFields_lookup (.there .here)))) ?_
  exact .trans (.appBeta _ _ hk) .refl

theorem selfHeadSteps {continuation : Term} (hk : Value continuation) :
    Steps (readHead self continuation) (.app continuation unit) :=
  TermCPS.self_force_field_call (.cons (.abs _) (.cons (.abs _) .nil)) .here hk

theorem programSteps : Steps program unit := by
  refine .trans (.appBeta _ _ (.abs _)) ?_
  refine .trans (.appArg (.abs _) (.fixUnfold (.abs _))) ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  change Steps (readHead thunk _) unit
  refine (thunkHeadSteps (.abs _)).trans' ?_
  refine .trans (.appBeta _ _ (.record _ _ .nil)) ?_
  change Steps (readNext thunk _) unit
  refine (thunkNextSteps (.abs _)).trans' ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  change Steps (readHead self _) unit
  refine (selfHeadSteps (.abs _)).trans' ?_
  exact .trans (.appBeta _ _ (.record _ _ .nil)) .refl

local instance : CDot.Signature where
  TypLabel := String
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

def sourceContext : CDot.Ctx := [(0, .top), (1, .rcd (.typ "Tag" .top .top))]

def sourceBody : CDot.Typ :=
  .and (.rcd (.trm "head" (.sngl (.var 0))))
    (.rcd (.trm "next" (.sngl (.select (.bound 0) []))))

def sourceDefinitions : CDot.Defs :=
  .cons (.cons .nil (.trm "head" (.path (.var 0))))
    (.trm "next" (.path (.select (.bound 0) [])))

def sourceValue : CDot.Val := .new (.var 1) "Tag" sourceBody sourceDefinitions

/-- Both fields are source path aliases; `next` refers to the actual new self binder. -/
def sourceDerivation : Core.Typing sourceContext (.val sourceValue) (.bnd sourceBody) :=
  .newIntro {0, 1}
    (fun self fresh => by
      have different : (0 : CDot.Var) ≠ self := by
        intro equal
        subst self
        simp at fresh
      exact .cons (.one (.path (.var (.there different .here)))) (.path (.var .here))
        (by
          simp [CDot.Defs.Hasnt, CDot.Defs.get, CDot.Defs.openRec,
            CDot.Def.openRec, CDot.Def.label]
          decide))
    (fun self fresh => by
      have different : (1 : CDot.Var) ≠ self := by
        intro equal
        subst self
        simp at fresh
      exact .sub (.sub (.var .here) .top)
        (.selLo (.var (.there different (.there (by decide) .here)))))

theorem sourceTyping : CDot.Typed sourceContext (.val sourceValue) (.bnd sourceBody) :=
  sourceDerivation.source

/-- Direct labels make the exact compiler output comparable to the existing schema. -/
def environment : TermCPS.Env where
  free := id
  bound := id
  fieldName := id

theorem sourceValueRuntime :
    TermCPS.value environment sourceValue = some (MixedFieldSharing.object (.var 0)) := rfl

theorem sourceComputationRuntime :
    TermCPS.compile environment sourceDerivation = pack (MixedFieldSharing.object (.var 0)) := rfl

def compiledProgram : Term :=
  .app (.app (.abs (TermCPS.compile environment sourceDerivation)) unit) client

/-- The specialized known-layout package types the actual compiler output. -/
theorem compiledTyping : Mixed.HasType carrierPolicy SubtypingContext.empty
    (TypingContext.empty.bind (WFTy.cls "Unit"))
    (TermCPS.compile environment sourceDerivation)
    ((NativeFieldSharing.interface WFTy.top).package WFTy.top) := by
  rw [sourceComputationRuntime]
  exact MixedFieldSharing.packTyping (.native (.var _ _ _ .here))

theorem compiledProgramTyping : Mixed.HasType carrierPolicy SubtypingContext.empty
    TypingContext.empty compiledProgram WFTy.top :=
  interfaceUnpackTyping
    (.application (.abstraction compiledTyping) (.native (.record .nil))) clientOpened

theorem compiledProgramSafe {reached : Term} (steps : Steps compiledProgram reached) :
    Value reached ∨ ∃ next, Step reached next := compiledProgramTyping.safe steps

theorem compiledProgramSteps : Steps compiledProgram unit := by
  refine .trans (.appHead client (.appBeta _ _ (.record _ _ .nil))) ?_
  exact programSteps

end CDotFCCT.CTML.MixedFieldSharingExamples
