import CDotFCCT.OpenTyping
import CDotFCCT.StaticCompilation

/-!
# A compiled client of a record with a shared abstract member

The client calls `p.id p.value`. Its source derivation uses both bounds of `p.A`,
record introduction and intersection introduction. `Typing.translate` generates
the target body proof; `Typing.consumerAt` abstracts the witness and its bounds.
Packing a concrete record then discharges those assumptions in the empty context.
-/

set_option autoImplicit false

namespace CDotFCCT.RecordCompilation

open CTMLCore OpenCore

local instance : CDot.Signature where
  TypLabel := Nat
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

def aliasType : Typ := .arrow .top .top

def member (x : CDot.Var) : Member := ⟨⟨x, []⟩, (1 : Nat)⟩

def bound (x : CDot.Var) : Bound := ⟨member x, aliasType, aliasType⟩

def interface (x : CDot.Var) : Typ :=
  .inter
    (.inter
      (.inter (.member (0 : Nat) .top .top) (.member (1 : Nat) aliasType aliasType))
      (.field "value" aliasType))
    (.field "id" (.arrow (.selection (member x)) (.selection (member x))))

def root (x : CDot.Var) : Path := ⟨x, []⟩

def valueDerivation (x : CDot.Var) :
    PathTyping [bound x] [(x, interface x)] ((root x).field "value") aliasType :=
  .field (.subsumption (.var .here) (.trans .interLeft .interRight))

def methodDerivation (x : CDot.Var) :
    PathTyping [bound x] [(x, interface x)] ((root x).field "id")
      (.arrow (.selection (member x)) (.selection (member x))) :=
  .field (.subsumption (.var .here) .interRight)

def refinedDerivation (x : CDot.Var) :
    PathTyping [bound x] [(x, interface x)] (root x)
      (.inter (.field "value" (.selection (member x)))
        (.field "id" (.arrow (.selection (member x)) (.selection (member x))))) :=
  .inter
    (.record (.subsumption (valueDerivation x) (.lower (bound x) List.mem_cons_self)))
    (.record (methodDerivation x))

def client (x : CDot.Var) : Term :=
  .app ((root x).field "id") ((root x).field "value")

def clientDerivation (x : CDot.Var) :
    Typing [bound x] [(x, interface x)] (client x) aliasType :=
  .subsumption
    (.app (.field (.subsumption (refinedDerivation x) .interRight))
      (.field (.subsumption (refinedDerivation x) .interLeft)))
    (.upper (bound x) List.mem_cons_self)

theorem sourceBounds {context : CDot.Ctx} (x : CDot.Var)
    (self : CDot.Typed context (.var x) (interface x).source) :
    SourceBounds context [bound x] := by
  intro b membership
  rcases List.mem_singleton.mp membership with rfl
  exact .sub self (.trans .andLeft (.trans .andLeft .andRight))

def selectedBound (index : Nat) : CDot.Typ :=
  .path (.select (.bound index) []) (1 : Nat)

def sourceObjectBody : CDot.Typ :=
  .and
    (.and
      (.and (.rcd (.typ (0 : Nat) .top .top))
        (.rcd (.typ (1 : Nat) aliasType.source aliasType.source)))
      (.rcd (.trm "value" aliasType.source)))
    (.rcd (.trm "id" (.all (selectedBound 0) (selectedBound 1))))

def sourceObjectDefs : CDot.Defs :=
  .cons
    (.cons
      (.cons (.cons .nil (.typ (0 : Nat) .top)) (.typ (1 : Nat) aliasType.source))
      (.trm "value" (.val (.lambda .top (.path (.select (.bound 0) []))))))
    (.trm "id" (.val (.lambda (selectedBound 0) (.path (.select (.bound 0) [])))))

def sourceObject : CDot.Val :=
  .new (.select (.bound 0) []) (0 : Nat) sourceObjectBody sourceObjectDefs

theorem sourceObjectBody_open (x : CDot.Var) :
    sourceObjectBody.open x = (interface x).source := rfl

private theorem sourceIdentity (context : CDot.Ctx) (type : Typ) :
    CDot.Typed context
      (.val (.lambda type.source (.path (.select (.bound 0) []))))
      (.all type.source type.source) := by
  refine .allIntro ∅ (fun x _ => ?_)
  change CDot.Typed (context.push x type.source) (.var x) (type.source.openRec 0 x)
  exact (Typ.source_openRec type 0 x).symm ▸ CDot.Typed.var CDot.Env.Binds.here

theorem sourceObjectTyping : CDot.Typed [] (.val sourceObject) (.bnd sourceObjectBody) := by
  refine .newIntro ∅ ?_ ?_
  · refine fun x _ =>
      .cons (.cons (.cons (.one .typ) .typ ?_) (.all (sourceIdentity _ .top)) ?_)
        (.all (sourceIdentity _ (.selection (member x)))) ?_
    all_goals simp [CDot.Defs.Hasnt, CDot.Defs.get, CDot.Defs.openRec,
      CDot.Def.openRec, CDot.Def.label]
    decide
  · exact fun _ _ => .sub (.sub (.var .here) .top)
      (.selLo (.sub (.var .here) (.trans .andLeft (.trans .andLeft .andLeft))))

def sourceProgram : CDot.Trm :=
  .letE (.val sourceObject)
    (.app (.select (.bound 0) ["id"]) (.select (.bound 0) ["value"]))

theorem sourceProgramTyping : CDot.Typed [] sourceProgram aliasType.source := by
  refine .letE ∅ sourceObjectTyping (fun x _ => ?_)
  refine (clientDerivation x).sourceIn ?_ (sourceBounds x (.recElim (.var .here)))
  exact fun lookup => match lookup with
    | .here => .recElim (.var .here)
    | .there _ rest => nomatch rest

def witnesses : Witnesses 1 where
  get := fun key => if key = member 0 then WFTy.var 0 (by decide) else WFTy.top
  fieldName := id
  answer := WFTy.top

def witness : WFTy 0 := WFTy.arrow WFTy.top WFTy.top

def guards : List (WFConstraint 1) := (bound 0).guards witnesses

def payload : WFTy 1 := (interface 0).translate witnesses

def targetIdentity : CTMLCore.Syntax.Term := .abs (.var 0)

def targetRecord : CTMLCore.Syntax.Term :=
  .record "DOT"
    (.cons "value" targetIdentity (.cons "id" targetIdentity .nil (by simp)) (by decide))

def targetConsumer : CTMLCore.Syntax.Term :=
  .abs ((client 0).translate witnesses [(0, interface 0)])

def targetProgram : CTMLCore.Syntax.Term := .app (CTML.pack targetRecord) targetConsumer

def compilationEnv : StaticCompilation.Env where
  free := fun _ => none
  bound := fun _ => none
  fieldName := id

/-- The typed target is exactly the executable syntax pass's output. -/
theorem compilation :
    StaticCompilation.program compilationEnv sourceProgram = some targetProgram := rfl

theorem targetConsumerTyping :
    HasType SubtypingContext.empty TypingContext.empty targetConsumer
      (CTML.consumer guards payload witness) :=
  (clientDerivation 0).consumerAt witnesses witness rfl

theorem targetRecordTyping :
    HasType SubtypingContext.empty TypingContext.empty targetRecord
      (payload.instantiate witness) := by
  refine (HasType.record
    (.cons (.abstraction (param := WFTy.top) (.var _ 0 _ .here))
      (.cons (.abstraction (param := witness) (.var _ 0 _ .here)) .nil))).subsumption ?_
  exact .interMono (.interMono (.leInter .leTop .leTop) .refl) .refl

theorem guardsSatisfied :
    CTML.Satisfies SubtypingContext.empty (guards.map (·.instantiate witness)) :=
  @CTML.boundsSatisfies SubtypingContext.empty witness witness witness .refl .refl

theorem targetProgramTyping :
    HasType SubtypingContext.empty TypingContext.empty targetProgram witness :=
  .application (CTML.packTyping targetRecordTyping guardsSatisfied) targetConsumerTyping

theorem targetRecordValue : CTMLCore.Evaluation.Value targetRecord :=
  .record _ _ (.cons (.abs _) (.cons (.abs _) .nil))

/-- The translation computes the identity function stored in `value`. -/
theorem targetProgramSteps : CTMLCore.Evaluation.Steps targetProgram targetIdentity := by
  refine .trans (.appBeta _ _ (.abs _)) ?_
  refine .trans (.appBeta _ _ targetRecordValue) ?_
  change CTMLCore.Evaluation.Steps
    (.app (.proj targetRecord "id") (.proj targetRecord "value")) targetIdentity
  refine .trans (.appHead _ (.proj targetRecordValue (.there .here))) ?_
  refine .trans (.appArg (.abs _) (.proj targetRecordValue .here)) ?_
  exact .trans (.appBeta _ _ (.abs _)) .refl

end CDotFCCT.RecordCompilation
