import CDotFCCT.CTML.TransparentRecursivePackages

/-!
# A native record exporting mutually recursive witnesses

The equations `A = Unit → B` and `B = Unit → A` share one scope. A native `Z`
produces the function stored in the record. Packing hides both names; the client
opens their equations, follows both arrows and returns Unit. This checks the
recursive target interface, not a general source-object compilation theorem.
-/

set_option autoImplicit false

namespace CDotFCCT.CarrierRecursiveExamples

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTML.Transparent

def unit : Term := .record "Unit" .nil
def unitType {depth : Nat} : WFTy depth := WFTy.cls "Unit"
def alpha : WFTy 2 := WFTy.var 0 (by decide)
def beta : WFTy 2 := WFTy.var 1 (by decide)

def system : RecursiveSystem 0 2 where
  parameter _ := unitType
  result index := if index = 0 then beta else alpha

def inside : SubtypingContext := system.openContext SubtypingContext.empty

theorem consistent : ¬ InvertingSubtype inside WFTy.top WFTy.bottom := System.noCollapse system

def functional : Term := .abs (.abs (.abs (.var 2)))
def maker : Term := .fix functional
def fields (start : Term) : TermFields ["start"] := .cons "start" start .nil (by simp)
def record (start : Term) : Term := .record "Mutual" (fields start)
def payload : WFTy 2 := WFTy.record "start" alpha

theorem makerTyping : CTML.Transparent.HasType inside TypingContext.empty maker alpha :=
  .subsumption
    (.fixpoint (.abstraction (.abstraction
      (.subsumption
        (.abstraction (.subsumption (.native (.var _ _ _ (.there (.there .here))))
          (.native (system.fold SubtypingContext.empty 0))))
        (.native (system.fold SubtypingContext.empty 1))))))
    (.native (system.fold SubtypingContext.empty 0))

theorem recordTyping : CTML.Transparent.HasType inside TypingContext.empty (record maker) payload :=
  .subsumption (.record (.cons makerTyping .nil)) (.native .interRight)

def interface : CTML.Interface 0 := CTML.RecursivePackage.interface system payload
def packed : Term := CTML.packCBV (record maker)

theorem packedTyping : CTML.Transparent.HasType SubtypingContext.empty TypingContext.empty
    packed (interface.package unitType) :=
  RecursivePackage.packTyping (s := SubtypingContext.empty) (context := TypingContext.empty)
    (term := record maker) system unitType recordTyping

def client : Term := .app (.abs unit) (.app (.app (.proj (.var 0) "start") unit) unit)

def clientContext : SubtypingContext := ⟨2, system.equations.reverse⟩

theorem clientUnfold (index : Fin 2) :
    CTMLCore.Subtype clientContext (system.name index) (system.body index) :=
  @CTMLCore.Subtype.hyp clientContext (system.unfoldGuard index)
    (List.mem_reverse.mpr
      (List.mem_append_left _ (List.mem_ofFn.mpr ⟨index, rfl⟩)))

theorem clientTyping : InterfaceOpened interface [] TypingContext.empty client unitType :=
  .application (.abstraction (.native (.record .nil)))
    (.application
      (.subsumption
        (.application
          (.subsumption (.projection (.native (.var _ _ _ .here)))
            (.native (clientUnfold 0)))
          (.native (.record .nil)))
        (.native (clientUnfold 1)))
      (.native (.record .nil)))

def program : Term := .app packed (.abs client)

theorem programTyping :
    CTML.Transparent.HasType SubtypingContext.empty TypingContext.empty program unitType :=
  interfaceUnpackTyping packedTyping clientTyping

theorem programSafe {reached : Term} (steps : Steps program reached) :
    Value reached ∨ ∃ next, Step reached next := programTyping.safe steps

theorem recordValue : Value (record (unfoldFix functional)) :=
  .record _ _ (.cons (.abs _) .nil)

theorem unitValue : Value unit := .record _ _ .nil

theorem programSteps : Steps program unit := by
  refine .trans (.appHead (.abs client)
    (.appArg (.abs _) (.recordField (.head (.fixUnfold (.abs _)))))) ?_
  refine .trans (.appHead (.abs client) (CTML.packCBVStep recordValue)) ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  refine .trans (.appBeta _ _ recordValue) ?_
  refine .trans (.appArg (.abs _) (.appHead unit (.appHead unit (.proj recordValue .here)))) ?_
  change Steps (.app (.abs unit) (.app (.app (unfoldFix functional) unit) unit)) unit
  refine .trans (.appArg (.abs _)
    (.appHead unit (.unfoldFix_beta (function := functional) unitValue))) ?_
  refine .trans (.appArg (.abs _) (.appHead unit (.appHead unit (.appBeta _ _ (.abs _))))) ?_
  refine .trans (.appArg (.abs _) (.appHead unit (.appBeta _ _ unitValue))) ?_
  refine .trans (.appArg (.abs _) (.appBeta _ _ unitValue)) ?_
  exact .trans (.appBeta _ _ (.abs _)) .refl

def publicSupport : List (Option Bool) := [none, some false, some true]

def publicWitnesses : Option Bool → WFTy 2
  | none => payload
  | some false => alpha
  | some true => beta

def publicInterface : CTML.Interface 0 :=
  CarrierLayout.interface publicSupport none WFTy.top

/-- The same constructor can keep all recursive equations private behind a carrier view. -/
theorem publicPackedTyping : CTML.Transparent.HasType SubtypingContext.empty TypingContext.empty
    packed (publicInterface.package WFTy.top) :=
  RecursivePackage.packCarrierTyping (s := SubtypingContext.empty) (context := TypingContext.empty)
    (term := record maker) system publicSupport none List.mem_cons_self publicWitnesses
    WFTy.top WFTy.top (.native .leTop) recordTyping

theorem publicClientTyping :
    InterfaceOpened publicInterface [] TypingContext.empty (.var 0) WFTy.top :=
  .subsumption (.native (.var _ _ _ .here)) (.native .leTop)

def publicProgram : Term := .app packed (.abs (.var 0))

theorem publicProgramTyping : CTML.Transparent.HasType SubtypingContext.empty TypingContext.empty
    publicProgram WFTy.top := interfaceUnpackTyping publicPackedTyping publicClientTyping

/-- Erasing the public view does not replace or discard the constructed native record. -/
theorem publicProgramSteps : Steps publicProgram (record (unfoldFix functional)) := by
  refine .trans (.appHead (.abs (.var 0))
    (.appArg (.abs _) (.recordField (.head (.fixUnfold (.abs _)))))) ?_
  refine .trans (.appHead (.abs (.var 0)) (CTML.packCBVStep recordValue)) ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  exact .trans (.appBeta _ _ recordValue) .refl

end CDotFCCT.CarrierRecursiveExamples
