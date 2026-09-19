import CDotFCCT.TypeOnlyCompilation
import CTMLCore.Declarative.IndexedFundamental

/-!
# Compiling a source object whose type members contain alias cycles

The source declares `A = A & (A → A)`, `B = C`, and `C = B`, as well as
the required tag member. `TypeOnlyCompilation.compile` generates the complete
target derivation from the source derivation. The public package exports the
original equations, and a closed client opens it and forces the native object.
-/

set_option autoImplicit false

namespace CDotFCCT.RecursiveAliasExamples

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation
open CTML.RecursiveAliases RecursiveAliasTranslation

local instance : CDot.Signature where
  TypLabel := Nat
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

def selected (self label : Nat) : CDot.Typ := .path (.select (.bound self) []) label
def sourceA : CDot.Typ := .and (selected 0 1) (.all (selected 0 1) (selected 1 1))
def sourceB : CDot.Typ := selected 0 3
def sourceC : CDot.Typ := selected 0 2

def sourceBody : CDot.Typ :=
  .and (.and (.and (.rcd (.typ (0 : Nat) .top .top))
    (.rcd (.typ (1 : Nat) sourceA sourceA))) (.rcd (.typ (2 : Nat) sourceB sourceB)))
    (.rcd (.typ (3 : Nat) sourceC sourceC))

def sourceDefinitions : CDot.Defs :=
  .cons (.cons (.cons (.cons .nil (.typ (0 : Nat) .top)) (.typ (1 : Nat) sourceA))
    (.typ (2 : Nat) sourceB)) (.typ (3 : Nat) sourceC)

def sourceObject : CDot.Val :=
  .new (.select (.bound 0) []) (0 : Nat) sourceBody sourceDefinitions

def sourceDerivation : Core.Typing [] (.val sourceObject) (.bnd sourceBody) :=
  .newIntro ∅
    (fun _ _ => .cons (.cons (.cons (.one .typ) .typ
      (by simp +decide [CDot.Defs.Hasnt, CDot.Defs.get, CDot.Defs.openRec, CDot.Def.openRec,
        CDot.Def.label])) .typ
      (by simp +decide [CDot.Defs.Hasnt, CDot.Defs.get, CDot.Defs.openRec, CDot.Def.openRec,
        CDot.Def.label])) .typ
      (by simp +decide [CDot.Defs.Hasnt, CDot.Defs.get, CDot.Defs.openRec, CDot.Def.openRec,
        CDot.Def.label]))
    (fun _ _ => .sub (.sub (.var .here) .top)
      (.selLo (.sub (.var .here) (.trans .andLeft (.trans .andLeft .andLeft)))))

theorem sourceTyping : CDot.Typed [] (.val sourceObject) (.bnd sourceBody) :=
  sourceDerivation.source

def env : TermCPS.Env := ⟨id, id, id⟩
def answer {depth : Nat} : WFTy depth := WFTy.cls "DOT"

/-- Evaluation of the compiler, with no supplied target witnesses or typing premises. -/
def compiled : TypeOnlyCompilation.Result answer env sourceDerivation :=
  (TypeOnlyCompilation.compile answer env sourceDerivation).get (by decide)

def first : WFTy 4 := names (depth := 0) (1 : Fin 4)
def firstConsumer : WFTy 4 := WFTy.arrow (WFTy.arrow first first) answer

theorem translatedA : compiled.members.equations (1 : Fin 4) =
    .intersection (.reference (1 : Fin 4)) (.arrow firstConsumer) := rfl

theorem translatedB : compiled.members.equations (2 : Fin 4) = .reference (3 : Fin 4) := rfl
theorem translatedC : compiled.members.equations (3 : Fin 4) = .reference (2 : Fin 4) := rfl

/-- Argument-dependent results are not silently mistaken for references to the enclosing self. -/
theorem rejectsDependentResult :
    RecursiveAliasTranslation.type compiled.only.labels id (answer : WFTy 0) 0
      (.all (selected 0 1) (selected 0 1)) = none := rfl

/-- The computed closure keeps A's arrow and removes its bare self-alias edge. -/
theorem resolvedA : resolved compiled.members.equations (1 : Fin 4) =
    WFTy.union firstConsumer WFTy.bottom := rfl

/-- A mutually recursive group with no guarded leaves receives the empty consumer. -/
theorem resolvedPureCycle : resolved compiled.members.equations (2 : Fin 4) = WFTy.bottom ∧
    resolved compiled.members.equations (3 : Fin 4) = WFTy.bottom := ⟨rfl, rfl⟩

theorem memberAUnfold :
    Subtype (compiled.members.system.openContext SubtypingContext.empty) first
      (WFTy.intersection first (WFTy.arrow firstConsumer answer)) :=
  compiled.members.unfold (s := SubtypingContext.empty) (1 : Fin 4)

theorem memberAFold :
    Subtype (compiled.members.system.openContext SubtypingContext.empty)
      (WFTy.intersection first (WFTy.arrow firstConsumer answer)) first :=
  compiled.members.fold (s := SubtypingContext.empty) (1 : Fin 4)

def observer : Term := .abs (.app (.var 0) TermCPS.unit)
def program : Term := .app (TermCPS.compile env sourceDerivation) observer
def result : Term := .record "DOT" .nil

theorem observerTyping : HasType SubtypingContext.empty TypingContext.empty observer
    ((compiled.members.interface TypeOnlyCompilation.payload).consumer answer) := by
  refine CTML.Interface.consumerTyping (s := SubtypingContext.empty)
    (context := TypingContext.empty) _ ?_
  exact HasType.application (.var _ 0 _ .here) ((HasType.record .nil).subsumption .leTop)

/-- The exact general runtime pass is typed using the generated existential interface. -/
theorem programTyping :
    Recursive.HasType SubtypingContext.empty TypingContext.empty program answer :=
  .application compiled.typing (.native observerTyping)

theorem programSafe {reached : Term} (steps : Steps program reached) :
    Value reached ∨ ∃ next, Step reached next := programTyping.safe steps

theorem programSteps : Steps program result := by
  change Steps (.app (CTML.pack TypeOnlyCompilation.objectThunk) observer) result
  refine .trans (.appBeta _ _ (.abs _)) ?_
  refine .trans (.appArg (.abs _) (.fixUnfold (.abs _))) ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  change Steps (.app (unfoldFix (.abs (.abs result))) TermCPS.unit) result
  refine .trans (.unfoldFix_beta (.record _ _ .nil)) ?_
  refine .trans (.appHead _ (.appBeta _ _ (.abs _))) ?_
  exact .single (.appBeta _ _ (.record _ _ .nil))

end CDotFCCT.RecursiveAliasExamples
