import CDotFCCT.MemberScopeSafety
import CDotFCCT.SharedWitnessFusion
import CDotFCCT.RecursiveAliasExamples

/-!
# Sharing and scope checks for the full-source member analysis

These examples run the analysis on real core derivations. They check the opaque
bound and nested-field regressions, distinguish unrelated cofinite binders, and
keep hypothetical singleton equalities out of the outer scope. They do not assert
that the corresponding target constraints have been generated or discharged.
-/

set_option autoImplicit false

namespace CDotFCCT.MemberUseExamples

open MemberUses

section StringLabels

local instance : CDot.Signature where
  TypLabel := String
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

def opaqueUses : List Event := subtyping SharedWitnessRegression.sourceCollapse [] []

def selectedKey : MemberKey := ⟨⟨.external 1, []⟩, "A"⟩
def ownerKey : MemberKey := ⟨⟨.external 0, []⟩, "X"⟩

/-- Two different bounds on `q.X` expose two uses of the very same `p.A`. -/
theorem opaqueOccurrences : opaqueUses.filterMap Event.memberKey =
    [selectedKey, ownerKey, selectedKey, ownerKey] := rfl

/-- The actual finite allocation uses two witnesses, rather than four. -/
theorem opaqueKeys : keys opaqueUses = [selectedKey, ownerKey] := rfl

theorem selectedWitness : witness opaqueUses selectedKey (by decide) =
    CTMLCore.WFTy.var 0 (by decide) := rfl

def opaqueVariable : Core.Typing SharedWitnessRegression.sourceContext (.var 1)
    (.path (.var 0) "X") := .var .here

/-- A bare variable rule still requests the witnesses in its type. -/
theorem variableTypeKeys : keys (typing opaqueVariable [] []) = [ownerKey] := rfl

def reflexiveSelection : Core.Subtyping SharedWitnessRegression.sourceContext
    (.path (.var 1) "A") (.path (.var 1) "A") := .refl

theorem reflexiveKeys : keys (subtyping reflexiveSelection [] []) = [selectedKey] := rfl

def fieldUses : List Event := subtyping SharedWitnessFusion.sourceFieldCollapse [] []

/-- The field path is part of the key; neither record view allocates it afresh. -/
theorem fieldKeys : keys fieldUses = [⟨⟨.external 0, ["child"]⟩, "A"⟩] := rfl

def paramType : CDot.Typ := .rcd (.typ "A" .top .top)
def selectedParam : CDot.Typ := .path (.select (.bound 0) []) "A"

def dependentResultIn (context : CDot.Ctx) : Core.Subtyping context (.all paramType .top)
    (.all paramType selectedParam) :=
  .all ∅ .refl (fun _ _ => .selLo (.var .here))

def dependentResult := dependentResultIn []

def separateArguments : Core.Subtyping [] (.all paramType .top)
    (.and (.all paramType selectedParam) (.all paramType selectedParam)) :=
  .andIntro dependentResult dependentResult

def separateUses : List Event := subtyping separateArguments [] []

def binderNames (events : List Event) : List CDot.Var :=
  events.filterMap (fun event => match event with
    | .binder entry => some entry.variableName
    | _ => none)

theorem sameRepresentative : binderNames separateUses = [1, 1] := rfl

/-- Equal numeric representatives at different binders do not conflate witnesses. -/
theorem separateKeys : keys separateUses =
    [⟨⟨.bound [0], []⟩, "A"⟩, ⟨⟨.bound [1], []⟩, "A"⟩] := rfl

/-- The bound uses in the dependent results cannot become outer assumptions. -/
theorem noOuterBounds : keys (localEvents separateUses []) = [] := rfl

theorem noOuterWitnesses : visibleKeys separateUses [] = [] := rfl

theorem firstArgumentWitnesses : visibleKeys separateUses [(1, [0])] =
    [⟨⟨.bound [0], []⟩, "A"⟩] := rfl

theorem secondArgumentWitnesses : visibleKeys separateUses [(1, [1])] =
    [⟨⟨.bound [1], []⟩, "A"⟩] := rfl

def nestedWithOuter : Core.Subtyping SharedWitnessRegression.sourceContext (.all paramType .top)
    (.and .bot (.all paramType selectedParam)) :=
  .andIntro (.trans .top SharedWitnessRegression.sourceCollapse)
    (dependentResultIn SharedWitnessRegression.sourceContext)

def nestedUses : List Event := subtyping nestedWithOuter [] []

theorem nestedRepresentative : binderNames nestedUses = [2] := rfl

theorem outerWitnesses : visibleKeys nestedUses [] = [selectedKey, ownerKey] := rfl

theorem innerWitnesses : visibleKeys nestedUses [(2, [1])] =
    [⟨⟨.bound [1], []⟩, "A"⟩, selectedKey, ownerKey] := rfl

theorem outerWitnessShift : scopedWitness nestedUses [(2, [1])] selectedKey (by decide) =
    (scopedWitness nestedUses [] selectedKey (by decide)).weaken := rfl

def singletonParam : CDot.Typ := .sngl (.var 0)
def singletonFunction : CDot.Trm :=
  .val (.lambda singletonParam (.path (.select (.bound 0) [])))

def singletonDerivation : Core.Typing [(0, .top)] singletonFunction
    (.all singletonParam .top) :=
  .allIntro {0} (fun _ fresh =>
    .sngl (.var .here)
      (.var (.there (fun equal => fresh (Finset.mem_singleton.mpr equal.symm)) .here)))

def singletonUses : List Event := typing singletonDerivation [] []

def aliases (events : List Event) : List (PathKey × PathKey) :=
  events.filterMap (fun event => match event with
    | .alias equality => some (equality.leftKey, equality.rightKey)
    | _ => none)

theorem innerAlias : aliases singletonUses = [(⟨.bound [], []⟩, ⟨.external 0, []⟩)] := rfl

theorem noOuterAlias : aliases (localEvents singletonUses []) = [] := rfl

end StringLabels

section NatLabels

local instance : CDot.Signature where
  TypLabel := Nat
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

def objectUses : List Event := typing RecursiveAliasExamples.sourceDerivation [] []

/-- Declarations and the self-tag check use the same object's member table. -/
theorem objectKeys : keys objectUses =
    [⟨⟨.bound [], []⟩, (1 : Nat)⟩, ⟨⟨.bound [], []⟩, (3 : Nat)⟩,
      ⟨⟨.bound [], []⟩, (2 : Nat)⟩, ⟨⟨.bound [], []⟩, (0 : Nat)⟩] := rfl

end NatLabels

end CDotFCCT.MemberUseExamples
