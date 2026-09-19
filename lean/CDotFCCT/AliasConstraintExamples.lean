import CDotFCCT.AliasConstraints

/-!
# Running the generated alias coercion with discharged guards

The input is a real source subtyping derivation using singleton replacement at
`p.child.A`. The pass generates both witness equations and a constrained coercion.
The closed target client instantiates both witnesses with `Unit`, proves the two
resulting guards by reflexivity, and puts the unchanged value in a native record.
-/

set_option autoImplicit false

namespace CDotFCCT.AliasConstraintExamples

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation MemberUses

local instance : CDot.Signature where
  TypLabel := String
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

def sourceContext : CDot.Ctx := [(1, .sngl (.var 0)), (0, .top)]
def leftPath : CDot.Path := (CDot.Path.var 1).selectFields ["child"]
def rightPath : CDot.Path := (CDot.Path.var 0).selectFields ["child"]

def sourceDerivation : Core.Subtyping sourceContext
    (.path leftPath "A") (.path rightPath "A") :=
  .snglPQ (.var .here) (.var (.there (by decide) .here)) .path

def events : List Event := subtyping sourceDerivation [] []
def answer {depth : Nat} : WFTy depth := WFTy.record "kept" (WFTy.cls "Unit")
def first : WFTy 2 := WFTy.var 0 (by decide)
def second : WFTy 2 := WFTy.var 1 (by decide)

def compiled : AliasConstraints.Compiled events [] answer :=
  (AliasConstraints.compile events [] answer).get ⟨0, by decide⟩

theorem generatedGuards : AliasConstraints.guards events [] =
    [WFConstraint.constr first second, WFConstraint.constr second first] := rfl

theorem sourceChecked : CDot.Subtyp sourceContext (.path leftPath "A")
    (.path rightPath "A") := compiled.entry.source.1

theorem generatedEndpoints : compiled.entry.left = first ∧ compiled.entry.right = second :=
  ⟨rfl, rfl⟩

def schema : WFTy 0 := WFTy.all (WFTy.all
  (CTML.qualify (AliasConstraints.guards events [])
    (CTML.Coercion.type compiled.entry.left compiled.entry.right answer)))

theorem schemaTyping :
    HasType SubtypingContext.empty TypingContext.empty CTML.Coercion.identity schema :=
  .forall _ _ _ (.value (.abs _)) (.forall _ _ _ (.value (.abs _)) compiled.typing)

def witness {depth : Nat} : WFTy depth := WFTy.cls "Unit"

/-- Both generated equations are discharged, rather than retained as hypotheses. -/
theorem schemaInstance : Subtype SubtypingContext.empty schema
    (CTML.Coercion.type witness witness answer) := by
  refine .trans (Subtype.forallLeft (argument := witness)) ?_
  change Subtype SubtypingContext.empty
    (WFTy.all (CTML.qualify
      [WFConstraint.constr (WFTy.var 0 (by decide)) witness,
        WFConstraint.constr witness (WFTy.var 0 (by decide))]
      (CTML.Coercion.type (WFTy.var 0 (by decide)) witness answer))) _
  refine .trans (Subtype.forallLeft (argument := witness)) ?_
  change Subtype SubtypingContext.empty
    (CTML.qualify [WFConstraint.constr witness witness, WFConstraint.constr witness witness]
      (CTML.Coercion.type witness witness answer)) _
  exact .trans (Subtype.constrainedLeft (WFConstraint.constr witness witness) _ .refl)
    (Subtype.constrainedLeft (WFConstraint.constr witness witness) _ .refl)

theorem specializedTyping : HasType SubtypingContext.empty TypingContext.empty
    CTML.Coercion.identity (CTML.Coercion.type witness witness answer) :=
  schemaTyping.subsumption schemaInstance

def value : Term := .record "Unit" .nil
def observer : Term := .abs (.record "Box" (.cons "kept" (.var 0) .nil (by decide)))
def program : Term := .app (.app CTML.Coercion.identity value) observer
def result : Term := .record "Box" (.cons "kept" value .nil (by decide))

theorem observerTyping : HasType SubtypingContext.empty TypingContext.empty observer
    (WFTy.arrow witness answer) :=
  .abstraction ((HasType.record (.cons (.var _ 0 _ .here) .nil)).subsumption .interRight)

theorem programTyping : HasType SubtypingContext.empty TypingContext.empty program answer :=
  .application (.application specializedTyping (.record .nil)) observerTyping

theorem programSteps : Steps program result :=
  (CTML.Coercion.identitySteps (.record _ _ .nil) (.abs _)).trans'
    (.single (.appBeta _ _ (.record _ _ .nil)))

def scopedDerivation : Core.Subtyping [(0, .top)]
    (.all (.sngl (.var 0)) (.path (.select (.bound 0) ["child"]) "A"))
    (.all (.sngl (.var 0)) (.path rightPath "A")) :=
  .all {0} .refl (fun _ fresh => .snglPQ (.var .here)
    (.var (.there (fun equal => fresh (Finset.mem_singleton.mpr equal.symm)) .here))
    (CDot.ReplTyp.path (fields := ["child"])))

def scopedEvents : List Event := subtyping scopedDerivation [] []

theorem noEscapingGuards : AliasConstraints.guards scopedEvents [] = [] := rfl

theorem localGuards : AliasConstraints.guards scopedEvents [(1, [])] =
    [WFConstraint.constr first second, WFConstraint.constr second first] := rfl

def baseLeft : CDot.Path := (CDot.Path.var 1).selectField "base"
def baseRight : CDot.Path := (CDot.Path.var 0).selectField "base"
def baseContext : CDot.Ctx :=
  [(1, .rcd (.trm "base" (.sngl baseRight))), (0, .rcd (.trm "base" .top))]

def baseReplacement : Core.Subtyping baseContext
    (.path (baseLeft.selectField "child") "A") (.path (baseRight.selectField "child") "A") :=
  .snglPQ (.newElim (.var .here)) (.newElim (.var (.there (by decide) .here)))
    (CDot.ReplTyp.path (fields := ["child"]))

def withOtherFields : CDot.Typ :=
  .and (.path (baseLeft.selectField "child") "A")
    (.and (.path ((CDot.Path.var 1).selectField "other") "A")
      (.path ((CDot.Path.var 0).selectField "other") "A"))

def baseDerivation : Core.Subtyping baseContext withOtherFields
    (.and (.path (baseRight.selectField "child") "A") withOtherFields) :=
  .andIntro (.trans .andLeft baseReplacement) .refl

def baseEvents : List Event := subtyping baseDerivation [] []

/-- Equal owners and suffix lengths do not suffice: the base field path must match. -/
theorem exactPrefix : (AliasConstraints.generate baseEvents []).map
    (fun entry => (entry.equality.leftMember entry.fields entry.label,
      entry.equality.rightMember entry.fields entry.label)) =
    [(⟨⟨.external 1, ["child", "base"]⟩, "A"⟩,
      ⟨⟨.external 0, ["child", "base"]⟩, "A"⟩)] := rfl

end CDotFCCT.AliasConstraintExamples
