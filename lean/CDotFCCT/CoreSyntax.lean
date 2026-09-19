import CDotFCCT.CoreDerivation
import Mathlib.Data.Finset.Lattice.Fold

/-! # Syntax coverage of the core-DOT derivations -/

set_option autoImplicit false

namespace CDotFCCT.Core

open CDot

variable [Signature]

mutual
  /-- No runtime tag test occurs, including inside any lambda or nested object. -/
  def testFree : Trm → Bool
    | .val value => valueTestFree value
    | .path _ | .app _ _ => true
    | .letE rhs body => testFree rhs && testFree body
    | .caseE .. => false

  def valueTestFree : Val → Bool
    | .lambda _ body => testFree body
    | .new _ _ _ definitions => definitionsTestFree definitions

  def definitionTestFree : Def → Bool
    | .typ .. => true
    | .trm _ rhs => rhsTestFree rhs

  def definitionsTestFree : Defs → Bool
    | .nil => true
    | .cons rest field => definitionsTestFree rest && definitionTestFree field

  def rhsTestFree : DefRhs → Bool
    | .path _ => true
    | .val value => valueTestFree value
end

mutual
  theorem testFree_openRec (term : Trm) (index : Nat) (x : Var) :
      testFree (term.openRec index x) = testFree term :=
    match term with
    | .val value => valueTestFree_openRec value index x
    | .path _ | .app _ _ | .caseE .. => rfl
    | .letE rhs body => congrArg₂ Bool.and
        (testFree_openRec rhs index x) (testFree_openRec body (index + 1) x)

  theorem valueTestFree_openRec (value : Val) (index : Nat) (x : Var) :
      valueTestFree (value.openRec index x) = valueTestFree value :=
    match value with
    | .lambda _ body => testFree_openRec body (index + 1) x
    | .new _ _ _ definitions => definitionsTestFree_openRec definitions (index + 1) x

  theorem definitionTestFree_openRec (field : Def) (index : Nat) (x : Var) :
      definitionTestFree (field.openRec index x) = definitionTestFree field :=
    match field with
    | .typ .. => rfl
    | .trm _ rhs => rhsTestFree_openRec rhs index x

  theorem definitionsTestFree_openRec (definitions : Defs) (index : Nat) (x : Var) :
      definitionsTestFree (definitions.openRec index x) = definitionsTestFree definitions :=
    match definitions with
    | .nil => rfl
    | .cons rest field => congrArg₂ Bool.and
        (definitionsTestFree_openRec rest index x) (definitionTestFree_openRec field index x)

  theorem rhsTestFree_openRec (rhs : DefRhs) (index : Nat) (x : Var) :
      rhsTestFree (rhs.openRec index x) = rhsTestFree rhs :=
    match rhs with
    | .path _ => rfl
    | .val value => valueTestFree_openRec value index x
end

mutual
  theorem testFree_openRecPath (term : Trm) (index : Nat) (p : Path) :
      testFree (term.openRecPath index p) = testFree term :=
    match term with
    | .val value => valueTestFree_openRecPath value index p
    | .path _ | .app _ _ | .caseE .. => rfl
    | .letE rhs body => congrArg₂ Bool.and
        (testFree_openRecPath rhs index p) (testFree_openRecPath body (index + 1) p)

  theorem valueTestFree_openRecPath (value : Val) (index : Nat) (p : Path) :
      valueTestFree (value.openRecPath index p) = valueTestFree value :=
    match value with
    | .lambda _ body => testFree_openRecPath body (index + 1) p
    | .new _ _ _ definitions => definitionsTestFree_openRecPath definitions (index + 1) p

  theorem definitionTestFree_openRecPath (field : Def) (index : Nat) (p : Path) :
      definitionTestFree (field.openRecPath index p) = definitionTestFree field :=
    match field with
    | .typ .. => rfl
    | .trm _ rhs => rhsTestFree_openRecPath rhs index p

  theorem definitionsTestFree_openRecPath (definitions : Defs) (index : Nat) (p : Path) :
      definitionsTestFree (definitions.openRecPath index p) = definitionsTestFree definitions :=
    match definitions with
    | .nil => rfl
    | .cons rest field => congrArg₂ Bool.and
        (definitionsTestFree_openRecPath rest index p)
        (definitionTestFree_openRecPath field index p)

  theorem rhsTestFree_openRecPath (rhs : DefRhs) (index : Nat) (p : Path) :
      rhsTestFree (rhs.openRecPath index p) = rhsTestFree rhs :=
    match rhs with
    | .path _ => rfl
    | .val value => valueTestFree_openRecPath value index p
end

def fresh (excluded : Vars) : Var := excluded.sup id + 1

omit [Signature] in
theorem fresh_not_mem (excluded : Vars) : fresh excluded ∉ excluded :=
  fun membership => Nat.not_succ_le_self _ (Finset.le_sup (f := id) membership)

mutual
  /-- A full core derivation rules out every unsupported runtime tag test in its syntax. -/
  theorem Typing.testFree {G : Ctx} {term : Trm} {type : Typ}
      (h : Typing G term type) : testFree term = true :=
    match h with
    | .var _ | .allElim _ _ | .newElim _ | .rcdIntro _ | .sngl _ _ | .self _ |
        .pathElim _ _ | .recIntro _ | .recElim _ | .andIntro _ _ => rfl
    | .allIntro L body => by
        simpa only [Trm.open, testFree_openRec, testFree, valueTestFree] using
          (body (fresh L) (fresh_not_mem L)).testFree
    | .newIntro L fields _ => by
        simpa only [Defs.open, definitionsTestFree_openRec, testFree, valueTestFree] using
          (fields (fresh L) (fresh_not_mem L)).testFree
    | .letE L rhs body => by
        simpa only [Trm.open, testFree_openRec, testFree, Bool.and_self] using
          congrArg₂ Bool.and rhs.testFree (body (fresh L) (fresh_not_mem L)).testFree
    | .sub term _ => term.testFree

  theorem DefinitionTyping.testFree {x : Var} {fields : Fields} {G : Ctx}
      {field : Def} {type : Dec} (h : DefinitionTyping x fields G field type) :
      definitionTestFree field = true :=
    match h with
    | .typ | .path _ => rfl
    | .all function => function.testFree
    | .new _ _ _ fields _ => by
        simpa only [Defs.openPath, definitionsTestFree_openRecPath, definitionTestFree,
          rhsTestFree, valueTestFree] using fields.testFree

  theorem DefinitionsTyping.testFree {x : Var} {fields : Fields} {G : Ctx}
      {definitions : Defs} {type : Typ} (h : DefinitionsTyping x fields G definitions type) :
      definitionsTestFree definitions = true :=
    match h with
    | .one field => field.testFree
    | .cons rest field _ => congrArg₂ Bool.and rest.testFree field.testFree
end

end CDotFCCT.Core
