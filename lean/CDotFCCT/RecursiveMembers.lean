import CDot.Definitions
import CDotFCCT.Existentials

/-!
# A recursive-member obligation for the translation

A closed DOT object may define `A = self.A → self.A`. Any translation that represents
type-member definitions by existential witnesses and equality constraints must explain
how such a witness is constructed. A term fixpoint does not itself prove a subtyping equation.
The guarded recursive type extension now supplies this example's witness; the package and
its abstract consumer are checked below.
-/

set_option autoImplicit false

namespace CDotFCCT.RecursiveMembers

open CDot

local instance : Signature where
  TypLabel := Nat
  TrmLabel := Nat
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

private def selfPath : Path := .select (.bound 0) []

/-- Member zero supplies the object's tag; member one is its recursive type. -/
def recursiveMember : Typ :=
  .all (.path selfPath (1 : Nat)) (.path (.select (.bound 1) []) (1 : Nat))

def objectBody : Typ :=
  .and (.rcd (.typ (0 : Nat) .top .top))
    (.rcd (.typ (1 : Nat) recursiveMember recursiveMember))

def objectDefs : Defs :=
  .cons (.cons .nil (.typ (0 : Nat) .top)) (.typ (1 : Nat) recursiveMember)

def objectValue : Val := .new selfPath (0 : Nat) objectBody objectDefs

theorem objectTyping : Typed [] (.val objectValue) (.bnd objectBody) := by
  refine .newIntro ∅ ?_ ?_
  · refine fun _ _ => .cons (.one .typ) .typ ?_
    simp [Defs.Hasnt, Defs.get, Defs.openRec, Def.openRec, Def.label]
  · exact fun _ _ => .sub (.sub (.var .here) .top) (.selLo (.sub (.var .here) .andLeft))

/-- The selected type of member one, after binding the object to `x`. -/
def member (x : Var) : Typ := .path (.var x) (1 : Nat)

theorem memberTyping (x : Var) :
    Typed [(x, .bnd objectBody)] (.path (.var x))
      (.rcd (.typ (1 : Nat) (.all (member x) (member x)) (.all (member x) (member x)))) :=
  .sub (.recElim (.var .here)) .andRight

/-- Both directions of the recursive equation are available in an ordinary DOT context. -/
theorem memberEquation (x : Var) :
    Subtyp [(x, .bnd objectBody)] (member x) (.all (member x) (member x)) ∧
    Subtyp [(x, .bnd objectBody)] (.all (member x) (member x)) (member x) :=
  ⟨.selHi (memberTyping x), .selLo (memberTyping x)⟩

/-- The equality guards of a direct, arrow-preserving encoding of member one. -/
def equalityGuards : List (FCCT.WFConstraint 1) :=
  let a := FCCT.WFTy.var 0 Nat.zero_lt_one
  [FCCT.WFConstraint.constr a (FCCT.WFTy.arrow a a),
   FCCT.WFConstraint.constr (FCCT.WFTy.arrow a a) a]

/-- Packing this direct encoding really does require both recursive subtyping equations.
This identifies an obligation; it is not a theorem ruling out every possible encoding of DOT. -/
theorem witnessObligation (witness : FCCT.WFTy 0) :
    Satisfies FCCT.SubtypingContext.empty
      (equalityGuards.map (·.instantiate witness)) ↔
    (FCCT.Subtype FCCT.SubtypingContext.empty witness (FCCT.WFTy.arrow witness witness) ∧
     FCCT.Subtype FCCT.SubtypingContext.empty (FCCT.WFTy.arrow witness witness) witness) := by
  change (∀ guard ∈
      [FCCT.WFConstraint.constr witness (FCCT.WFTy.arrow witness witness),
       FCCT.WFConstraint.constr (FCCT.WFTy.arrow witness witness) witness],
      FCCT.Subtype FCCT.SubtypingContext.empty guard.sub guard.sup) ↔ _
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rfl

private def alpha : FCCT.WFTy 1 := FCCT.WFTy.var 0 Nat.zero_lt_one

/-- A witness for the recursive equation required by this source object. -/
def recursiveWitness : FCCT.WFTy 0 := FCCT.WFTy.recArrow alpha alpha

theorem witnessUnfold :
    FCCT.Subtype FCCT.SubtypingContext.empty recursiveWitness
      (FCCT.WFTy.arrow recursiveWitness recursiveWitness) :=
  @FCCT.Subtype.recUnfold FCCT.SubtypingContext.empty alpha alpha

theorem witnessFold :
    FCCT.Subtype FCCT.SubtypingContext.empty
      (FCCT.WFTy.arrow recursiveWitness recursiveWitness) recursiveWitness :=
  @FCCT.Subtype.recFold FCCT.SubtypingContext.empty alpha alpha

theorem recursiveGuardsSatisfied :
    Satisfies FCCT.SubtypingContext.empty
      (equalityGuards.map (·.instantiate recursiveWitness)) :=
  (witnessObligation recursiveWitness).mpr ⟨witnessUnfold, witnessFold⟩

/-- Store an identity function at the hidden recursive type. This packages the recursive
member equation; it is not yet a translation of the entire source object. -/
def recursivePackage : FCCT.Syntax.Term := pack (.abs (.var 0))

theorem recursivePackageTyping :
    FCCT.HasType FCCT.SubtypingContext.empty FCCT.TypingContext.empty recursivePackage
      (existsCPS equalityGuards alpha FCCT.WFTy.bool) :=
  packTyping (subtyping := FCCT.SubtypingContext.empty)
    (context := FCCT.TypingContext.empty) (guards := equalityGuards) (payload := alpha)
    (answer := FCCT.WFTy.bool) (witness := recursiveWitness)
    ((FCCT.HasType.abstraction (.var _ 0 _ .here)).subsumption witnessFold)
    recursiveGuardsSatisfied

/-- The consumer applies its abstract payload to itself, using only the abstracted bound,
then returns a boolean without letting the hidden type escape. -/
def recursiveClient : FCCT.Syntax.Term :=
  .app recursivePackage (.abs (.app (.abs (.boolean true)) (.app (.var 0) (.var 0))))

theorem abstractFunctionBound :
    FCCT.Subtype (assumeMany FCCT.SubtypingContext.empty.bindType equalityGuards)
      alpha (FCCT.WFTy.arrow alpha alpha) :=
  assumedGuard (subtyping := FCCT.SubtypingContext.empty.bindType)
    (guards := equalityGuards) List.mem_cons_self

theorem recursiveClientTyping :
    FCCT.HasType FCCT.SubtypingContext.empty FCCT.TypingContext.empty recursiveClient
      FCCT.WFTy.bool := by
  refine unpackTyping recursivePackageTyping ?_
  exact .application (.abstraction (.boolean _ true))
    (.application ((FCCT.HasType.var _ 0 _ .here).subsumption abstractFunctionBound)
      (.var _ 0 _ .here))

theorem recursiveClientSteps :
    FCCT.Evaluation.Steps recursiveClient (.boolean true) :=
  .trans (.appBeta _ _ (.abs _))
    (.trans (.appBeta _ _ (.abs _))
      (.trans (.appArg (.abs _) (.appBeta _ _ (.abs _)))
        (.trans (.appBeta _ _ (.abs _)) .refl)))

end CDotFCCT.RecursiveMembers
