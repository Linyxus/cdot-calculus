import CDotFCCT.Intersections

/-! Checked introduction, bound use, and execution of a continuation-encoded package. -/

set_option autoImplicit false

namespace CDotFCCT.Examples

open FCCT FCCT.Syntax FCCT.Evaluation

private def alpha : WFTy 1 := WFTy.var 0 Nat.zero_lt_one
private def guards : List (WFConstraint 1) := bounds WFTy.bool WFTy.bool

def booleanPackage : Term := pack (.boolean true)

theorem booleanPackageTyping :
    HasType SubtypingContext.empty TypingContext.empty booleanPackage
      (existsCPS guards alpha WFTy.bool) :=
  packTyping (witness := WFTy.bool) (.boolean _ true) (boundsSatisfies .refl .refl)

theorem abstractUpperBound :
    Subtype (assumeMany SubtypingContext.empty.bindType guards) alpha WFTy.bool :=
  assumedGuard (subtyping := SubtypingContext.empty.bindType)
    (guards := guards) (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The consumer uses the abstract witness's upper bound, rather than its hidden equality. -/
theorem unpackBooleanTyping :
    HasType SubtypingContext.empty TypingContext.empty
      (.app booleanPackage (.abs (.var 0))) WFTy.bool :=
  unpackTyping booleanPackageTyping ((HasType.var _ 0 _ .here).subsumption abstractUpperBound)

theorem unpackBooleanSteps :
    Steps (.app booleanPackage (.abs (.var 0))) (.boolean true) :=
  .trans (.appBeta _ _ (.abs _)) (.trans (.appBeta _ _ (.boolean true)) .refl)

/-- Arbitrary guard abstraction does not make an inconsistent package constructible by packing. -/
theorem noBadBoundsWitness :
    ¬ ∃ witness : WFTy 0,
      Subtype SubtypingContext.empty WFTy.bool witness ∧
      Subtype SubtypingContext.empty witness (WFTy.arrow WFTy.bool WFTy.bool) :=
  fun ⟨_, lower, upper⟩ => Subtype.bool_not_le_arrow (.trans lower upper)

private def polyIdentity : WFTy 0 := WFTy.all (WFTy.arrow alpha alpha)
private def boolFunction : WFTy 0 := WFTy.arrow WFTy.bool WFTy.bool
private def functionIdentity : WFTy 0 := WFTy.arrow boolFunction boolFunction

private theorem polyIdentityTyping :
    HasType SubtypingContext.empty TypingContext.empty (.abs (.var 0)) polyIdentity :=
  .forall _ _ _ (.value (.abs _)) (.abstraction (.var _ 0 _ .here))

/-- One polymorphic witness supports two distinct function interfaces. -/
theorem intersectionPackageTyping :
    HasType SubtypingContext.empty TypingContext.empty (pack (.abs (.var 0)))
      (intersectionCPS boolFunction functionIdentity WFTy.bool) :=
  intersectionIntro polyIdentityTyping
    (@Subtype.forallLeft SubtypingContext.empty (WFTy.arrow alpha alpha) WFTy.bool)
    (@Subtype.forallLeft SubtypingContext.empty (WFTy.arrow alpha alpha) boolFunction)

theorem intersectionLeftTyping :
    HasType SubtypingContext.empty TypingContext.empty (pack (.abs (.var 0)))
      (computation boolFunction WFTy.bool) :=
  intersectionPackageTyping.subsumption (intersectionLeft _ _ _)

theorem intersectionRightTyping :
    HasType SubtypingContext.empty TypingContext.empty (pack (.abs (.var 0)))
      (computation functionIdentity WFTy.bool) :=
  intersectionPackageTyping.subsumption (intersectionRight _ _ _)

theorem intersectionClientTyping :
    HasType SubtypingContext.empty TypingContext.empty
      (.app (pack (.abs (.var 0))) (.abs (.app (.var 0) (.boolean true)))) WFTy.bool :=
  .application intersectionLeftTyping
    (.abstraction (.application (.var _ 0 _ .here) (.boolean _ true)))

theorem intersectionClientSteps :
    Steps (.app (pack (.abs (.var 0))) (.abs (.app (.var 0) (.boolean true)))) (.boolean true) :=
  .trans (.appBeta _ _ (.abs _))
    (.trans (.appBeta _ _ (.abs _)) (.trans (.appBeta _ _ (.boolean true)) .refl))

end CDotFCCT.Examples
