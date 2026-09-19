import CDotFCCT.PackageSubtyping

/-!
# Continuation-encoded common-subtype packages

An intersection package hides one witness below both component types. Its projections are
FCCT subtyping derivations. Introduction requires a *common* witness with both bounds;
two unrelated typing derivations alone do not supply this witness. The DOT path translation
must maintain this invariant when handling `Typed.andIntro`.
-/

set_option autoImplicit false

namespace CDotFCCT

open FCCT FCCT.Syntax

def computation {n : Nat} (type answer : WFTy n) : WFTy n :=
  WFTy.arrow (WFTy.arrow type answer) answer

def intersectionGuards {n : Nat} (left right : WFTy n) : List (WFConstraint (n + 1)) :=
  let witness := WFTy.var 0 (Nat.zero_lt_succ n)
  [WFConstraint.constr witness left.weaken, WFConstraint.constr witness right.weaken]

def intersectionCPS {n : Nat} (left right answer : WFTy n) : WFTy n :=
  existsCPS (intersectionGuards left right) (WFTy.var 0 (Nat.zero_lt_succ n)) answer

/-- A continuation for a supertype accepts any witness satisfying the package's guards. -/
theorem callbackSubtype {subtyping : SubtypingContext}
    {guards : List (WFConstraint (subtyping.typeDepth + 1))}
    {payload : WFTy (subtyping.typeDepth + 1)} {type answer : WFTy subtyping.typeDepth}
    (bound : Subtype (assumeMany subtyping.bindType guards) payload type.weaken) :
    Subtype subtyping (WFTy.arrow type answer) (consumer guards payload answer) := by
  refine .trans (@Subtype.forallRight subtyping (WFTy.arrow type answer))
    (.forallCovariant _ _ (qualifyRight guards ?_))
  change Subtype (assumeMany subtyping.bindType guards)
    (WFTy.arrow type.weaken answer.weaken) (WFTy.arrow payload answer.weaken)
  exact .arrow bound .refl

theorem packageProjection {subtyping : SubtypingContext}
    {guards : List (WFConstraint (subtyping.typeDepth + 1))}
    {payload : WFTy (subtyping.typeDepth + 1)} {type answer : WFTy subtyping.typeDepth}
    (bound : Subtype (assumeMany subtyping.bindType guards) payload type.weaken) :
    Subtype subtyping (existsCPS guards payload answer) (computation type answer) :=
  .arrow (callbackSubtype bound) .refl

theorem intersectionLeft {subtyping : SubtypingContext}
    (left right answer : WFTy subtyping.typeDepth) :
    Subtype subtyping (intersectionCPS left right answer) (computation left answer) :=
  packageProjection (assumedGuard (subtyping := subtyping.bindType)
    (guards := intersectionGuards left right) List.mem_cons_self)

theorem intersectionRight {subtyping : SubtypingContext}
    (left right answer : WFTy subtyping.typeDepth) :
    Subtype subtyping (intersectionCPS left right answer) (computation right answer) :=
  packageProjection (assumedGuard (subtyping := subtyping.bindType)
    (guards := intersectionGuards left right) (List.mem_cons_of_mem _ List.mem_cons_self))

theorem intersectionSatisfies {subtyping : SubtypingContext}
    {left right witness : WFTy subtyping.typeDepth}
    (hLeft : Subtype subtyping witness left) (hRight : Subtype subtyping witness right) :
    Satisfies subtyping ((intersectionGuards left right).map (·.instantiate witness)) := by
  change Satisfies subtyping
    [WFConstraint.constr witness (left.weaken.instantiate witness),
     WFConstraint.constr witness (right.weaken.instantiate witness)]
  simpa only [Satisfies, WFTy.weaken_instantiate_cancel, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, WFConstraint.sub, WFConstraint.sup,
    WFConstraint.constr] using And.intro hLeft hRight

theorem intersectionIntro {subtyping : SubtypingContext}
    {context : TypingContext subtyping.typeDepth}
    {left right answer witness : WFTy subtyping.typeDepth} {value : Term}
    (hValue : HasType subtyping context value witness)
    (hLeft : Subtype subtyping witness left) (hRight : Subtype subtyping witness right) :
    HasType subtyping context (pack value) (intersectionCPS left right answer) :=
  packTyping (witness := witness) hValue (intersectionSatisfies hLeft hRight)

end CDotFCCT
