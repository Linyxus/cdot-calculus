import CDotFCCT.RecordCompilation
import CTMLCore.Declarative.RecursiveTypes

/-!
# Compiling a recursive type member to native CTML

The source object defines `A = self.A → self.A` and stores an identity function
at `self.A → self.A`. A client applies that function to itself, using the lower
bound to coerce its argument, and returns an ordinary identity function.

The target uses a scoped equirecursive declaration, a native record, and a CPS
existential. Only the existential is continuation-encoded. The target derivation
is in `CTMLCore.Recursive.HasType`; Core's existing soundness theorem is not a
soundness proof for that new recursive binding rule.
-/

set_option autoImplicit false

namespace CDotFCCT.RecursiveCompilation

open CTMLCore

local instance : CDot.Signature where
  TypLabel := Nat
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

def sourceMember (index : Nat) : CDot.Typ :=
  .path (.select (.bound index) []) (1 : Nat)

def sourceAlias : CDot.Typ := .all (sourceMember 0) (sourceMember 1)

def sourceObjectBody : CDot.Typ :=
  .and
    (.and (.rcd (.typ (0 : Nat) .top .top))
      (.rcd (.typ (1 : Nat) sourceAlias sourceAlias)))
    (.rcd (.trm "value" sourceAlias))

def sourceObject : CDot.Val :=
  .new (.select (.bound 0) []) (0 : Nat) sourceObjectBody
    (.cons
      (.cons (.cons .nil (.typ (0 : Nat) .top)) (.typ (1 : Nat) sourceAlias))
      (.trm "value" (.val (.lambda (sourceMember 0) (.path (.select (.bound 0) []))))))

theorem sourceObjectTyping : CDot.Typed [] (.val sourceObject) (.bnd sourceObjectBody) := by
  exact .newIntro ∅
    (fun _ _ => .cons (.cons (.one .typ) .typ
      (by simp [CDot.Defs.Hasnt, CDot.Defs.get, CDot.Defs.openRec, CDot.Def.openRec,
        CDot.Def.label]))
      (.all (.allIntro ∅ (fun _ _ => .var .here)))
      (by simp [CDot.Defs.Hasnt, CDot.Defs.get, CDot.Defs.openRec, CDot.Def.openRec,
        CDot.Def.label]))
    (fun _ _ => .sub (.sub (.var .here) .top)
      (.selLo (.sub (.var .here) (.trans .andLeft .andLeft))))

def sourceIdentity : CDot.Val := .lambda .top (.path (.select (.bound 0) []))

def sourceBody : CDot.Trm :=
  .letE (.path (.select (.bound 0) ["value"]))
    (.letE (.app (.select (.bound 0) []) (.select (.bound 0) [])) (.val sourceIdentity))

def sourceProgram : CDot.Trm := .letE (.val sourceObject) sourceBody

theorem sourceProgramTyping : CDot.Typed [] sourceProgram (.all .top .top) := by
  refine .letE ∅ sourceObjectTyping (fun p _ => ?_)
  refine .letE (CDot.Env.dom ([(p, .bnd sourceObjectBody)] : CDot.Ctx))
    (.newElim (.sub (.recElim (.var .here)) .andRight)) (fun f hf => ?_)
  have self : CDot.Typed
      (CDot.Env.push [(p, .bnd sourceObjectBody)] f (sourceAlias.open p))
      (.var p) (sourceObjectBody.open p) :=
    (CDot.Typed.recElim (CDot.Typed.var CDot.Env.Binds.here)).mono
      (CDot.Env.Extends.pushRight hf (sourceAlias.open p))
  exact .letE ∅
    (.allElim (.var .here)
      (.sub (.var .here) (.selLo (.sub self (.trans .andLeft .andRight)))))
    (fun _ _ => .allIntro ∅ (fun _ _ => .var .here))

def alpha {n : Nat} : WFTy (n + 1) := WFTy.var 0 (Nat.zero_lt_succ n)

def definition : RecursiveType 0 := .arrow alpha alpha

def recursiveContext : SubtypingContext := definition.openContext SubtypingContext.empty

def guards {n : Nat} : List (WFConstraint (n + 1)) :=
  [WFConstraint.constr alpha (WFTy.arrow alpha alpha),
   WFConstraint.constr (WFTy.arrow alpha alpha) alpha]

def payload {n : Nat} : WFTy (n + 1) := WFTy.record "value" (WFTy.arrow alpha alpha)

def answer {n : Nat} : WFTy n := WFTy.arrow WFTy.top WFTy.top

def identity : CTMLCore.Syntax.Term := .abs (.var 0)

def targetRecord : CTMLCore.Syntax.Term :=
  .record "DOT" (.cons "value" identity .nil (by simp))

def targetBody : CTMLCore.Syntax.Term :=
  .app (.abs (.app (.abs identity) (.app (.var 0) (.var 0)))) (.proj (.var 0) "value")

def targetProgram : CTMLCore.Syntax.Term :=
  .app (CTML.pack targetRecord) (.abs targetBody)

theorem compilation :
    StaticCompilation.program RecordCompilation.compilationEnv sourceProgram =
      some targetProgram := rfl

theorem witnessGuards :
    CTML.Satisfies recursiveContext (guards.map (·.instantiate (alpha : WFTy 1))) := by
  change (∀ guard ∈
    [WFConstraint.constr (alpha : WFTy 1) (WFTy.arrow alpha alpha),
     WFConstraint.constr (WFTy.arrow alpha alpha) alpha],
    Subtype recursiveContext guard.sub guard.sup)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨definition.unfold SubtypingContext.empty, definition.fold SubtypingContext.empty⟩

theorem targetRecordTyping :
    HasType recursiveContext TypingContext.empty targetRecord
      (payload.instantiate (alpha : WFTy 1)) :=
  (HasType.record (.cons (.abstraction (.var _ 0 _ .here)) .nil)).subsumption .interRight

private theorem targetBodyTyping (s : SubtypingContext) :
    HasType (CTML.assumeMany s.bindType guards) (TypingContext.empty.bind payload)
      targetBody answer.weaken := by
  refine .application (.abstraction ?_) (.projection (.var _ 0 _ .here))
  refine .application (.abstraction ?_)
    (.application (.var _ 0 _ .here)
      ((HasType.var _ 0 _ .here).subsumption
        (@CTML.assumedGuard s.bindType guards (WFConstraint.constr (WFTy.arrow alpha alpha) alpha)
          (List.mem_cons_of_mem _ List.mem_cons_self))))
  change HasType _ _ (.abs (.var 0)) (WFTy.arrow WFTy.top WFTy.top)
  exact .abstraction (.var _ 0 _ .here)

theorem targetProgramTyping :
    Recursive.HasType SubtypingContext.empty TypingContext.empty targetProgram answer := by
  refine .recursive definition (.native ?_)
  exact .application (CTML.packTyping targetRecordTyping witnessGuards)
    (CTML.consumerTyping (targetBodyTyping recursiveContext))

theorem targetProgramSteps : CTMLCore.Evaluation.Steps targetProgram identity := by
  refine .trans (.appBeta _ _ (.abs _)) ?_
  refine .trans (.appBeta _ _ (.record _ _ (.cons (.abs _) .nil))) ?_
  refine .trans (.appArg (.abs _) (.proj (.record _ _ (.cons (.abs _) .nil)) .here)) ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  refine .trans (.appArg (.abs _) (.appBeta _ _ (.abs _))) ?_
  exact .trans (.appBeta _ _ (.abs _)) .refl

end CDotFCCT.RecursiveCompilation
