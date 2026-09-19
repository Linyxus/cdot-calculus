import CDotFCCT.CTML.PackageWitnesses
import CDotFCCT.CTML.RecursiveRecords
import CDotFCCT.CTML.RecursivePackages
import CDotFCCT.TermCPS
import CTMLCore.Declarative.IndexedFundamental

/-!
# One member witness across a recursive record's fields

The producer chooses its payload type once. A single outer existential binds that
member type and the record's recursive row. The `head` field returns the member;
the `next` field returns another object thunk with the very same row and member.
Both fields are suspended CPS computations, as in `TermCPS.value`.

Only native CTML subtyping is used. Recursive equations come from a record-guarded
`RecursiveType`; no record component inversion or negative witness equation is assumed.
This is a known-layout constructor lemma, not the general opaque-field invariant.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.NativeFieldSharing

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

def objectType {n : Nat} (row : WFTy n) : WFTy n := WFTy.arrow WFTy.top row

def body {n : Nat} (member row answer : WFTy n) : WFTy n :=
  WFTy.intersection (WFTy.record "head" (Coercion.observation member answer))
    (WFTy.record "next" (Coercion.observation (objectType row) answer))

/-- The recursive carrier is a native record intersection. -/
def definition {n : Nat} (member answer : WFTy n) : RecursiveType n :=
  RecursiveType.intersection
    (.record "head" (Coercion.observation member.weaken answer.weaken))
    (.record "next" (Coercion.observation
      (objectType (WFTy.var 0 (by omega))) answer.weaken))

def rowName {n : Nat} : WFTy (n + 2) := WFTy.var 0 (by omega)

def memberName {n : Nat} : WFTy (n + 2) := WFTy.var 1 (by omega)

/-- Both recursive fields are inside the same member and row telescope. -/
def interface {n : Nat} (answer : WFTy n) : Interface n :=
  .bind (.bind
    (.guard (WFConstraint.constr rowName (body memberName rowName answer.weaken.weaken))
      (.guard (WFConstraint.constr (body memberName rowName answer.weaken.weaken) rowName)
        (.payload (objectType rowName)))))

/-- The exact object thunk and suspended field shape used by the runtime CPS pass. -/
def object (payload : Term) : Term :=
  .fix (.abs (.abs (.record "DOT"
    (.cons "head" (.abs (.app (.var 0) (payload.lift 3)))
      (.cons "next" (.abs (.app (.var 0) (.var 2))) .nil (by decide)) (by decide)))))

/-- A known recursive row instantiates the telescope at one shared member. -/
def interfaceInstance {s : SubtypingContext} (member row answer : WFTy s.typeDepth)
    (unfold : Subtype s row (body member row answer))
    (fold : Subtype s (body member row answer) row) :
    Interface.Instance s (interface answer) (objectType row) := by
  refine .bind member ?_
  simp only [Interface.instantiate, Interface.substAt]
  refine .bind row ?_
  simp only [Interface.instantiate, Interface.substAt]
  change Interface.Instance s
    (.guard (WFConstraint.constr row
      (body (member.weaken.instantiate row) row
        (((answer.weaken.weaken).substAt 1 (by omega) member.weaken).instantiate row)))
      (.guard (WFConstraint.constr
        (body (member.weaken.instantiate row) row
          (((answer.weaken.weaken).substAt 1 (by omega) member.weaken).instantiate row)) row)
        (.payload (objectType row)))) (objectType row)
  rw [WFTy.substAt_weaken (Nat.zero_le s.typeDepth)]
  simp only [WFTy.weaken_instantiate_cancel]
  change Interface.Instance s
    (.guard (WFConstraint.constr row (body member row (answer.weaken.instantiate member)))
      (.guard (WFConstraint.constr (body member row (answer.weaken.instantiate member)) row)
        (.payload (objectType row)))) (objectType row)
  rw [WFTy.weaken_instantiate_cancel]
  exact .guard unfold (.guard fold (.payload _))

theorem interface_weaken {n : Nat} (answer : WFTy n) :
    (interface answer).weaken = interface answer.weaken := by
  change Interface.bind (.bind
    (.guard (WFConstraint.constr rowName
      (body memberName rowName (answer.weaken.weaken.liftAt 2 (by omega))))
      (.guard (WFConstraint.constr
        (body memberName rowName (answer.weaken.weaken.liftAt 2 (by omega))) rowName)
        (.payload (objectType rowName))))) = _
  rw [WFTy.liftAt_weaken (show 1 ≤ n + 1 by omega),
    WFTy.liftAt_weaken (Nat.zero_le n)]
  rfl

theorem objectTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {payload : Term} {member answer : WFTy s.typeDepth}
    (typing : Recursive.HasType s context payload member) :
    Recursive.HasType ((definition member answer).openContext s) context.bindType
      ((object payload).liftTy 1) (objectType (definition member answer).name) := by
  refine .fixpoint (.abstraction (.abstraction (.subsumption (.record
    (fieldTypes := [("head", Coercion.observation member.weaken answer.weaken),
      ("next", Coercion.observation (objectType (definition member answer).name) answer.weaken)])
    (.cons (.abstraction (.application (.native (.var _ 0 _ .here)) ?_))
      (.cons (.abstraction (.application (.native (.var _ 0 _ .here))
        (.native (.var _ 2 _ (.there (.there .here)))))) .nil))) ?_)))
  · have lifted := ((typing.weakenType.weakenAssumption
      (WFConstraint.constr (definition member answer).name
        (definition member answer).body)).weakenAssumption
        (WFConstraint.constr (definition member answer).body (definition member answer).name))
    have selfLifted := lifted.weakenFront (objectType (definition member answer).name)
    have allLifted := (selfLifted.weakenFront WFTy.top).weakenFront
      (WFTy.arrow member.weaken answer.weaken)
    change Recursive.HasType ((definition member answer).openContext s) _
      ((payload.lift 3).liftTy 1) member.weaken
    rw [← Term.liftTy_liftAt_comm payload 0 3 1]
    have shift : (((payload.liftTy 1).lift 1).lift 1).lift 1 =
        (payload.liftTy 1).lift 3 := by
      simp only [Term.lift, Term.liftAt, Term.renameWith_renameWith, Nat.zero_le, ite_true]
    rw [shift] at allLifted
    exact allLifted
  · exact (Subtype.leInter (.trans .interLeft .interRight) .interRight).trans
      ((definition member answer).fold s)

/-- The constructor chooses both hidden witnesses and proves both recursive guards.
Its only input derivation is the ordinary typing of its stored member value. -/
theorem packTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {payload : Term} {member answer : WFTy s.typeDepth}
    (typing : Recursive.HasType s context payload member) :
    Recursive.HasType s context (pack (object payload)) ((interface answer).package answer) := by
  refine .recursive (definition member answer) ?_
  rw [RecursivePackage.pack_liftTypes, (interface answer).package_weaken, interface_weaken]
  exact Interface.recursivePackTyping
    (interfaceInstance (s := (definition member answer).openContext s)
      member.weaken (definition member answer).name answer.weaken
      ((definition member answer).unfold s) ((definition member answer).fold s))
    (objectTyping typing)

end CDotFCCT.CTML.NativeFieldSharing
