import CDotFCCT.CTML.CarrierFieldInvariant
import CDotFCCT.CTML.RecursivePackages

/-!
# A self-aliasing field with a fixed carrier anchor

The recursive equation defines the native record row. Its field package reuses
the surrounding finite member witnesses and the object thunk's payload type.
The recursion passes through the ordinary runtime record field, even though the
package also contains reflective carrier labels and arbitrary constraints.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.SelfFieldAnchor

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation
open CarrierLayout CarrierFieldInvariant

universe u
variable {Label : Type u} [DecidableEq Label]

def objectType {depth : Nat} (row : WFTy depth) : WFTy depth :=
  WFTy.arrow (WFTy.cls "$Unit") row

/-- Existing members are retained; only the payload slot names the recursive object. -/
def witnesses {depth : Nat} (payload : Label) (members : Label → WFTy depth) :
    Label → WFTy (depth + 1) :=
  fun label => if label = payload then objectType (WFTy.var 0 (by omega))
    else (members label).weaken

theorem witnesses_payload {depth : Nat} (payload : Label) (members : Label → WFTy depth) :
    witnesses payload members payload = objectType (WFTy.var 0 (by omega)) := by
  simp only [witnesses, ite_true]

/-- The equation's outer constructor is the ordinary field, with no arrow guard needed. -/
def definition {depth : Nat} (support : List Label) (payload : Label)
    (members : Label → WFTy depth) (field : FieldName) (ordinary : carrierPolicy field = false)
    (answer : WFTy depth) : Definition carrierPolicy depth :=
  .record field ordinary
    ((anchoredInterface support payload (witnesses payload members)).package answer.weaken)

/-- The source object has one field whose right-hand side is its bound self variable. -/
def object (field : FieldName) : Term :=
  .fix (.abs (.abs (.record "DOT" (.cons field (pack (.var 1)) .nil (by simp)))))

theorem object_runtime [CDot.Signature] (env : TermCPS.Env)
    (tag : CDot.Path) (tagLabel : CDot.Signature.TypLabel) (body : CDot.Typ)
    (field : CDot.Signature.TrmLabel) :
    TermCPS.value env
      (.new tag tagLabel body (.cons .nil (.trm field (.path (.select (.bound 0) []))))) =
      some (object (env.fieldName field)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The constructor generates the record equation and all package witnesses itself. -/
theorem objectTyping (support : List Label) (payload : Label) (present : payload ∈ support)
    {s : SubtypingContext} (context : TypingContext s.typeDepth)
    (members : Label → WFTy s.typeDepth) (field : FieldName)
    (ordinary : carrierPolicy field = false) (answer : WFTy s.typeDepth) :
    HasType carrierPolicy
      ((definition support payload members field ordinary answer).native.openContext s)
      context.bindType (object field)
      (objectType (definition support payload members field ordinary answer).native.name) := by
  refine .fixpoint (.abstraction (.abstraction (.subsumption
    (.record (.cons ?_ .nil)) (.native (.trans .interRight
      ((definition support payload members field ordinary answer).native.fold s))))))
  apply interfacePackVariableTyping
    (packingInstance
      (s := (definition support payload members field ordinary answer).native.openContext s)
      support payload present (witnesses payload members)
      (precise support (witnesses payload members)) (.native .refl))
  rw [witnesses_payload]
  exact .there .here

/-- Export the solved row and both equations while retaining the fixed member witnesses. -/
def exportedInterface {depth : Nat} (recursive : Definition carrierPolicy depth) :
    Interface depth :=
  Interface.closeGuards 1
    [WFConstraint.constr recursive.body recursive.native.name,
      WFConstraint.constr recursive.native.name recursive.body]
    (objectType recursive.native.name)

theorem consumerSubtype {s : SubtypingContext} (recursive : Definition carrierPolicy s.typeDepth)
    (answer : WFTy s.typeDepth) :
    Subtype (recursive.native.openContext s)
      (((exportedInterface recursive).consumer answer).weaken)
      (WFTy.arrow (objectType recursive.native.name) answer.weaken) := by
  have opened := (Interface.bindBlock_open s 1
    (Interface.guards
      [WFConstraint.constr recursive.body recursive.native.name,
        WFConstraint.constr recursive.native.name recursive.body]
      (.payload (objectType recursive.native.name))) answer).mapAssumptions
        (target := (recursive.native.openContext s).assumptions)
        (fun guard member => @Subtype.hyp (recursive.native.openContext s) guard
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)))
  refine opened.trans (Interface.guards_open _ _ _ ?_)
  exact fun guard member => @Subtype.hyp (recursive.native.openContext s) guard
    (List.mem_append_left _ member)

/-- The complete generated self object exports its solved row in one existential package. -/
theorem packTyping (support : List Label) (payload : Label) (present : payload ∈ support)
    {s : SubtypingContext} (context : TypingContext s.typeDepth)
    (members : Label → WFTy s.typeDepth) (field : FieldName)
    (ordinary : carrierPolicy field = false) (answer : WFTy s.typeDepth) :
    HasType carrierPolicy s context (pack (object field))
      ((exportedInterface
        (definition support payload members field ordinary answer)).package answer) := by
  refine .recursive (definition support payload members field ordinary answer) ?_
  refine .abstraction (.application
    ((HasType.native (.var _ 0 _ .here)).subsumption
      (.native (consumerSubtype (definition support payload members field ordinary answer) answer)))
    ?_)
  exact objectTyping support payload present
    (context.bind ((exportedInterface
      (definition support payload members field ordinary answer)).consumer answer))
    members field ordinary answer

set_option backward.isDefEq.respectTransparency false in
/-- Any value at the solved object type returns that same fixed type through its self field. -/
theorem fieldCallTyping (support : List Label) (payload : Label) (present : payload ∈ support)
    {s : SubtypingContext} (context : TypingContext (s.typeDepth + 1))
    (members : Label → WFTy s.typeDepth) (field : FieldName)
    (ordinary : carrierPolicy field = false) (answer : WFTy s.typeDepth)
    {parent continuation : Term}
    (parentTyping : HasType carrierPolicy
      ((definition support payload members field ordinary answer).native.openContext s)
      context parent
      (objectType (definition support payload members field ordinary answer).native.name))
    (continuationTyping : HasType carrierPolicy
      ((definition support payload members field ordinary answer).native.openContext s)
      context continuation
      (WFTy.arrow
        (objectType (definition support payload members field ordinary answer).native.name)
        answer.weaken)) :
    HasType carrierPolicy
      ((definition support payload members field ordinary answer).native.openContext s)
      context (fieldCall parent field continuation) answer.weaken := by
  apply CarrierFieldInvariant.fieldCallTyping support payload present
    (s := (definition support payload members field ordinary answer).native.openContext s)
    (witnesses payload members) field answer.weaken
    (parentTyping.subsumption (.native (.arrow .refl
      ((definition support payload members field ordinary answer).native.unfold s))))
  simpa only [witnesses_payload, RecursiveType.name] using continuationTyping

theorem computation_runtime [CDot.Signature] (env : TermCPS.Env)
    (tag : CDot.Path) (tagLabel : CDot.Signature.TypLabel) (body : CDot.Typ)
    (field : CDot.Signature.TrmLabel) :
    TermCPS.computation env
      (.val (.new tag tagLabel body
        (.cons .nil (.trm field (.path (.select (.bound 0) [])))))) =
      some (pack (object (env.fieldName field))) := by
  rfl

def unit : Term := .record "$Unit" .nil

/-- Force a self-aliasing object and run its field with a terminating continuation. -/
def program (field : FieldName) : Term := fieldCall (object field) field (.abs unit)

theorem programTyping (field : FieldName) (ordinary : carrierPolicy field = false) :
    HasType carrierPolicy SubtypingContext.empty TypingContext.empty (program field)
      (WFTy.cls "$Unit") := by
  refine .recursive
    (definition [()] () (fun _ => WFTy.top) field ordinary (WFTy.cls "$Unit")) ?_
  exact fieldCallTyping [()] () List.mem_cons_self (s := SubtypingContext.empty)
    TypingContext.empty (fun _ => WFTy.top) field ordinary (WFTy.cls "$Unit")
    (objectTyping [()] () List.mem_cons_self (s := SubtypingContext.empty)
      TypingContext.empty (fun _ => WFTy.top) field ordinary (WFTy.cls "$Unit"))
    (.abstraction (.native (.record .nil)))

def recordValue (field : FieldName) : Term :=
  .record "DOT" (.cons field (pack (.abs (.app (object field) (.var 0)))) .nil (by simp))

theorem forceSteps (field : FieldName) :
    Steps (.app (object field) unit) (recordValue field) := by
  refine .trans (.appHead _ (.fixUnfold (.abs _))) ?_
  refine .trans (.appBeta _ _ (.record _ _ .nil)) ?_
  refine .trans (.appHead _ (.appBeta _ _ (.abs _))) ?_
  exact .trans (.appBeta _ _ (.record _ _ .nil)) .refl

theorem programSteps (field : FieldName) : Steps (program field) unit := by
  refine (((forceSteps field).projHead field).appHead (.abs unit)).trans' ?_
  refine .trans (.appHead _ (.proj (.record _ _ (.cons (.abs _) .nil)) .here)) ?_
  refine .trans (.appBeta _ _ (.abs _)) ?_
  exact .trans (.appBeta _ _ (.abs _)) .refl

theorem programSafe (field : FieldName) (ordinary : carrierPolicy field = false)
    {reached : Term} (steps : Steps (program field) reached) :
    Value reached ∨ ∃ next, Step reached next := (programTyping field ordinary).safe steps

end CDotFCCT.CTML.Mixed.SelfFieldAnchor
