import CDotFCCT.TermCPSRecords
import CDotFCCT.CTML.RecursiveInterfaces

/-!
# The native recursive object step of the CPS typing proof

The recursive self equation is generated from the native record's field types.
Every recursive occurrence is guarded by a record, regardless of the field type's
internal shape. The constructor lemma consumes the translated field derivations,
which are induction hypotheses for a complete compiler; it does not claim to
generate those derivations from arbitrary source definitions yet.
-/

set_option autoImplicit false

namespace CDotFCCT.TermCPS

open CTMLCore CTMLCore.Syntax

private theorem recordFold_guarded {depth : Nat} (index : Nat)
    (entries : List (String × WFTy depth)) (start : WFTy depth)
    (guarded : start.raw.GuardedAt index) :
    (entries.foldl (fun row entry => WFTy.intersection row
      (WFTy.record entry.1 entry.2)) start).raw.GuardedAt index :=
  match entries with
  | [] => guarded
  | entry :: rest => recordFold_guarded index rest
      (WFTy.intersection start (WFTy.record entry.1 entry.2)) ⟨guarded, trivial⟩

/-- The native record itself guards the self equation; no arrow test is imposed. -/
def objectDefinition {depth : Nat} (entries : List (String × WFTy (depth + 1))) :
    RecursiveType depth :=
  ⟨recordResultType "DOT" entries, recordFold_guarded 0 entries (WFTy.cls "DOT") trivial⟩

def nativeObjectThunk {names : List String} (contents : TermFields names) : Term :=
  .fix (.abs (.abs (.record "DOT" contents)))

/-- Tie the self thunk using the actual field proofs and a native row bound. -/
theorem nativeObjectThunkTyping {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {self : WFTy s.typeDepth}
    {names : List String} {contents : TermFields names}
    {types : List (String × WFTy s.typeDepth)}
    (typing : Recursive.FieldsHaveType s
      ((context.bind (WFTy.arrow WFTy.top self)).bind WFTy.top) contents types)
    (fold : Subtype s (recordResultType "DOT" types) self) :
    Recursive.HasType s context (nativeObjectThunk contents) (WFTy.arrow WFTy.top self) :=
  .fixpoint (.abstraction (.abstraction
    ((Recursive.HasType.record typing).subsumption fold)))

/-- The generated record equation discharges the constructor's row bound. -/
theorem recursiveObjectThunkTyping {s : SubtypingContext}
    {context : TypingContext (s.typeDepth + 1)}
    {names : List String} {contents : TermFields names}
    (types : List (String × WFTy (s.typeDepth + 1)))
    (typing : Recursive.FieldsHaveType ((objectDefinition types).openContext s)
      ((context.bind (WFTy.arrow WFTy.top (objectDefinition types).name)).bind WFTy.top)
      contents types) :
    Recursive.HasType ((objectDefinition types).openContext s) context
      (nativeObjectThunk contents) (WFTy.arrow WFTy.top (objectDefinition types).name) :=
  nativeObjectThunkTyping typing ((objectDefinition types).fold s)

variable [CDot.Signature]

theorem computation_object {env : Env} {tag : CDot.Path}
    {label : CDot.Signature.TypLabel} {body : CDot.Typ} {definitions : CDot.Defs}
    {entries : List (String × Term)}
    (compiled : fields ((env.weaken 1).bind.weaken 1) definitions = some entries) :
    computation env (.val (.new tag label body definitions)) =
      some (.abs (.app (.var 0) (nativeObjectThunk (recordFields entries).2))) := by
  simp [computation, run, value, compiled, nativeObjectThunk]

theorem compile_object_eq {env : Env} {sourceContext : CDot.Ctx} {tag : CDot.Path}
    {label : CDot.Signature.TypLabel} {body result : CDot.Typ} {definitions : CDot.Defs}
    {entries : List (String × Term)}
    (compiled : fields ((env.weaken 1).bind.weaken 1) definitions = some entries)
    (derivation : Core.Typing sourceContext
      (.val (.new tag label body definitions)) result) :
    compile env derivation =
      .abs (.app (.var 0) (nativeObjectThunk (recordFields entries).2)) := by
  simp [compile, computation_object compiled]

/-- The object case needs field induction hypotheses and generated package evidence,
not a different runtime compiler. Both inputs remain obligations of the general proof. -/
theorem compileObjectTyping {env : Env} {sourceContext : CDot.Ctx} {tag : CDot.Path}
    {label : CDot.Signature.TypLabel} {body result : CDot.Typ} {definitions : CDot.Defs}
    {entries : List (String × Term)}
    (compiled : fields ((env.weaken 1).bind.weaken 1) definitions = some entries)
    (derivation : Core.Typing sourceContext
      (.val (.new tag label body definitions)) result)
    {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {self answer : WFTy s.typeDepth} {interface : CTML.Interface s.typeDepth}
    {types : List (String × WFTy s.typeDepth)}
    (typing : Recursive.FieldsHaveType s
      (((context.bind (interface.consumer answer)).bind
        (WFTy.arrow WFTy.top self)).bind WFTy.top) (recordFields entries).2 types)
    (fold : Subtype s (recordResultType "DOT" types) self)
    (inst : CTML.Interface.Instance s interface (WFTy.arrow WFTy.top self)) :
    Recursive.HasType s context (compile env derivation) (interface.package answer) :=
  (compile_object_eq compiled derivation).symm ▸
    Recursive.HasType.abstraction (.application
      ((Recursive.HasType.native (.var _ 0 _ .here)).subsumption
        (inst.consumerSubtype answer)) (nativeObjectThunkTyping typing fold))

end CDotFCCT.TermCPS
