import CDotFCCT.CoreSyntax
import CTMLCore.Language.DeBruijn

/-!
# Runtime CPS translation of core DOT

This pass handles every term admitted by `Core.Typing`, including nested objects,
runtime self references, and path aliases. Objects use native CTML records. A
fixed-point function returns the record when forced; its fields contain suspended
CPS computations, so constructing an object does not evaluate its path aliases.
Only the cDOT runtime tag test, excluded from the core input judgment, is rejected.

This module establishes syntax coverage. The target typing theorem must also
account for each object's shared type witnesses and is a separate obligation.
-/

set_option autoImplicit false

namespace CDotFCCT.TermCPS

variable [CDot.Signature]

abbrev Term := CTMLCore.Syntax.Term

/-- Target indices for source variables; label names must be injective on the
finite set of labels used by a program. -/
structure Env where
  free : CDot.Var → Nat
  bound : Nat → Nat
  fieldName : CDot.Signature.TrmLabel → String

def Env.weaken (env : Env) (amount : Nat) : Env where
  free x := env.free x + amount
  bound i := env.bound i + amount
  fieldName := env.fieldName

def Env.bind (env : Env) : Env where
  free x := env.free x + 1
  bound
    | 0 => 0
    | i + 1 => env.bound i + 1
  fieldName := env.fieldName

def unit : Term := .record "$Unit" .nil

/-- Keep the last occurrence of a field name, as source definition lookup does.
Well-typed definition lists have distinct labels, so no field is dropped there. -/
def recordFields (entries : List (String × Term)) :
    (names : List String) × CTMLCore.Syntax.TermFields names :=
  match entries with
  | [] => ⟨[], .nil⟩
  | (name, term) :: rest =>
      let ⟨names, fields⟩ := recordFields rest
      if duplicate : name ∈ names then ⟨names, fields⟩
      else ⟨name :: names, .cons name term fields duplicate⟩

/-- Field lists are stored inside out in DOT paths. Each projection forces the
object thunk and then runs the selected field's suspended computation. -/
def project (fieldName : CDot.Signature.TrmLabel → String) (root : Term) :
    CDot.Fields → Term → Term
  | [], continuation => .app continuation root
  | label :: rest, continuation =>
      project fieldName root rest
        (.abs (.app (.proj (.app (.var 0) unit) (fieldName label))
          (continuation.lift 1)))

def path (env : Env) (p : CDot.Path) (continuation : Term) : Term :=
  match p with
  | .select root fields =>
      let index := match root with
        | .free x => env.free x
        | .bound i => env.bound i
      project env.fieldName (.var index) fields continuation

mutual
  /-- A command sends its result to the supplied continuation. -/
  def run (env : Env) : CDot.Trm → Term → Option Term
    | .path p, continuation => some (path env p continuation)
    | .app function argument, continuation =>
        some (path env function (.abs (path (env.weaken 1) argument
          (.abs (.app (.app (.var 1) (.var 0)) (continuation.lift 2))))))
    | .val v, continuation => return .app continuation (← value env v)
    | .letE rhs body, continuation => do
        let bodyCommand ← run env.bind body (continuation.lift 1)
        run env rhs (.abs bodyCommand)
    | .caseE .., _ => none

  def value (env : Env) : CDot.Val → Option Term
    | .lambda _ body => return .abs (.abs (← run (env.bind.weaken 1) body (.var 0)))
    | .new _ _ _ definitions => do
        let entries ← fields (env.bind.weaken 1) definitions
        let ⟨_, contents⟩ := recordFields entries
        return .fix (.abs (.abs (.record "DOT" contents)))

  def fields (env : Env) : CDot.Defs → Option (List (String × Term))
    | .nil => some []
    | .cons rest (.typ ..) => fields env rest
    | .cons rest (.trm label rhs) => do
        let earlier ← fields env rest
        let computation ← field env rhs
        return earlier ++ [(env.fieldName label, computation)]

  def field (env : Env) : CDot.DefRhs → Option Term
    | .path p => some (.abs (path (env.weaken 1) p (.var 0)))
    | .val v => return .abs (.app (.var 0) (← value (env.weaken 1) v))
end

def computation (env : Env) (term : CDot.Trm) : Option Term :=
  return .abs (← run (env.weaken 1) term (.var 0))

mutual
  theorem run_total (env : Env) (term : CDot.Trm) (continuation : Term)
      (allowed : Core.testFree term = true) : ∃ result, run env term continuation = some result :=
    match term with
    | .path _ | .app _ _ => ⟨_, rfl⟩
    | .caseE .. => by contradiction
    | .val v => by
        obtain ⟨result, equal⟩ := value_total env v allowed
        exact ⟨.app continuation result, by simp [run, equal]⟩
    | .letE rhs body => by
        have both := Bool.and_eq_true_iff.mp allowed
        obtain ⟨bodyResult, bodyEqual⟩ := run_total env.bind body (continuation.lift 1) both.2
        obtain ⟨rhsResult, rhsEqual⟩ := run_total env rhs (.abs bodyResult) both.1
        exact ⟨rhsResult, by simp [run, bodyEqual, rhsEqual]⟩

  theorem value_total (env : Env) (v : CDot.Val)
      (allowed : Core.valueTestFree v = true) : ∃ result, value env v = some result :=
    match v with
    | .lambda _ body => by
        obtain ⟨result, equal⟩ := run_total (env.bind.weaken 1) body (.var 0) allowed
        exact ⟨.abs (.abs result), by simp [value, equal]⟩
    | .new _ _ _ definitions => by
        obtain ⟨result, equal⟩ := fields_total (env.bind.weaken 1) definitions allowed
        exact ⟨.fix (.abs (.abs (.record "DOT" (recordFields result).2))),
          by simp [value, equal]⟩

  theorem fields_total (env : Env) (definitions : CDot.Defs)
      (allowed : Core.definitionsTestFree definitions = true) :
      ∃ result, fields env definitions = some result :=
    match definitions with
    | .nil => ⟨_, rfl⟩
    | .cons rest (.typ ..) =>
        fields_total env rest (Bool.and_eq_true_iff.mp allowed).1
    | .cons rest (.trm label rhs) => by
        have both := Bool.and_eq_true_iff.mp allowed
        obtain ⟨earlier, earlierEqual⟩ := fields_total env rest both.1
        obtain ⟨result, equal⟩ := field_total env rhs both.2
        exact ⟨earlier ++ [(env.fieldName label, result)],
          by simp [fields, earlierEqual, equal]⟩

  theorem field_total (env : Env) (rhs : CDot.DefRhs)
      (allowed : Core.rhsTestFree rhs = true) : ∃ result, field env rhs = some result :=
    match rhs with
    | .path _ => ⟨_, rfl⟩
    | .val v => by
        obtain ⟨result, equal⟩ := value_total (env.weaken 1) v allowed
        exact ⟨.abs (.app (.var 0) result), by simp [field, equal]⟩
end

/-- The runtime pass is defined on every full core-DOT typing derivation. -/
theorem computation_total (env : Env) {context : CDot.Ctx} {term : CDot.Trm}
    {type : CDot.Typ} (derivation : Core.Typing context term type) :
    (computation env term).isSome = true := by
  obtain ⟨result, equal⟩ := run_total (env.weaken 1) term (.var 0) derivation.testFree
  simp [computation, equal]

/-- Extract the executable result using the source derivation only to prove coverage.
There is no supplied target typing proof or unchecked fallback in this function. -/
def compile (env : Env) {context : CDot.Ctx} {term : CDot.Trm} {type : CDot.Typ}
    (derivation : Core.Typing context term type) : Term :=
  (computation env term).get (computation_total env derivation)

end CDotFCCT.TermCPS
