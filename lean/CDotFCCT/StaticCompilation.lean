import CDot.Definitions
import CTMLCore.Language.DeBruijn

/-!
# Executable erasure for a static-record package and its client

This is a partial syntax pass, not the general DOT compiler. It supports pure
lambda/application/path clients, ordinary lets, and an outer let binding a record
whose fields do not use its runtime self variable. The record's self variable may
occur in type annotations: those erase. Unsupported constructs return `none`.

The record is passed to one CPS consumer, so all its type-member witnesses can be
abstracted together. `RecordCompilation` checks the actual output of this pass,
using the proof-producing opened-derivation translation for its consumer.
-/

set_option autoImplicit false

namespace CDotFCCT.StaticCompilation

variable [CDot.Signature]

abbrev TargetTerm := CTMLCore.Syntax.Term

structure Env where
  free : CDot.Var → Option Nat
  bound : Nat → Option Nat
  fieldName : CDot.Signature.TrmLabel → String

def Env.bind (env : Env) : Env where
  free x := (env.free x).map (· + 1)
  bound
    | 0 => some 0
    | i + 1 => (env.bound i).map (· + 1)
  fieldName := env.fieldName

/-- Erasing a nonrecursive record introduces no target self binder. -/
def Env.hideSelf (env : Env) : Env where
  free := env.free
  bound
    | 0 => none
    | i + 1 => env.bound i
  fieldName := env.fieldName

def path (env : Env) : CDot.Path → Option TargetTerm
  | .select root fields => do
      let index ← match root with
        | .free x => env.free x
        | .bound i => env.bound i
      return fields.foldr (fun label term => .proj term (env.fieldName label)) (.var index)

mutual
  def pureTerm (env : Env) : CDot.Trm → Option TargetTerm
    | .val v => value env v
    | .path p => path env p
    | .app function argument => do
        return .app (← path env function) (← path env argument)
    | .letE rhs body => do
        return .app (.abs (← pureTerm env.bind body)) (← pureTerm env rhs)
    | .caseE .. => none

  def value (env : Env) : CDot.Val → Option TargetTerm
    | .lambda _ body => return .abs (← pureTerm env.bind body)
    | .new .. => none
end

def fieldValue (env : Env) : CDot.DefRhs → Option TargetTerm
  | .val v => value env v
  | .path p => path env p

def fields (env : Env) : CDot.Defs → Option (List (String × TargetTerm))
  | .nil => some []
  | .cons rest (.typ ..) => fields env rest
  | .cons rest (.trm label rhs) => do
      let earlierFields ← fields env rest
      let result ← fieldValue env rhs
      return earlierFields ++ [(env.fieldName label, result)]

/-- Construct native record syntax, checking distinct labels as its grammar requires. -/
def recordFields (entries : List (String × TargetTerm)) :
    Option (CTMLCore.Syntax.TermFields (entries.map Prod.fst)) :=
  match entries with
  | [] => some .nil
  | (name, term) :: rest => do
      let tail ← recordFields rest
      if fresh : name ∈ rest.map Prod.fst then none
      else some (.cons name term tail fresh)

def record (env : Env) : CDot.Val → Option TargetTerm
  | .new _ _ _ definitions => do
      let entries ← fields env.hideSelf definitions
      let result ← recordFields entries
      return .record "DOT" result
  | .lambda .. => none

def pack (term : TargetTerm) : TargetTerm :=
  .abs (.app (.var 0) (term.lift 1))

/-- One whole-record package, with the entire client inside its witness scope. -/
def program (env : Env) : CDot.Trm → Option TargetTerm
  | .letE (.val object@(.new ..)) body => do
      return .app (pack (← record env object)) (.abs (← pureTerm env.bind body))
  | term => pureTerm env term

end CDotFCCT.StaticCompilation
