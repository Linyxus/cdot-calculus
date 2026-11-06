import CDotFCCT.CTML.ComplementedGhostCodes

/-!
# Finite syntactic certificates for completeness of pure ghost codes

Recursive references may name arbitrary ambient types, rather than a fresh
consecutive block. A schema generates its equation and leaf-completeness guards;
validating those guards entails completeness of each named code. The schema does
not contain a semantic entailment or change the target subtyping judgment.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CodeCompleteness

open CTMLCore (WFTy WFConstraint)
open CTMLCore.Syntax CTMLCore.Indexed
open CarrierEquation ComplementedGhostCodes

variable {ghost : FieldName → Bool} {depth size : Nat}

def instantiate (names : Fin size → WFTy depth) : Expr ghost depth size → WFTy depth
  | .leaf type => type
  | .ref index => names index
  | .neg body => WFTy.neg (instantiate names body)
  | .joint kind left right => WFTy.joint kind (instantiate names left) (instantiate names right)
  | .record field _ body => WFTy.record field (instantiate names body)

def leafGuards : Expr ghost depth size → List (WFConstraint depth)
  | .leaf type => [ComplementedProduct.complementGuard type]
  | .ref _ => []
  | .neg body => leafGuards body
  | .joint _ left right => leafGuards left ++ leafGuards right
  | .record _ _ body => leafGuards body

structure Schema (ghost : FieldName → Bool) (depth size : Nat) where
  system : System ghost depth size
  names : Fin size → WFTy depth

namespace Schema

def body (schema : Schema ghost depth size) (index : Fin size) : WFTy depth :=
  instantiate schema.names (schema.system.body index)

def unfoldGuard (schema : Schema ghost depth size) (index : Fin size) : WFConstraint depth :=
  WFConstraint.constr (schema.names index) (schema.body index)

def foldGuard (schema : Schema ghost depth size) (index : Fin size) : WFConstraint depth :=
  WFConstraint.constr (schema.body index) (schema.names index)

def equations (schema : Schema ghost depth size) : List (WFConstraint depth) :=
  List.ofFn schema.unfoldGuard ++ List.ofFn schema.foldGuard

def requirements (schema : Schema ghost depth size) : List (WFConstraint depth) :=
  schema.equations ++ (List.ofFn fun index => leafGuards (schema.system.body index)).flatten

def conclusion (schema : Schema ghost depth size) (index : Fin size) : WFConstraint depth :=
  ComplementedProduct.complementGuard (schema.names index)

end Schema

theorem interpret_instantiate (names : Fin size → WFTy depth)
    (expression : Expr ghost depth size) (env : Environment) :
    interpret ghost env (instantiate names expression).raw =
      expression.denote (fun type => interpret ghost env type.raw)
        (fun index => interpret ghost env (names index).raw) :=
  match expression with
  | .leaf _ => rfl
  | .ref _ => rfl
  | .neg body => congrArg negative (interpret_instantiate names body env)
  | .joint kind left right => congrArg₂ (joint kind)
      (interpret_instantiate names left env) (interpret_instantiate names right env)
  | .record field marked body => by
      simpa only [instantiate, WFTy.record, interpret, Expr.denote,
        Mixed.record, marked, ↓reduceIte] using
        congrArg (TransparentRecord.record field) (interpret_instantiate names body env)

theorem leafGuards_sound (expression : Expr ghost depth size) (env : Environment) (n : Nat)
    (valid : ∀ guard ∈ leafGuards expression, interpretGuard ghost env guard.raw n) :
    LeavesComplemented (fun type => interpret ghost env type.raw) n expression := by
  induction expression with
  | leaf type => exact valid (ComplementedProduct.complementGuard type) List.mem_cons_self
  | ref _ => trivial
  | neg _ ih => exact ih valid
  | joint _ left right ihLeft ihRight =>
      exact ⟨ihLeft (fun guard member => valid guard (List.mem_append_left _ member)),
        ihRight (fun guard member => valid guard (List.mem_append_right _ member))⟩
  | record _ _ _ ih => exact ih valid

namespace Schema

theorem equations_agree (schema : Schema ghost depth size) (env : Environment) (n : Nat)
    (valid : ∀ guard ∈ schema.equations, interpretGuard ghost env guard.raw n)
    (index : Fin size) :
    Agree n (interpret ghost env (schema.names index).raw)
      (interpret ghost env (schema.body index).raw) := by
  have forward := valid (schema.unfoldGuard index)
    (List.mem_append_left _ (List.mem_ofFn.mpr ⟨index, rfl⟩))
  have backward := valid (schema.foldGuard index)
    (List.mem_append_right _ (List.mem_ofFn.mpr ⟨index, rfl⟩))
  intro k within
  apply Prod.ext <;> funext term <;> apply propext
  · exact ⟨(forward k within term).1, (backward k within term).1⟩
  · exact ⟨(backward k within term).2, (forward k within term).2⟩

/-- Soundness uses only the guards computed from this finite schema. -/
theorem sound (schema : Schema ghost depth size) (env : Environment) (n : Nat)
    (valid : Validates ghost ⟨depth, schema.requirements⟩ env n) (index : Fin size) :
    interpretGuard ghost env (schema.conclusion index).raw n := by
  apply equations_guard schema.system
    (parameters := fun type => interpret ghost env type.raw)
    (selves := fun index => interpret ghost env (schema.names index).raw)
  · intro component
    apply leafGuards_sound (schema.system.body component) env n
    intro guard member
    exact valid guard (List.mem_append_right _ (List.mem_flatten.mpr
      ⟨_, List.mem_ofFn.mpr ⟨component, rfl⟩, member⟩))
  · intro component k within
    exact (schema.equations_agree env n
      (fun guard member => valid guard (List.mem_append_left _ member)) component k within).trans
      (congrFun (interpret_instantiate schema.names (schema.system.body component) env) k)

end Schema

end CDotFCCT.CTML.Mixed.CodeCompleteness
