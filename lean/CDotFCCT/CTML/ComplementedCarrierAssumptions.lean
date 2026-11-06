import CDotFCCT.CTML.ComplementedGhostCodes

/-!
# Pure carrier equations entail completeness in every valid environment

The equation guards, not the chosen fixed-point construction, justify the result.
Only occurring outer leaves require completeness guards, interpreted after their
weakening into the simultaneous block. No subtyping or typing rule is added here.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.ComplementedCarrierAssumptions

open CTMLCore (WFTy)
open CTMLCore.Syntax CTMLCore.Indexed
open CarrierEquation ComplementedGhostCodes

variable {ghost : FieldName → Bool} {depth size : Nat}

/-- Read the pure syntax directly in its current scope, without choosing a solution environment. -/
theorem denote_compile (expression : Expr ghost depth size) (env : Environment) :
    expression.denote (fun type => interpret ghost env (type.weakenBy size).raw)
        (fun index => prefixClosure (env index)) =
      interpret ghost env expression.compile.raw :=
  match expression with
  | .leaf _ => rfl
  | .ref _ => rfl
  | .neg body => congrArg negative (denote_compile body env)
  | .joint kind left right => congrArg₂ (joint kind)
      (denote_compile left env) (denote_compile right env)
  | .record field marked body => by
      simpa only [Expr.denote, Expr.compile, WFTy.record, interpret,
        Mixed.record, marked, ↓reduceIte] using
        congrArg (TransparentRecord.record field) (denote_compile body env)

/-- The two inclusions in each equation give equality of both observations. -/
theorem equations_agree (system : System ghost depth size) (env : Environment) (n : Nat)
    (valid : Validates ghost ⟨depth + size, system.equations⟩ env n) (index : Fin size) :
    Agree n (interpret ghost env (system.name index).raw)
      (interpret ghost env (system.compile index).raw) := by
  have forward := valid (system.unfoldGuard index)
    (List.mem_append_left _ (List.mem_ofFn.mpr ⟨index, rfl⟩))
  have backward := valid (system.foldGuard index)
    (List.mem_append_right _ (List.mem_ofFn.mpr ⟨index, rfl⟩))
  intro k within
  apply Prod.ext <;> funext term <;> apply propext
  · exact ⟨(forward k within term).1, (backward k within term).1⟩
  · exact ⟨(backward k within term).2, (forward k within term).2⟩

/-- Completeness follows from equation validity and the actual weakened leaf guards. -/
theorem guard (system : System ghost depth size) (env : Environment) (n : Nat)
    (valid : Validates ghost ⟨depth + size, system.equations⟩ env n)
    (leaves : ∀ index, Leaves
      (fun type => interpretGuard ghost env
        (ComplementedProduct.complementGuard (type.weakenBy size)).raw n)
      (system.body index))
    (index : Fin size) :
    interpretGuard ghost env (ComplementedProduct.complementGuard (system.name index)).raw n := by
  apply equations_guard system
    (parameters := fun type => interpret ghost env (type.weakenBy size).raw)
    (selves := fun index => prefixClosure (env index)) leaves
  intro component k within
  exact (equations_agree system env n valid component k within).trans
    (congrFun (denote_compile (system.body component) env).symm k)

end CDotFCCT.CTML.Mixed.ComplementedCarrierAssumptions
