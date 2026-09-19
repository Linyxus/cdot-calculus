import CDotFCCT.CTML.CarrierEquationAliases
import CDotFCCT.CTML.CarrierEquationInterpretation

/-!
# Original alias equations in normalized carrier scopes

The solved guarded scope proves both directions of every original equation,
including direct aliases. Exported packages can therefore retain the original
equation list rather than exposing the normalizer's duplicated guarded bodies.
All entailments below use native subtyping and generated scope assumptions.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierEquation

open CTMLCore CTMLCore.Syntax

variable {ghost : FieldName → Bool} {depth size : Nat}

/-- Both directions of the supplied equations, with no normalization of their bodies. -/
def equationGuards (body : Fin size → Expr ghost depth size) :
    List (WFConstraint (depth + size)) :=
  List.ofFn (fun index => WFConstraint.constr
    (Expr.ref index : Expr ghost depth size).compile (body index).compile) ++
    List.ofFn (fun index => WFConstraint.constr
      (body index).compile (Expr.ref index : Expr ghost depth size).compile)

namespace Aliases

def name (_ : Aliases ghost depth size) (index : Fin size) : WFTy (depth + size) :=
  (Expr.ref index : Expr ghost depth size).compile

def compile (system : Aliases ghost depth size) (index : Fin size) : WFTy (depth + size) :=
  (system.body index).expression.compile

def equations (system : Aliases ghost depth size) : List (WFConstraint (depth + size)) :=
  equationGuards (fun index => (system.body index).expression)

/-- An alias unfolds its normalized equation and folds its target's identical body. -/
theorem unfold (s : SubtypingContext) (system : Aliases ghost s.typeDepth size)
    (fallback : WFTy s.typeDepth) (index : Fin size) :
    Subtype ((system.normalize fallback).openContext s)
      (system.name index) (system.compile index) := by
  change Subtype ((system.normalize fallback).openContext s)
    ((system.normalize fallback).name index) (system.body index).expression.compile
  cases body : system.body index with
  | «alias» next =>
      exact .trans ((system.normalize fallback).unfold s index) (by
        simpa only [System.compile, system.normalize_alias fallback body,
          AliasBody.expression, Expr.compile, System.name] using
          (system.normalize fallback).fold s next)
  | guarded expression guarded =>
      simpa only [System.compile, system.normalize_guarded fallback body,
        AliasBody.expression] using
        (system.normalize fallback).unfold s index

theorem fold (s : SubtypingContext) (system : Aliases ghost s.typeDepth size)
    (fallback : WFTy s.typeDepth) (index : Fin size) :
    Subtype ((system.normalize fallback).openContext s)
      (system.compile index) (system.name index) := by
  change Subtype ((system.normalize fallback).openContext s)
    (system.body index).expression.compile ((system.normalize fallback).name index)
  cases body : system.body index with
  | «alias» next =>
      exact .trans ((system.normalize fallback).unfold s next) (by
        simpa only [System.compile, system.normalize_alias fallback body] using
          (system.normalize fallback).fold s index)
  | guarded expression guarded =>
      simpa only [System.compile, system.normalize_guarded fallback body,
        AliasBody.expression] using
        (system.normalize fallback).fold s index

/-- Every original guard can be discharged in the computed normalized scope. -/
theorem guards (s : SubtypingContext) (system : Aliases ghost s.typeDepth size)
    (fallback : WFTy s.typeDepth) {guard : WFConstraint (s.typeDepth + size)}
    (member : guard ∈ system.equations) :
    Subtype ((system.normalize fallback).openContext s) guard.sub guard.sup := by
  dsimp only [equations, equationGuards] at member
  rcases List.mem_append.mp member with forward | backward
  · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp forward
    exact system.unfold s fallback index
  · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp backward
    exact system.fold s fallback index

/-- A successful raw normalization derives the original equation's forward direction. -/
theorem normalizeChecked_unfold (s : SubtypingContext)
    {body : Fin size → Expr ghost s.typeDepth size} {fallback : WFTy s.typeDepth}
    {normalized : System ghost s.typeDepth size}
    (accepted : normalizeChecked body fallback = some normalized) (index : Fin size) :
    Subtype (normalized.openContext s) (normalized.name index) (body index).compile := by
  cases checked : check body with
  | none => simp only [normalizeChecked, checked, Option.map_none] at accepted; contradiction
  | some checkedBody =>
      have same : checkedBody.val.normalize fallback = normalized :=
        Option.some.inj (by simpa only [normalizeChecked, checked, Option.map_some] using accepted)
      subst normalized
      rw [← checkedBody.property index]
      exact checkedBody.val.unfold s fallback index

theorem normalizeChecked_fold (s : SubtypingContext)
    {body : Fin size → Expr ghost s.typeDepth size} {fallback : WFTy s.typeDepth}
    {normalized : System ghost s.typeDepth size}
    (accepted : normalizeChecked body fallback = some normalized) (index : Fin size) :
    Subtype (normalized.openContext s) (body index).compile (normalized.name index) := by
  cases checked : check body with
  | none => simp only [normalizeChecked, checked, Option.map_none] at accepted; contradiction
  | some checkedBody =>
      have same : checkedBody.val.normalize fallback = normalized :=
        Option.some.inj (by simpa only [normalizeChecked, checked, Option.map_some] using accepted)
      subst normalized
      rw [← checkedBody.property index]
      exact checkedBody.val.fold s fallback index

/-- Package producers can export exactly the guards from the raw finite source block. -/
theorem normalizeChecked_guards (s : SubtypingContext)
    {body : Fin size → Expr ghost s.typeDepth size} {fallback : WFTy s.typeDepth}
    {normalized : System ghost s.typeDepth size}
    (accepted : normalizeChecked body fallback = some normalized)
    {guard : WFConstraint (s.typeDepth + size)} (member : guard ∈ equationGuards body) :
    Subtype (normalized.openContext s) guard.sub guard.sup := by
  dsimp only [equationGuards] at member
  rcases List.mem_append.mp member with forward | backward
  · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp forward
    exact normalizeChecked_unfold s accepted index
  · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp backward
    exact normalizeChecked_fold s accepted index

end Aliases

end CDotFCCT.CTML.Mixed.CarrierEquation
