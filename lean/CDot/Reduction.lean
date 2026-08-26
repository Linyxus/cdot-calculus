import CDot.Lookup

/-!
# Operational semantics

Lean port of `cdot/Reduction.v`.
-/

namespace CDot

variable [Signature]

def ResolvedPath (σ : Sta) (p : Path) : Prop :=
  ∃ v, LookupStep σ (.path p) (.val v)

abbrev State := Sta × Trm

inductive Red : State → State → Prop where
  | resolve : LookupStep σ (.path p) (.path q) →
      Red (σ, .path p) (σ, .path q)
  | app : LookupStep σ (.path q) (.val (.lambda T t)) → ResolvedPath σ p →
      Red (σ, .app q p) (σ, t.openPath p)
  | ctxAppFun : Red (σ, .path q) (σ, .path q') →
      Red (σ, .app q p) (σ, .app q' p)
  | ctxAppArg : ResolvedPath σ q → Red (σ, .path p) (σ, .path p') →
      Red (σ, .app q p) (σ, .app q p')
  | letVal : Env.Fresh x σ →
      Red (σ, .letE (.val v) t) (σ.push x v, t.open x)
  | letPath : ResolvedPath σ p →
      Red (σ, .letE (.path p) t) (σ, t.openPath p)
  | letTarget : Red (σ, t₀) (σ', t₀') →
      Red (σ, .letE t₀ t) (σ', .letE t₀' t)
  | caseMatch : ResolvedPath σ r →
      LookupStep σ (.path p) (.val (.new q A T ds)) →
      Lookup σ (.path (q.openPath p)) (.path r) →
      Red (σ, .caseE p r A t₁ t₂) (σ, t₁.openPath p)
  | caseElse : ResolvedPath σ r₁ → ResolvedPath σ r₂ →
      LookupStep σ (.path p) (.val (.new q A₁ T ds)) →
      Lookup σ (.path (q.openPath p)) (.path r₁) →
      (r₁ ≠ r₂ ∨ A₁ ≠ A₂) →
      Red (σ, .caseE p r₂ A₂ t₁ t₂) (σ, t₂)
  | caseLambda : LookupStep σ (.path p) (.val (.lambda T t)) →
      Red (σ, .caseE p r A t₁ t₂) (σ, t₂)
  | ctxCaseScrutinee : Red (σ, .path p) (σ, .path p') →
      Red (σ, .caseE p r A t₁ t₂) (σ, .caseE p' r A t₁ t₂)
  | ctxCaseTag : ResolvedPath σ p → Red (σ, .path r) (σ, .path r') →
      Red (σ, .caseE p r A t₁ t₂) (σ, .caseE p r' A t₁ t₂)

abbrev Reds := Star Red

inductive NormalForm : Sta → Trm → Prop where
  | path : ResolvedPath σ p → NormalForm σ (.path p)
  | val : NormalForm σ (.val v)

end CDot
