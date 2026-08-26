import CDot.Weakening
import CDot.Sequences

/-!
# Runtime lookup of paths

Lean port of `cdot/Lookup.v`.
-/

namespace CDot

variable [Signature]

inductive LookupStep (σ : Sta) : DefRhs → DefRhs → Prop where
  | var : Env.Binds x v σ → LookupStep σ (.path (.var x)) (.val v)
  | selectPath : LookupStep σ (.path p) (.path q) →
      LookupStep σ (.path (p.selectField a)) (.path (q.selectField a))
  | selectVal : LookupStep σ (.path p) (.val (.new q A T ds)) →
      ds.Has (.trm a rhs) →
      LookupStep σ (.path (p.selectField a)) (rhs.openPath p)

def Lookup (σ : Sta) : DefRhs → DefRhs → Prop := Star (LookupStep σ)

def lookupFieldsStep (σ : Sta) (x : AVar) : Fields → Option DefRhs
  | [] =>
      match x with
      | .bound _ => none
      | .free y => (Env.get y σ).map DefRhs.val
  | a :: fields =>
      let p := Path.select x fields
      match lookupFieldsStep σ x fields with
      | some (.path q) => some (.path (q.selectField a))
      | some (.val (.new _ _ _ ds)) =>
          match ds.get (.trm a) with
          | some (.trm _ rhs) => some (rhs.openPath p)
          | _ => none
      | _ => none

def lookupPathStep (σ : Sta) : Path → Option DefRhs
  | .select x fields => lookupFieldsStep σ x fields

def lookupSourceStep (σ : Sta) : DefRhs → Option DefRhs
  | .path p => lookupPathStep σ p
  | .val _ => none

theorem lookup_empty {p : Path} {rhs : DefRhs}
    (h : LookupStep (Env.empty : Sta) (.path p) rhs) : False := by
  suffices ∀ src rhs, LookupStep (Env.empty : Sta) src rhs → False by
    exact this _ _ h
  intro src rhs hstep
  induction hstep
  case var hbind => exact hbind.empty_false
  case selectPath _ ih => exact ih
  case selectVal _ _ ih => exact ih

def DefRhs.SourceNamed : DefRhs → Prop
  | .path p => p.Named
  | .val _ => True

theorem LookupStep.sourceNamed' {σ : Sta} {src rhs : DefRhs}
    (h : LookupStep σ src rhs) : src.SourceNamed := by
  induction h with
  | var => exact ⟨_, rfl⟩
  | @selectPath p q a _ ih => exact Path.Named.selectFields ih [a]
  | @selectVal p q A T ds a body _ _ ih =>
      exact Path.Named.selectFields ih [a]

theorem LookupStep.sourceNamed {σ : Sta} {p : Path} {rhs : DefRhs}
    (h : LookupStep σ (.path p) rhs) : p.Named := h.sourceNamed'

theorem LookupStep.mono {σ σ' : Sta} {src rhs : DefRhs}
    (h : LookupStep σ src rhs) (he : Env.Extends σ σ') :
    LookupStep σ' src rhs := by
  induction h with
  | var hb => exact .var (he hb)
  | selectPath _ ih => exact .selectPath ih
  | selectVal _ hhas ih => exact .selectVal ih hhas

theorem Lookup.mono {σ σ' : Sta} {src rhs : DefRhs}
    (h : Lookup σ src rhs) (he : Env.Extends σ σ') :
    Lookup σ' src rhs := by
  induction h with
  | refl => exact .refl _
  | step hs hrest ih => exact .step (hs.mono he) ih

theorem LookupStep.strengthenPush {σ : Sta} {y x : Var} {v : Val}
    {fields : Fields} {rhs : DefRhs}
    (h : LookupStep (σ.push y v) (.path (.select (.free x) fields)) rhs)
    (hyx : y ≠ x) :
    LookupStep σ (.path (.select (.free x) fields)) rhs := by
  generalize heq : (DefRhs.path (.select (.free x) fields)) = src at h
  induction h generalizing x fields with
  | var hb =>
      injection heq with heq
      simp only [Path.var] at heq
      injection heq with havar hfields
      cases havar
      cases hfields
      cases hb with
      | here => exact False.elim (hyx rfl)
      | there _ hb => exact .var hb
  | selectPath hs ih =>
      rename_i p q a
      injection heq with heq
      cases p with
      | select av rest =>
          simp only [Path.selectField] at heq
          injection heq with havar hfields
          cases havar
          cases hfields
          exact .selectPath (ih hyx rfl)
  | selectVal hs hhas ih =>
      rename_i p q A T ds a body
      injection heq with heq
      cases p with
      | select av rest =>
          simp only [Path.selectField] at heq
          injection heq with havar hfields
          cases havar
          cases hfields
          exact .selectVal (ih hyx rfl) hhas

theorem LookupStep.weakenPush {σ : Sta} {src rhs : DefRhs} {y : Var} {v : Val}
    (h : LookupStep σ src rhs) (hy : Env.Fresh y σ) :
    LookupStep (σ.push y v) src rhs :=
  h.mono (.pushRight hy v)

theorem Lookup.weakenPush {σ : Sta} {src rhs : DefRhs} {y : Var} {v : Val}
    (h : Lookup σ src rhs) (hy : Env.Fresh y σ) :
    Lookup (σ.push y v) src rhs :=
  h.mono (.pushRight hy v)

theorem lookup_val_inv {σ : Sta} {v : Val} {rhs : DefRhs}
    (h : Lookup σ (.val v) rhs) : rhs = .val v := by
  cases h with
  | refl => rfl
  | step hstep _ => cases hstep

theorem lookupStep_eq_function {σ : Sta} {src rhs : DefRhs}
    (h : LookupStep σ src rhs) : lookupSourceStep σ src = some rhs := by
  induction h
  case var hbind =>
    change lookupFieldsStep σ (.free _) [] = some (.val _)
    simp [lookupFieldsStep, hbind.get_eq_some]
  case selectPath p q a _ ih =>
    cases p with
    | select x fields =>
      change lookupFieldsStep σ x fields = some (.path q) at ih
      change lookupFieldsStep σ x (a :: fields) = some (.path (q.selectField a))
      simp [lookupFieldsStep, ih]
  case selectVal p q A T ds a rhs _ has ih =>
    cases p with
    | select x fields =>
      change lookupFieldsStep σ x fields = some (.val (.new q A T ds)) at ih
      change lookupFieldsStep σ x (a :: fields) =
        some (rhs.openPath (.select x fields))
      unfold Defs.Has at has
      change ds.get (.trm a) = some (.trm a rhs) at has
      simp [lookupFieldsStep, ih, has]

theorem LookupStep.eq_lookupPathStep {σ : Sta} {p : Path} {rhs : DefRhs}
    (h : LookupStep σ (.path p) rhs) : lookupPathStep σ p = some rhs :=
  lookupStep_eq_function h

theorem lookup_step_functional {σ : Sta} {src rhs₁ rhs₂ : DefRhs}
    (h₁ : LookupStep σ src rhs₁) (h₂ : LookupStep σ src rhs₂) : rhs₁ = rhs₂ := by
  cases src with
  | val v => cases h₁
  | path p =>
    have h₁' := h₁.eq_lookupPathStep
    have h₂' := h₂.eq_lookupPathStep
    rw [h₁'] at h₂'
    exact Option.some.inj h₂'

theorem lookup_irred {σ : Sta} {v : Val} : Irred (LookupStep σ) (.val v) := by
  intro rhs h
  cases h

theorem lookup_functional {σ : Sta} {p : Path} {v₁ v₂ : Val}
    (h₁ : Lookup σ (.path p) (.val v₁))
    (h₂ : Lookup σ (.path p) (.val v₂)) : v₁ = v₂ := by
  have h := finseqUnique
    (R := LookupStep σ) (a := DefRhs.path p)
    (functional := fun _ _ _ => lookup_step_functional)
    h₁ lookup_irred h₂ lookup_irred
  exact DefRhs.val.inj h

end CDot
