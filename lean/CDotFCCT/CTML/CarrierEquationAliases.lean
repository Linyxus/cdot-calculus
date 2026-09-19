import CDotFCCT.CTML.CarrierEquationSyntax
import Mathlib.Data.Fintype.Card

/-!
# Eliminating direct aliases from finite carrier equations

Each equation is either a direct alias or a guarded pure carrier expression.
Bounded propagation finds the guarded endpoint of every terminating alias chain.
Components without such an endpoint receive one shared outer leaf. This includes
pure alias cycles and paths entering them, without accepting negative or constraint
cycles outside the guarded expression grammar.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierEquation

open CTMLCore CTMLCore.Syntax

variable {ghost : FieldName → Bool} {depth size : Nat}

instance Expr.decidableGuarded (expression : Expr ghost depth size) :
    Decidable expression.Guarded :=
  match expression with
  | .leaf _ => isTrue trivial
  | .ref _ => isFalse id
  | .neg body => body.decidableGuarded
  | .joint _ left right => @instDecidableAnd _ _ left.decidableGuarded right.decidableGuarded
  | .record _ _ _ => isTrue trivial

inductive AliasBody (ghost : FieldName → Bool) (depth size : Nat) where
  | alias : Fin size → AliasBody ghost depth size
  | guarded (expression : Expr ghost depth size) :
      expression.Guarded → AliasBody ghost depth size

def AliasBody.expression : AliasBody ghost depth size → Expr ghost depth size
  | .alias index => .ref index
  | .guarded expression _ => expression

/-- Checking introduces only evidence about the supplied expression's syntax. -/
def AliasBody.check (expression : Expr ghost depth size) :
    Option {body : AliasBody ghost depth size // body.expression = expression} :=
  match expression with
  | .ref index => some ⟨.alias index, rfl⟩
  | expression =>
      if guarded : expression.Guarded then some ⟨.guarded expression guarded, rfl⟩ else none

structure Aliases (ghost : FieldName → Bool) (depth size : Nat) where
  body : Fin size → AliasBody ghost depth size

namespace Aliases

/-- A finite raw block is accepted precisely when every body is guarded or a direct alias. -/
def check (body : Fin size → Expr ghost depth size) :
    Option {system : Aliases ghost depth size //
      ∀ index, (system.body index).expression = body index} :=
  if valid : ∀ index, (AliasBody.check (body index)).isSome then
    some ⟨⟨fun index => ((AliasBody.check (body index)).get (valid index)).val⟩,
      fun index => ((AliasBody.check (body index)).get (valid index)).property⟩
  else none

/-- One round propagates the index of a guarded endpoint across one alias. -/
def roots (system : Aliases ghost depth size) : Nat → Fin size → Option (Fin size)
  | 0, _ => none
  | fuel + 1, index =>
      match system.body index with
      | .alias next => roots system fuel next
      | .guarded _ _ => some index

private theorem roots_persistent (system : Aliases ghost depth size) (fuel : Nat)
    {index endpoint : Fin size} (found : system.roots fuel index = some endpoint) :
    system.roots (fuel + 1) index = some endpoint := by
  induction fuel generalizing index with
  | zero => cases found
  | succ fuel ih =>
      cases body : system.body index with
      | «alias» next =>
          simpa only [roots, body] using ih (by simpa only [roots, body] using found)
      | guarded expression guarded => simpa only [roots, body] using found

private def known (system : Aliases ghost depth size) (fuel : Nat) : Finset (Fin size) :=
  Finset.univ.filter (fun index => (system.roots fuel index).isSome)

private theorem known_mono (system : Aliases ghost depth size) (fuel : Nat) :
    system.known fuel ⊆ system.known (fuel + 1) := by
  intro index member
  obtain ⟨endpoint, found⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp member).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    Option.isSome_iff_exists.mpr ⟨endpoint, system.roots_persistent fuel found⟩⟩

private theorem roots_eq_of_known_eq (system : Aliases ghost depth size) (fuel : Nat)
    (equal : system.known fuel = system.known (fuel + 1)) :
    system.roots fuel = system.roots (fuel + 1) := by
  funext index
  cases before : system.roots fuel index with
  | some endpoint => exact (system.roots_persistent fuel before).symm
  | none =>
      have absent : index ∉ system.known fuel := by simp [known, before]
      rw [equal] at absent
      cases after : system.roots (fuel + 1) index <;> simp [known, after] at absent ⊢

private theorem roots_stay_equal (system : Aliases ghost depth size) (fuel : Nat)
    (equal : system.roots fuel = system.roots (fuel + 1)) :
    system.roots (fuel + 1) = system.roots (fuel + 2) := by
  funext index
  cases body : system.body index with
  | «alias» next => simpa only [roots, body] using congrFun equal next
  | guarded expression guarded => simp only [roots, body]

/-- Either propagation has stopped, or at least one new component was found each round. -/
private theorem stable_or_card (system : Aliases ghost depth size) (fuel : Nat) :
    system.roots fuel = system.roots (fuel + 1) ∨ fuel ≤ (system.known fuel).card := by
  induction fuel with
  | zero => exact .inr (Nat.zero_le _)
  | succ fuel ih =>
      rcases ih with stable | lower
      · exact .inl (system.roots_stay_equal fuel stable)
      · by_cases same : system.known fuel = system.known (fuel + 1)
        · exact .inl (system.roots_stay_equal fuel (system.roots_eq_of_known_eq fuel same))
        · have grows : (system.known fuel).card < (system.known (fuel + 1)).card :=
            Finset.card_lt_card ⟨system.known_mono fuel,
              fun reverse => same (Finset.Subset.antisymm (system.known_mono fuel) reverse)⟩
          exact .inr (Nat.lt_of_le_of_lt lower grows)

theorem roots_stable (system : Aliases ghost depth size) :
    system.roots (size + 1) = system.roots (size + 2) := by
  rcases system.stable_or_card (size + 1) with stable | lower
  · exact stable
  · have upper := (system.known (size + 1)).card_le_univ
    rw [Fintype.card_fin] at upper
    omega

private theorem roots_guarded (system : Aliases ghost depth size) (fuel : Nat)
    {index endpoint : Fin size} (found : system.roots fuel index = some endpoint) :
    (system.body endpoint).expression.Guarded := by
  induction fuel generalizing index with
  | zero => cases found
  | succ fuel ih =>
      cases body : system.body index with
      | «alias» next => exact ih (by simpa only [roots, body] using found)
      | guarded expression guarded =>
          have same : index = endpoint := by simpa only [roots, body, Option.some.injEq] using found
          subst endpoint
          simpa only [body, AliasBody.expression] using guarded

def normalizedBody (system : Aliases ghost depth size) (fallback : WFTy depth)
    (index : Fin size) : Expr ghost depth size :=
  match system.roots (size + 1) index with
  | none => .leaf fallback
  | some endpoint => (system.body endpoint).expression

theorem normalizedBody_guarded (system : Aliases ghost depth size) (fallback : WFTy depth)
    (index : Fin size) : (system.normalizedBody fallback index).Guarded := by
  cases found : system.roots (size + 1) index with
  | none => simp only [normalizedBody, found, Expr.Guarded]
  | some endpoint =>
      simpa only [normalizedBody, found] using system.roots_guarded (size + 1) found

/-- The block keeps its original indices; aliases share their endpoint's defining body. -/
def normalize (system : Aliases ghost depth size) (fallback : WFTy depth := WFTy.bottom) :
    System ghost depth size where
  body := system.normalizedBody fallback
  guarded := system.normalizedBody_guarded fallback

theorem normalize_alias (system : Aliases ghost depth size) (fallback : WFTy depth)
    {index next : Fin size} (body : system.body index = .alias next) :
    (system.normalize fallback).body index = (system.normalize fallback).body next := by
  have same : system.roots (size + 1) index = system.roots (size + 1) next :=
    (congrFun system.roots_stable index).trans (by simp only [roots, body])
  simp only [normalize, normalizedBody, same]

theorem normalize_guarded (system : Aliases ghost depth size) (fallback : WFTy depth)
    {index : Fin size} {expression : Expr ghost depth size} {guarded : expression.Guarded}
    (body : system.body index = .guarded expression guarded) :
    (system.normalize fallback).body index = expression := by
  simp only [normalize, normalizedBody, roots, body, AliasBody.expression]

/-- Any solution of the computed guarded block solves all original alias equations. -/
theorem normalize_sound (system : Aliases ghost depth size) (fallback : WFTy depth)
    {ValueType : Sort _} (values : Fin size → ValueType)
    (interpret : Expr ghost depth size → ValueType)
    (references : ∀ index, interpret (.ref index) = values index)
    (solution : ∀ index, values index = interpret ((system.normalize fallback).body index)) :
    ∀ index, values index = interpret (system.body index).expression := by
  intro index
  cases body : system.body index with
  | «alias» next =>
      exact (solution index).trans
        ((congrArg interpret (system.normalize_alias fallback body)).trans
          ((solution next).symm.trans (references next).symm))
  | guarded expression guarded =>
      simpa only [system.normalize_guarded fallback body, AliasBody.expression] using solution index

/-- The compiler-facing normalizer computes its guard evidence from the raw finite block. -/
def normalizeChecked (body : Fin size → Expr ghost depth size)
    (fallback : WFTy depth := WFTy.bottom) : Option (System ghost depth size) :=
  (check body).map (fun checked => checked.val.normalize fallback)

theorem normalizeChecked_sound {body : Fin size → Expr ghost depth size}
    {fallback : WFTy depth} {normalized : System ghost depth size}
    (accepted : normalizeChecked body fallback = some normalized)
    {ValueType : Sort _} (values : Fin size → ValueType)
    (interpret : Expr ghost depth size → ValueType)
    (references : ∀ index, interpret (.ref index) = values index)
    (solution : ∀ index, values index = interpret (normalized.body index)) :
    ∀ index, values index = interpret (body index) := by
  cases checked : check body with
  | none => simp only [normalizeChecked, checked, Option.map_none] at accepted; contradiction
  | some checkedBody =>
      have same : checkedBody.val.normalize fallback = normalized :=
        Option.some.inj (by simpa only [normalizeChecked, checked, Option.map_some] using accepted)
      subst normalized
      intro index
      rw [← checkedBody.property index]
      exact checkedBody.val.normalize_sound fallback values interpret references solution index

private theorem roots_none_of_closedAliases (system : Aliases ghost depth size)
    (nodes : Finset (Fin size))
    (closed : ∀ index ∈ nodes, ∃ next ∈ nodes, system.body index = .alias next)
    (fuel : Nat) {index : Fin size} (present : index ∈ nodes) :
    system.roots fuel index = none := by
  induction fuel generalizing index with
  | zero => rfl
  | succ fuel ih =>
      obtain ⟨next, present, body⟩ := closed index present
      simpa only [roots, body] using ih present

/-- Closed alias cycles and paths into them use the selected outer leaf. -/
theorem normalize_closedAliases (system : Aliases ghost depth size) (fallback : WFTy depth)
    (nodes : Finset (Fin size))
    (closed : ∀ index ∈ nodes, ∃ next ∈ nodes, system.body index = .alias next)
    {index : Fin size} (present : index ∈ nodes) :
    (system.normalize fallback).body index = .leaf fallback := by
  simp only [normalize, normalizedBody, system.roots_none_of_closedAliases nodes closed _ present]

/-- Any finite system consisting entirely of direct aliases admits one shared chosen leaf. -/
theorem normalize_pure (next : Fin size → Fin size) (fallback : WFTy depth) (index : Fin size) :
    ((⟨fun index => .alias (next index)⟩ : Aliases ghost depth size).normalize fallback).body
      index = .leaf fallback :=
  normalize_closedAliases _ fallback Finset.univ
    (fun index _ => ⟨next index, Finset.mem_univ _, rfl⟩) (Finset.mem_univ _)

end Aliases

namespace AliasExamples

/-- A two-link alias chain reaches a guarded recursive equation; another component loops. -/
def bodies (index : Fin 4) : Expr (fun _ => true) 0 4 :=
  if index = 0 then .ref 1
  else if index = 1 then .ref 2
  else if index = 2 then .record "m" rfl (.ref 0)
  else .ref 3

def checked : {system : Aliases (fun _ => true) 0 4 //
    ∀ index, (system.body index).expression = bodies index} :=
  (Aliases.check bodies).get (by decide +kernel)

def normalized : System (fun _ => true) 0 4 := checked.val.normalize

theorem chainReachesGuard : normalized.body 0 = .record "m" rfl (.ref 0) := by
  rfl

theorem selfAliasUsesBottom : normalized.body 3 = .leaf WFTy.bottom := by
  rfl

theorem rejectsNegativeSelf :
    Aliases.normalizeChecked (fun _ : Fin 1 =>
      (.neg (.ref 0) : Expr (fun _ => true) 0 1)) = none := by
  rfl

end AliasExamples

end CDotFCCT.CTML.Mixed.CarrierEquation
