import Mathlib.Tactic

/-!
# Transition sequences

Lean port of the relation operators used in `cdot/Sequences.v`.  Lean's
function space gives a convenient representation of infinite sequences.
-/

namespace CDot

universe u

variable {α : Type u} {R : α → α → Prop}

inductive Star (R : α → α → Prop) : α → α → Prop where
  | refl (a : α) : Star R a a
  | step : R a b → Star R b c → Star R a c

inductive Plus (R : α → α → Prop) : α → α → Prop where
  | left : R a b → Star R b c → Plus R a c

namespace Star

theorem one (h : R a b) : Star R a b := .step h (.refl b)

theorem trans (hab : Star R a b) (hbc : Star R b c) : Star R a c := by
  induction hab
  case refl => exact hbc
  case step h _ ih => exact .step h (ih hbc)

end Star

namespace Plus

theorem one (h : R a b) : Plus R a b := .left h (.refl b)

theorem star (h : Plus R a b) : Star R a b := by
  cases h with
  | left hr hs => exact .step hr hs

theorem starTrans (hab : Plus R a b) (hbc : Star R b c) : Plus R a c := by
  cases hab with
  | left hr hs => exact .left hr (hs.trans hbc)

theorem ofStarTrans (hab : Star R a b) (hbc : Plus R b c) : Plus R a c := by
  induction hab
  case refl => exact hbc
  case step hr _ ih => exact .left hr (ih hbc).star

theorem right (hab : Star R a b) (hbc : R b c) : Plus R a c :=
  ofStarTrans hab (one hbc)

end Plus

/-- An explicit infinite sequence beginning at `a`. -/
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ f : Nat → α, f 0 = a ∧ ∀ n, R (f n) (f (n + 1))

def AllSeqInf (R : α → α → Prop) (a : α) : Prop :=
  ∀ b, Star R a b → ∃ c, R b c

def Irred (R : α → α → Prop) (a : α) : Prop := ∀ b, ¬R a b

theorem cycleInfSeq (h : R a a) : InfSeq R a := by
  refine ⟨fun _ => a, rfl, ?_⟩
  intro n
  exact h

theorem infSeqCoinduction (X : α → Prop)
    (step : ∀ a, X a → ∃ b, R a b ∧ X b) {a : α} (ha : X a) :
    InfSeq R a := by
  classical
  let next : {x // X x} → {x // X x} := fun x =>
    ⟨(step x.1 x.2).choose, (step x.1 x.2).choose_spec.2⟩
  let states : Nat → {x // X x} := fun n =>
    Nat.rec ⟨a, ha⟩ (fun _ state => next state) n
  refine ⟨fun n => (states n).1, ?_, ?_⟩
  · change a = a
    rfl
  intro n
  change R (states n).1 (states (n + 1)).1
  simp only [states]
  exact (step (states n).1 (states n).2).choose_spec.1

theorem infSeqIfAllSeqInf (h : AllSeqInf R a) : InfSeq R a := by
  apply infSeqCoinduction (X := fun b => Star R a b)
  · intro b hab
    obtain ⟨c, hbc⟩ := h b hab
    exact ⟨c, hbc, hab.trans (.one hbc)⟩
  · exact .refl a

theorem infSeqOrFinseq (a : α) :
    InfSeq R a ∨ ∃ b, Star R a b ∧ Irred R b := by
  classical
  by_cases h : AllSeqInf R a
  · exact Or.inl (infSeqIfAllSeqInf h)
  · right
    unfold AllSeqInf at h
    push Not at h
    obtain ⟨b, hab, hstop⟩ := h
    exact ⟨b, hab, hstop⟩

theorem starStarInv (functional : ∀ a b c, R a b → R a c → b = c)
    (hab : Star R a b) (hac : Star R a c) : Star R b c ∨ Star R c b := by
  induction hab generalizing c
  case refl => exact Or.inl hac
  case step hab hbc ih =>
    cases hac with
    | refl => exact Or.inr (.step hab hbc)
    | step hac hac' =>
      have hEq := functional _ _ _ hab hac
      subst hEq
      exact ih hac'

theorem finseqUnique (functional : ∀ a b c, R a b → R a c → b = c)
    (hab : Star R a b) (hb : Irred R b)
    (hab' : Star R a b') (hb' : Irred R b') : b = b' := by
  rcases starStarInv functional hab hab' with h | h
  · cases h with
    | refl => rfl
    | step hr _ => exact False.elim (hb _ hr)
  · cases h with
    | refl => rfl
    | step hr _ => exact False.elim (hb' _ hr)

end CDot
