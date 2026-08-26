import CDot.Weakening

/-! # Subenvironments -/

namespace CDot

variable [Signature]

inductive Subenv : Ctx → Ctx → Prop where
  | empty : Subenv Env.empty Env.empty
  | push : Subenv G G' → Env.Ok (G.push x T) → Env.Ok (G'.push x T') →
      Subtyp G T T' → Subenv (G.push x T) (G'.push x T')

theorem Subenv.refl {G : Ctx} (h : Env.Ok G) : Subenv G G := by
  induction G with
  | nil => exact .empty
  | cons binding G ih =>
      rcases binding with ⟨x, T⟩
      have htail : Env.Ok G := by
        change List.Nodup (x :: G.map Prod.fst) at h
        exact h.tail
      exact .push (ih htail) h h (.refl)

theorem Subenv.extend {G₁ G₂ : Ctx} (h : Subenv G₁ G₂)
    (h₁ : Env.Ok (G₁.push x T)) (h₂ : Env.Ok (G₂.push x T)) :
    Subenv (G₁.push x T) (G₂.push x T) :=
  .push h h₁ h₂ .refl

theorem Subenv.last {G : Ctx} (h : Subtyp G S U)
    (hokS : Env.Ok (G.push x S)) (hokU : Env.Ok (G.push x U)) :
    Subenv (G.push x S) (G.push x U) :=
  .push (.refl (by
    change List.Nodup (x :: G.map Prod.fst) at hokS
    exact hokS.tail))
    hokS hokU h

theorem Subenv.ok {G₁ G₂ : Ctx} (h : Subenv G₁ G₂) : Env.Ok G₁ ∧ Env.Ok G₂ := by
  cases h with
  | empty => exact ⟨List.nodup_nil, List.nodup_nil⟩
  | push _ h₁ h₂ _ => exact ⟨h₁, h₂⟩

end CDot
