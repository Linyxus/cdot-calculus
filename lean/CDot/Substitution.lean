import CDot.InvertibleSubtyping

/-!
# Substitution infrastructure

Structural invariants needed by the typing substitution theorem.
-/

namespace CDot

variable [Signature]

mutual
  theorem Typ.tightBounds_subst (T : Typ) (h : T.tightBounds) (x : Var) (p : Path) :
      (T.subst x p).tightBounds := by
    cases T with
    | top | bot | path | all | sngl => trivial
    | rcd D => exact Dec.tightBounds_subst D h x p
    | and T U =>
        exact ⟨Typ.tightBounds_subst T h.1 x p,
          Typ.tightBounds_subst U h.2 x p⟩
    | bnd T => exact Typ.tightBounds_subst T h x p

  theorem Dec.tightBounds_subst (D : Dec) (h : D.tightBounds) (x : Var) (p : Path) :
      (D.subst x p).tightBounds := by
    cases D with
    | typ A T U =>
        simp only [Dec.tightBounds, Dec.subst] at h ⊢
        exact congrArg (fun V => V.subst x p) h
    | trm a T => exact Typ.tightBounds_subst T h x p
end

theorem UniqueMembership.subst {U T : Typ} {labels : Finset Label}
    (h : UniqueMembership U labels T) (x : Var) (p : Path) :
    UniqueMembership (U.subst x p) labels (T.subst x p) := by
  induction h with
  | typ => exact .typ
  | trm => exact .trm
  | bnd => exact .bnd
  | andLeft _ _ hd ih₁ ih₂ => exact .andLeft ih₁ ih₂ hd
  | andRight _ _ hd ih₁ ih₂ => exact .andRight ih₁ ih₂ hd

theorem Unique.subst {U T : Typ} (h : Unique U T) (x : Var) (p : Path) :
    Unique (U.subst x p) (T.subst x p) := by
  obtain ⟨labels, h⟩ := h
  exact ⟨labels, h.subst x p⟩

end CDot
