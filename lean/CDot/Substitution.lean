import CDot.InvertibleSubtyping

/-!
# Substitution infrastructure

Structural invariants needed by the typing substitution theorem.
-/

namespace CDot

variable [Signature]

@[simp] theorem Ctx.subst_empty (x : Var) (p : Path) :
    Ctx.subst x p Env.empty = Env.empty := rfl

@[simp] theorem Ctx.subst_push (G : Ctx) (y : Var) (T : Typ)
    (x : Var) (p : Path) :
    Ctx.subst x p (G.push y T) = (Ctx.subst x p G).push y (T.subst x p) := rfl

@[simp] theorem Ctx.subst_concat (G H : Ctx) (x : Var) (p : Path) :
    Ctx.subst x p (Env.concat G H) =
      Env.concat (Ctx.subst x p G) (Ctx.subst x p H) := by
  simp [Ctx.subst, Env.concat, List.map_append]

theorem Env.Binds.subst {G : Ctx} {y : Var} {T : Typ}
    (h : Env.Binds y T G) (x : Var) (p : Path) :
    Env.Binds y (T.subst x p) (Ctx.subst x p G) := by
  induction h with
  | here => exact .here
  | there hne h ih => exact .there hne ih

theorem Env.Ok.subst {G : Ctx} (h : Env.Ok G) (x : Var) (p : Path) :
    Env.Ok (Ctx.subst x p G) := by
  simpa [Env.Ok, Ctx.subst, Function.comp_def] using h

theorem Env.fvFold_mono (G : Ctx) {s t : Vars} (hst : s ⊆ t) :
    G.foldl (fun xs binding => xs ∪ binding.2.fv) s ⊆
      G.foldl (fun xs binding => xs ∪ binding.2.fv) t := by
  induction G generalizing s t with
  | nil => exact hst
  | cons binding G ih =>
      apply ih
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact Finset.mem_union_left _ (hst hz)
      · exact Finset.mem_union_right _ hz

theorem Env.fvFold_contains (G : Ctx) (s : Vars) :
    s ⊆ G.foldl (fun xs binding => xs ∪ binding.2.fv) s := by
  induction G generalizing s with
  | nil => exact fun _ h => h
  | cons binding G ih =>
      exact fun _ h => ih _ (Finset.mem_union_left _ h)

theorem Env.Binds.fv_mem_ctx {G : Ctx} {y : Var} {T : Typ}
    (h : Env.Binds y T G) {x : Var} (hx : x ∈ T.fv) : x ∈ G.fvTypes := by
  induction h with
  | here =>
      simp only [Ctx.fvTypes, Env.fvValues, List.foldl_cons, Finset.empty_union]
      exact Env.fvFold_contains _ _ hx
  | there hne h ih =>
      simp only [Ctx.fvTypes, Env.fvValues, List.foldl_cons, Finset.empty_union]
      exact Env.fvFold_mono _ (Finset.empty_subset _) ih

theorem Env.Binds.removeMiddleSubst {G₁ G₂ : Ctx} {x y : Var}
    {S T : Typ} {p : Path} (hne : y ≠ x)
    (hfresh : x ∉ G₁.fvTypes)
    (h : Env.Binds y T (Env.concat (G₁.push x S) G₂)) :
    Env.Binds y (T.subst x p) (Env.concat G₁ (Ctx.subst x p G₂)) := by
  induction G₂ with
  | nil =>
      simp only [Env.concat, List.nil_append] at h ⊢
      cases h with
      | here => exact False.elim (hne rfl)
      | there _ h =>
          rw [Typ.subst_eq_self_of_not_mem T]
          · exact h
          · intro hx
            exact hfresh (h.fv_mem_ctx hx)
  | cons binding G₂ ih =>
      obtain ⟨z, U⟩ := binding
      simp only [Env.concat, List.cons_append, Ctx.subst, List.map_cons] at h ⊢
      cases h with
      | here => exact .here
      | there hyz h => exact .there hyz (ih h)

theorem Env.Binds.middle_of_ok {G₁ G₂ : Ctx} {x : Var} {S : Typ}
    (hok : Env.Ok (Env.concat (G₁.push x S) G₂)) :
    Env.Binds x S (Env.concat (G₁.push x S) G₂) := by
  induction G₂ with
  | nil => exact .here
  | cons binding G₂ ih =>
      obtain ⟨y, T⟩ := binding
      change List.Nodup (y :: (Env.concat (G₁.push x S) G₂).map Prod.fst) at hok
      have hnot := (List.nodup_cons.mp hok).1
      have htail := ih (List.nodup_cons.mp hok).2
      apply Env.Binds.there
      · intro hxy
        subst y
        apply hnot
        simpa only [Env.dom, List.mem_toFinset] using htail.mem_dom
      · exact htail

theorem Env.Binds.middle_type_eq {G₁ G₂ : Ctx} {x : Var} {S T : Typ}
    (hok : Env.Ok (Env.concat (G₁.push x S) G₂))
    (h : Env.Binds x T (Env.concat (G₁.push x S) G₂)) : T = S :=
  h.functional (Env.Binds.middle_of_ok hok)

theorem Env.removeMiddleSubst_dom_subset {G₁ G₂ : Ctx} {x : Var}
    {S : Typ} {p : Path} :
    (Env.concat G₁ (Ctx.subst x p G₂)).dom ⊆
      (Env.concat (G₁.push x S) G₂).dom := by
  intro y hy
  induction G₂ with
  | nil =>
      change y ∈ G₁.dom at hy
      change y ∈ (G₁.push x S).dom
      simp only [Env.push, Env.dom, List.map_cons, List.mem_toFinset, List.mem_cons]
      exact Or.inr (by simpa only [Env.dom, List.mem_toFinset] using hy)
  | cons binding G₂ ih =>
      obtain ⟨z, U⟩ := binding
      simp only [Env.concat, Ctx.subst, List.map_cons, List.cons_append,
        Env.dom, List.mem_toFinset, List.mem_cons] at hy ⊢
      rcases hy with rfl | hy
      · exact Or.inl rfl
      · apply Or.inr
        have hout := ih (by
          simpa [Env.dom, Env.concat, Ctx.subst, List.map_append] using hy)
        simp [Env.dom, Env.concat, Env.push, List.map_append] at hout ⊢
        rcases hout with rfl | hG₂ | hG₁
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl hG₂
        · exact Or.inr (Or.inr hG₁)

theorem Env.Ok.removeMiddleSubst {G₁ G₂ : Ctx} {x : Var}
    {S : Typ} {p : Path} (hok : Env.Ok (Env.concat (G₁.push x S) G₂)) :
    Env.Ok (Env.concat G₁ (Ctx.subst x p G₂)) := by
  induction G₂ with
  | nil =>
      change List.Nodup (x :: G₁.map Prod.fst) at hok
      exact (List.nodup_cons.mp hok).2
  | cons binding G₂ ih =>
      obtain ⟨y, U⟩ := binding
      change List.Nodup (y :: (Env.concat (G₁.push x S) G₂).map Prod.fst) at hok
      change List.Nodup (y :: (Env.concat G₁ (Ctx.subst x p G₂)).map Prod.fst)
      apply List.Nodup.cons
      · intro hy
        have hy' : y ∈ (Env.concat G₁ (Ctx.subst x p G₂)).dom := by
          simpa only [Env.dom, List.mem_toFinset] using hy
        have := Env.removeMiddleSubst_dom_subset (G₁ := G₁) (G₂ := G₂)
          (x := x) (S := S) (p := p) hy'
        exact (List.nodup_cons.mp hok).1 (by
          simpa only [Env.dom, List.mem_toFinset] using this)
      · exact ih (List.nodup_cons.mp hok).2

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
