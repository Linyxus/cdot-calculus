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

theorem Env.fvFold_eq_union (G : Ctx) (s : Vars) :
    G.foldl (fun xs binding => xs ∪ binding.2.fv) s =
      s ∪ G.foldl (fun xs binding => xs ∪ binding.2.fv) ∅ := by
  induction G generalizing s with
  | nil => simp
  | cons binding G ih =>
      simp only [List.foldl_cons, Finset.empty_union]
      rw [ih (s ∪ binding.2.fv), ih binding.2.fv]
      simp only [Finset.union_assoc]

@[simp] theorem Ctx.fvTypes_push (G : Ctx) (x : Var) (T : Typ) :
    Ctx.fvTypes (G.push x T) = T.fv ∪ G.fvTypes := by
  unfold Ctx.fvTypes Env.fvValues Env.push
  simp only [List.foldl_cons, Finset.empty_union]
  rw [Env.fvFold_eq_union]

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

structure SubstCtx (x : Var) (p : Path) (S : Typ) (E E' : Ctx) where
  headCtx : Ctx
  tailCtx : Ctx
  source_eq : E = Env.concat (headCtx.push x S) tailCtx
  target_eq : E' = Env.concat headCtx (Ctx.subst x p tailCtx)
  ok : Env.Ok E
  headFresh : x ∉ headCtx.fvTypes
  replacement : Typed E' (.path p) (S.subst x p)

theorem SubstCtx.targetOk {x : Var} {p : Path} {S : Typ} {E E' : Ctx}
    (h : SubstCtx x p S E E') : Env.Ok E' := by
  rw [h.target_eq]
  have hok := h.ok
  rw [h.source_eq] at hok
  exact hok.removeMiddleSubst

theorem SubstCtx.middle {x : Var} {p : Path} {S : Typ} {E E' : Ctx}
    (h : SubstCtx x p S E E') : Env.Binds x S E := by
  have hok := h.ok
  rw [h.source_eq] at hok
  have hm := Env.Binds.middle_of_ok hok
  exact h.source_eq.symm ▸ hm

theorem SubstCtx.ne_of_sourceFresh {x : Var} {p : Path} {S : Typ} {E E' : Ctx}
    (h : SubstCtx x p S E E') {y : Var} (hy : Env.Fresh y E) : y ≠ x := by
  exact (h.middle.ne_of_fresh hy).symm

def SubstCtx.push {x : Var} {p : Path} {S V : Typ} {E E' : Ctx}
    (h : SubstCtx x p S E E') (y : Var)
    (hy : Env.Fresh y E) (hy' : Env.Fresh y E') :
    SubstCtx x p S (E.push y V) (E'.push y (V.subst x p)) := by
  refine
    { headCtx := h.headCtx
      tailCtx := h.tailCtx.push y V
      source_eq := ?_
      target_eq := ?_
      ok := Env.okPush h.ok hy
      headFresh := h.headFresh
      replacement := h.replacement.mono (.pushRight hy' _) }
  · simpa only [Env.push, Env.concat, List.cons_append] using
      congrArg (fun G => G.push y V) h.source_eq
  · simpa only [Env.push, Env.concat, Ctx.subst, List.map_cons,
      List.cons_append] using
      congrArg (fun G => G.push y (V.subst x p)) h.target_eq

theorem SubstCtx.targetFresh {x y : Var} {p : Path} {S : Typ} {E E' : Ctx}
    (h : SubstCtx x p S E E') (hy : Env.Fresh y E) : Env.Fresh y E' := by
  intro hy'
  rw [h.target_eq] at hy'
  rw [h.source_eq] at hy
  exact hy (Env.removeMiddleSubst_dom_subset hy')

theorem Typ.subst_open (T : Typ) {x y : Var} {p : Path}
    (hp : p.Named) (hyx : y ≠ x) :
    (T.open y).subst x p = (T.subst x p).open y := by
  simpa [Var.substPath, hyx] using T.subst_openRec p hp x y 0

theorem Trm.subst_open (t : Trm) {x y : Var} {p : Path}
    (hp : p.Named) (hyx : y ≠ x) :
    (t.open y).subst x p = (t.subst x p).open y := by
  simpa [Var.substPath, hyx] using t.subst_openRec p hp x y 0

theorem Defs.subst_open (ds : Defs) {x y : Var} {p : Path}
    (hp : p.Named) (hyx : y ≠ x) :
    (ds.open y).subst x p = (ds.subst x p).open y := by
  simpa [Var.substPath, hyx] using ds.subst_openRec p hp x y 0

theorem Path.selfFreshSubst (q : Path) {x y : Var} (hxy : x ≠ y) :
    x ∉ (q.subst x (.var y)).fv := by
  cases q with
  | select a fields =>
      cases a with
      | bound n =>
          change x ∉ (Path.select (.bound n) fields).fv
          simp [Path.fv, AVar.fv]
      | free z =>
          by_cases hzx : z = x
          · subst z
            simp [Path.subst, AVar.subst, Var.substPath, Path.var,
              Path.selectFields, Path.fv, AVar.fv, hxy]
          · have hxq : x ∉ (Path.select (.free z) fields).fv := by
              simp only [Path.fv, AVar.fv, Finset.mem_singleton]
              exact fun hxz => hzx hxz.symm
            rw [Path.subst_eq_self_of_not_mem hxq]
            exact hxq

mutual
  theorem Typ.selfFreshSubst (T : Typ) {x y : Var} (hxy : x ≠ y) :
      x ∉ (T.subst x (.var y)).fv := by
    cases T with
    | top | bot => simp [Typ.subst, Typ.fv]
    | rcd D => exact Dec.selfFreshSubst D hxy
    | and T U | all T U =>
        simp only [Typ.subst, Typ.fv, Finset.mem_union, not_or]
        exact ⟨Typ.selfFreshSubst T hxy, Typ.selfFreshSubst U hxy⟩
    | path q A | sngl q =>
        simpa only [Typ.subst, Typ.fv] using Path.selfFreshSubst q hxy
    | bnd T => exact Typ.selfFreshSubst T hxy

  theorem Dec.selfFreshSubst (D : Dec) {x y : Var} (hxy : x ≠ y) :
      x ∉ (D.subst x (.var y)).fv := by
    cases D with
    | typ A T U =>
        simp only [Dec.subst, Dec.fv, Finset.mem_union, not_or]
        exact ⟨Typ.selfFreshSubst T hxy, Typ.selfFreshSubst U hxy⟩
    | trm a T => exact Typ.selfFreshSubst T hxy
end

@[simp] theorem Path.subst_selectField (q : Path) (a : Signature.TrmLabel)
    (x : Var) (p : Path) :
    (q.selectField a).subst x p = (q.subst x p).selectField a := by
  simpa only [Path.selectFields_cons, Path.selectFields_nil] using
    Path.subst_selectFields q [a] x p

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


private theorem Typed.substMiddleRec {E : Ctx} {t : Trm} {T : Typ}
    (h : Typed E t T) {x : Var} {p : Path} {S : Typ} {E' : Ctx}
    (sc : SubstCtx x p S E E') :
    Typed E' (t.subst x p) (T.subst x p) := by
  revert x p S E' sc
  apply Typed.rec
    (motive_1 := fun G t T _ => ∀ {x p S G'}, SubstCtx x p S G G' →
      Typed G' (t.subst x p) (T.subst x p))
    (motive_2 := fun z fs G d D _ => ∀ {x p S G'}, SubstCtx x p S G G' →
      z ≠ x → TypedDef z fs G' (d.subst x p) (D.subst x p))
    (motive_3 := fun z fs G ds T _ => ∀ {x p S G'}, SubstCtx x p S G G' →
      z ≠ x → TypedDefs z fs G' (ds.subst x p) (T.subst x p))
    (motive_4 := fun G T U _ => ∀ {x p S G'}, SubstCtx x p S G G' →
      Subtyp G' (T.subst x p) (U.subst x p))
  case var =>
    intro y T G hb x p S G' sc
    by_cases hyx : y = x
    · subst y
      have hTS : T = S := hb.functional sc.middle
      subst T
      simpa [Trm.var, Trm.subst, Path.var, Path.subst, AVar.subst,
        Var.substPath] using sc.replacement
    · have hb₀ : Env.Binds y T (Env.concat (sc.headCtx.push x S) sc.tailCtx) :=
        sc.source_eq ▸ hb
      have hb' := hb₀.removeMiddleSubst hyx sc.headFresh (p := p)
      rw [← sc.target_eq] at hb'
      simpa [Trm.var, Trm.subst, Path.var, Path.subst, AVar.subst,
        Var.substPath, hyx] using Typed.var hb'
  case allIntro =>
    intro G T t U L hbody ih x p S G' sc
    have hp := sc.replacement.pathNamed
    refine .allIntro ((L ∪ G.dom) ∪ G'.dom) ?_
    intro y hy
    have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _
      (Finset.mem_union_left _ h))
    have hyG : Env.Fresh y G := fun h => hy (Finset.mem_union_left _
      (Finset.mem_union_right _ h))
    have hyG' : Env.Fresh y G' := fun h => hy (Finset.mem_union_right _ h)
    have hyx := sc.ne_of_sourceFresh hyG
    simpa only [Trm.subst, Typ.subst, Trm.subst_open _ hp hyx,
      Typ.subst_open _ hp hyx] using ih y hyL (sc.push y hyG hyG')
  case allElim =>
    intro G q S₀ U r hq hr ihq ihr x p S G' sc
    have hp := sc.replacement.pathNamed
    simpa only [Trm.subst, Typ.subst,
      Typ.subst_openRecPath p hp x r U 0] using
      Typed.allElim (ihq sc) (ihr sc)
  case newIntro =>
    intro q A G T ds L hdefs hself ihdefs ihself x p S G' sc
    have hp := sc.replacement.pathNamed
    refine .newIntro ((L ∪ G.dom) ∪ G'.dom) ?_ ?_
    · intro y hy
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _
        (Finset.mem_union_left _ h))
      have hyG : Env.Fresh y G := fun h => hy (Finset.mem_union_left _
        (Finset.mem_union_right _ h))
      have hyG' : Env.Fresh y G' := fun h => hy (Finset.mem_union_right _ h)
      have hyx := sc.ne_of_sourceFresh hyG
      simpa only [Typ.subst, Trm.subst, Val.subst,
        Defs.subst_open _ hp hyx, Typ.subst_open _ hp hyx] using
        ihdefs y hyL (sc.push y hyG hyG') hyx
    · intro y hy
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _
        (Finset.mem_union_left _ h))
      have hyG : Env.Fresh y G := fun h => hy (Finset.mem_union_left _
        (Finset.mem_union_right _ h))
      have hyG' : Env.Fresh y G' := fun h => hy (Finset.mem_union_right _ h)
      have hyx := sc.ne_of_sourceFresh hyG
      have hi := ihself y hyL (sc.push y hyG hyG')
      rw [Typ.subst_open T hp hyx, Typ.subst_open (.path q A) hp hyx] at hi
      simpa [Trm.subst, Typ.subst, Path.subst_openRec p 0 x _ _ hp, Path.var,
        Path.subst, AVar.subst, Var.substPath, hyx] using hi
  case newElim =>
    intro G q a T h ih x p S G' sc
    simpa only [Trm.subst, Typ.subst, Dec.subst,
      Path.subst_selectField] using Typed.newElim (ih sc)
  case rcdIntro =>
    intro G T q a h ih x p S G' sc
    simpa [Trm.subst, Typ.subst, Dec.subst] using Typed.rcdIntro (ih sc)
  case letE =>
    intro G t T U u L ht hbody iht ihbody x p S G' sc
    have hp := sc.replacement.pathNamed
    refine .letE ((L ∪ G.dom) ∪ G'.dom) (iht sc) ?_
    intro y hy
    have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _
      (Finset.mem_union_left _ h))
    have hyG : Env.Fresh y G := fun h => hy (Finset.mem_union_left _
      (Finset.mem_union_right _ h))
    have hyG' : Env.Fresh y G' := fun h => hy (Finset.mem_union_right _ h)
    have hyx := sc.ne_of_sourceFresh hyG
    simpa only [Trm.subst, Typ.subst, Trm.subst_open _ hp hyx] using
      ihbody y hyL (sc.push y hyG hyG')
  case caseE =>
    intro G q S₀ r U A T t₂ t₁ L hq hr hbody helse ihq ihr ihbody ihelse
      x p S G' sc
    have hp := sc.replacement.pathNamed
    refine .caseE ((L ∪ G.dom) ∪ G'.dom) (ihq sc) (ihr sc) ?_ (ihelse sc)
    intro y hy
    have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _
      (Finset.mem_union_left _ h))
    have hyG : Env.Fresh y G := fun h => hy (Finset.mem_union_left _
      (Finset.mem_union_right _ h))
    have hyG' : Env.Fresh y G' := fun h => hy (Finset.mem_union_right _ h)
    have hyx := sc.ne_of_sourceFresh hyG
    simpa only [Trm.subst, Typ.subst, Trm.subst_open _ hp hyx] using
      ihbody y hyL (sc.push y hyG hyG')
  case sngl =>
    intro G q r T hq hr ihq ihr x p S G' sc
    exact .sngl (ihq sc) (ihr sc)
  case self =>
    intro G q T h ih x p S G' sc
    simpa only [Trm.subst, Typ.subst] using Typed.self (ih sc)
  case pathElim =>
    intro G q r a T hq hr ihq ihr x p S G' sc
    simpa only [Trm.subst, Typ.subst,
      Path.subst_selectField] using Typed.pathElim (ihq sc) (ihr sc)
  case recIntro =>
    intro G q T h ih x p S G' sc
    have hp := sc.replacement.pathNamed
    have hi := ih sc
    rw [Typ.subst_openRecPath p hp x q T 0] at hi
    simpa only [Trm.subst, Typ.subst] using Typed.recIntro hi
  case recElim =>
    intro G q T h ih x p S G' sc
    have hp := sc.replacement.pathNamed
    rw [Typ.subst_openRecPath p hp x q T 0]
    simpa only [Trm.subst, Typ.subst] using Typed.recElim (ih sc)
  case andIntro =>
    intro G q T U hT hU ihT ihU x p S G' sc
    exact .andIntro (ihT sc) (ihU sc)
  case sub =>
    intro G t T U ht hs iht ihs x p S G' sc
    exact .sub (iht sc) (ihs sc)
  case typ => intros; exact .typ
  case all =>
    intro G T t U V z fs b h ih x p S G' sc hzx
    simpa only [Def.subst, Dec.subst, DefRhs.subst, Val.subst, Typ.subst] using
      TypedDef.all (ih sc)
  case new =>
    intro z fs T b G q A ds r hr ht hdefs htag ihdefs iht x p S G' sc hzx
    have hp := sc.replacement.pathNamed
    refine TypedDef.new (r.subst x p) ?_ ?_ ?_ ?_
    · simpa [hr, Path.subst, AVar.subst, Var.substPath, hzx,
        Path.var, Path.selectFields]
    · simpa only [Typ.subst] using Typ.tightBounds_subst (.bnd T) ht x p
    · simpa only [Def.subst, Dec.subst, DefRhs.subst, Val.subst,
        Defs.subst_openRecPath p hp x _ _ _, Typ.subst_openRecPath p hp x _ _ _,
        Path.subst_selectField] using ihdefs sc hzx
    · simpa only [Def.subst, Dec.subst, DefRhs.subst, Val.subst, Trm.subst,
        Typ.subst,
        Path.subst_selectField,
        Typ.subst_openRecPath p hp x _ _ _] using
        iht sc
  case path =>
    intro G q T z fs b h ih x p S G' sc hzx
    simpa only [Def.subst, Dec.subst, DefRhs.subst, Typ.subst] using
      TypedDef.path (ih sc)
  case one =>
    intro z fs G d D h ih x p S G' sc hzx
    simpa only [Defs.subst, Typ.subst] using TypedDefs.one (ih sc hzx)
  case cons =>
    intro z fs G ds T d D hds hd hn ihds ihd x p S G' sc hzx
    simpa only [Defs.subst, Typ.subst, Dec.subst] using
      TypedDefs.cons (ihds sc hzx) (ihd sc hzx) (Defs.hasnt_subst_label hn)
  case top => intros; exact .top
  case bot => intros; exact .bot
  case refl => intros; exact .refl
  case trans =>
    intro G R T U h₁ h₂ ih₁ ih₂ x p S G' sc
    exact .trans (ih₁ sc) (ih₂ sc)
  case andLeft => intros; exact .andLeft
  case andRight => intros; exact .andRight
  case andIntro =>
    intro G R T U h₁ h₂ ih₁ ih₂ x p S G' sc
    exact .andIntro (ih₁ sc) (ih₂ sc)
  case fld =>
    intro G T U a h ih x p S G' sc
    exact .fld (ih sc)
  case fldInv =>
    intro G U a T₂ T₁ h hu ih x p S G' sc
    exact .fldInv (ih sc) (Unique.subst hu x p)
  case typ =>
    intro G S₂ S₁ T₁ T₂ A h₁ h₂ ih₁ ih₂ x p S G' sc
    exact .typ (ih₁ sc) (ih₂ sc)
  case typInvLo =>
    intro G U A S₂ T₂ S₁ T₁ h hu ih x p S G' sc
    exact .typInvLo (ih sc) (Unique.subst hu x p)
  case typInvHi =>
    intro G U A S₂ T₂ S₁ T₁ h hu ih x p S G' sc
    exact .typInvHi (ih sc) (Unique.subst hu x p)
  case allInv =>
    intro G S₁ T₁ S₂ T₂ h ih x p S G' sc
    exact .allInv (ih sc)
  case snglPQ =>
    intro G q r U T T' hq hr hrepl ihq ihr x p S G' sc
    exact .snglPQ (ihq sc) (ihr sc) (hrepl.subst x p)
  case snglQP =>
    intro G q r U T T' hq hr hrepl ihq ihr x p S G' sc
    exact .snglQP (ihq sc) (ihr sc) (hrepl.subst x p)
  case selLo =>
    intro G q A S₀ T h ih x p S G' sc
    exact .selLo (ih sc)
  case selHi =>
    intro G q A S₀ T h ih x p S G' sc
    exact .selHi (ih sc)
  case all =>
    intro G S₂ S₁ T₁ T₂ L hdom hbody ihdom ihbody x p S G' sc
    have hp := sc.replacement.pathNamed
    refine .all ((L ∪ G.dom) ∪ G'.dom) (ihdom sc) ?_
    intro y hy
    have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _
      (Finset.mem_union_left _ h))
    have hyG : Env.Fresh y G := fun h => hy (Finset.mem_union_left _
      (Finset.mem_union_right _ h))
    have hyG' : Env.Fresh y G' := fun h => hy (Finset.mem_union_right _ h)
    have hyx := sc.ne_of_sourceFresh hyG
    simpa only [Typ.subst, Typ.subst_open _ hp hyx] using
      ihbody y hyL (sc.push y hyG hyG')
  case t => exact h

theorem Typed.substMiddle {E : Ctx} {t : Trm} {T : Typ}
    (h : Typed E t T) {x : Var} {p : Path} {S : Typ} {E' : Ctx}
    (sc : SubstCtx x p S E E') :
    Typed E' (t.subst x p) (T.subst x p) :=
  h.substMiddleRec sc

theorem TypedDef.substMiddle {z : Var} {fields : Fields} {E : Ctx}
    {d : Def} {D : Dec} (h : TypedDef z fields E d D)
    {x : Var} {p : Path} {S : Typ} {E' : Ctx}
    (sc : SubstCtx x p S E E') (hzx : z ≠ x) :
    TypedDef z fields E' (d.subst x p) (D.subst x p) := by
  revert x p S E' sc
  apply TypedDef.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun z fs G d D _ => ∀ {x p S G'}, SubstCtx x p S G G' →
      z ≠ x → TypedDef z fs G' (d.subst x p) (D.subst x p))
    (motive_3 := fun z fs G ds T _ => ∀ {x p S G'}, SubstCtx x p S G G' →
      z ≠ x → TypedDefs z fs G' (ds.subst x p) (T.subst x p))
    (motive_4 := fun _ _ _ _ => True)
  case var => intros; trivial
  case allIntro => intros; trivial
  case allElim => intros; trivial
  case newIntro => intros; trivial
  case newElim => intros; trivial
  case rcdIntro => intros; trivial
  case letE => intros; trivial
  case caseE => intros; trivial
  case sngl => intros; trivial
  case self => intros; trivial
  case pathElim => intros; trivial
  case recIntro => intros; trivial
  case recElim => intros; trivial
  case andIntro => intros; trivial
  case sub => intros; trivial
  case typ => intros; exact .typ
  case all =>
    intro G T t U V z fs b ht ih x p S G' sc hzx
    simpa only [Def.subst, Dec.subst, DefRhs.subst, Val.subst, Typ.subst] using
      TypedDef.all (ht.substMiddle sc)
  case new =>
    intro z fs T b G q A ds r hr ht hdefs htag ihdefs iht x p S G' sc hzx
    have hp := sc.replacement.pathNamed
    refine TypedDef.new (r.subst x p) ?_ ?_ ?_ ?_
    · simpa [hr, Path.subst, AVar.subst, Var.substPath, hzx,
        Path.var, Path.selectFields]
    · simpa only [Typ.subst] using Typ.tightBounds_subst (.bnd T) ht x p
    · simpa only [Def.subst, Dec.subst, DefRhs.subst, Val.subst,
        Defs.subst_openRecPath p hp x _ _ _, Typ.subst_openRecPath p hp x _ _ _,
        Path.subst_selectField] using ihdefs sc hzx
    · simpa only [Def.subst, Dec.subst, DefRhs.subst, Val.subst, Trm.subst,
        Typ.subst, Path.subst_selectField,
        Typ.subst_openRecPath p hp x _ _ _] using htag.substMiddle sc
  case path =>
    intro G q T z fs b ht ih x p S G' sc hzx
    simpa only [Def.subst, Dec.subst, DefRhs.subst, Typ.subst] using
      TypedDef.path (ht.substMiddle sc)
  case one =>
    intro z fs G d D hd ih x p S G' sc hzx
    simpa only [Defs.subst, Typ.subst] using TypedDefs.one (ih sc hzx)
  case cons =>
    intro z fs G ds T d D hds hd hn ihds ihd x p S G' sc hzx
    simpa only [Defs.subst, Typ.subst, Dec.subst] using
      TypedDefs.cons (ihds sc hzx) (ihd sc hzx) (Defs.hasnt_subst_label hn)
  case top => intros; trivial
  case bot => intros; trivial
  case refl => intros; trivial
  case trans => intros; trivial
  case andLeft => intros; trivial
  case andRight => intros; trivial
  case andIntro => intros; trivial
  case fld => intros; trivial
  case fldInv => intros; trivial
  case typ => intros; trivial
  case typInvLo => intros; trivial
  case typInvHi => intros; trivial
  case allInv => intros; trivial
  case snglPQ => intros; trivial
  case snglQP => intros; trivial
  case selLo => intros; trivial
  case selHi => intros; trivial
  case all => intros; trivial
  case t => exact h

theorem TypedDefs.substMiddle {z : Var} {fields : Fields} {E : Ctx}
    {ds : Defs} {T : Typ} (h : TypedDefs z fields E ds T)
    {x : Var} {p : Path} {S : Typ} {E' : Ctx}
    (sc : SubstCtx x p S E E') (hzx : z ≠ x) :
    TypedDefs z fields E' (ds.subst x p) (T.subst x p) := by
  revert x p S E' sc
  apply TypedDefs.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ => True)
    (motive_3 := fun z fs G ds T _ => ∀ {x p S G'}, SubstCtx x p S G G' →
      z ≠ x → TypedDefs z fs G' (ds.subst x p) (T.subst x p))
    (motive_4 := fun _ _ _ _ => True)
  case one =>
    intro z fs G d D hd ih x p S G' sc hzx
    simpa only [Defs.subst, Typ.subst] using
      TypedDefs.one (hd.substMiddle sc hzx)
  case cons =>
    intro z fs G ds T d D hds hd hn ihds ihd x p S G' sc hzx
    simpa only [Defs.subst, Typ.subst, Dec.subst] using
      TypedDefs.cons (ihds sc hzx) (hd.substMiddle sc hzx)
        (Defs.hasnt_subst_label hn)
  case t => exact h
  all_goals intros; trivial

theorem Subtyp.substMiddle {E : Ctx} {T U : Typ} (h : Subtyp E T U)
    {x : Var} {p : Path} {S : Typ} {E' : Ctx}
    (sc : SubstCtx x p S E E') :
    Subtyp E' (T.subst x p) (U.subst x p) := by
  revert x p S E' sc
  apply Subtyp.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
    (motive_4 := fun G T U _ => ∀ {x p S G'}, SubstCtx x p S G G' →
      Subtyp G' (T.subst x p) (U.subst x p))
  case var => intros; trivial
  case allIntro => intros; trivial
  case allElim => intros; trivial
  case newIntro => intros; trivial
  case newElim => intros; trivial
  case rcdIntro => intros; trivial
  case letE => intros; trivial
  case caseE => intros; trivial
  case sngl => intros; trivial
  case self => intros; trivial
  case pathElim => intros; trivial
  case recIntro => intros; trivial
  case recElim => intros; trivial
  case andIntro => intros; trivial
  case sub => intros; trivial
  case typ => intros; trivial
  case all => intros; trivial
  case new => intros; trivial
  case path => intros; trivial
  case one => intros; trivial
  case cons => intros; trivial
  case top => intros; exact .top
  case bot => intros; exact .bot
  case refl => intros; exact .refl
  case trans =>
    intro G R T U h₁ h₂ ih₁ ih₂ x p S G' sc
    exact .trans (ih₁ sc) (ih₂ sc)
  case andLeft => intros; exact .andLeft
  case andRight => intros; exact .andRight
  case andIntro =>
    intro G R T U h₁ h₂ ih₁ ih₂ x p S G' sc
    exact .andIntro (ih₁ sc) (ih₂ sc)
  case fld =>
    intro G T U a h ih x p S G' sc
    exact .fld (ih sc)
  case fldInv =>
    intro G U a T₂ T₁ h hu ih x p S G' sc
    exact .fldInv (ih sc) (Unique.subst hu x p)
  case typ =>
    intro G S₂ S₁ T₁ T₂ A h₁ h₂ ih₁ ih₂ x p S G' sc
    exact .typ (ih₁ sc) (ih₂ sc)
  case typInvLo =>
    intro G U A S₂ T₂ S₁ T₁ h hu ih x p S G' sc
    exact .typInvLo (ih sc) (Unique.subst hu x p)
  case typInvHi =>
    intro G U A S₂ T₂ S₁ T₁ h hu ih x p S G' sc
    exact .typInvHi (ih sc) (Unique.subst hu x p)
  case allInv =>
    intro G S₁ T₁ S₂ T₂ h ih x p S G' sc
    exact .allInv (ih sc)
  case snglPQ =>
    intro G q r U T T' hq hr hrepl ihq ihr x p S G' sc
    exact .snglPQ (hq.substMiddle sc) (hr.substMiddle sc) (hrepl.subst x p)
  case snglQP =>
    intro G q r U T T' hq hr hrepl ihq ihr x p S G' sc
    exact .snglQP (hq.substMiddle sc) (hr.substMiddle sc) (hrepl.subst x p)
  case selLo =>
    intro G q A S₀ T h ih x p S G' sc
    exact .selLo (h.substMiddle sc)
  case selHi =>
    intro G q A S₀ T h ih x p S G' sc
    exact .selHi (h.substMiddle sc)
  case all =>
    intro G S₂ S₁ T₁ T₂ L hdom hbody ihdom ihbody x p S G' sc
    have hp := sc.replacement.pathNamed
    refine .all ((L ∪ G.dom) ∪ G'.dom) (ihdom sc) ?_
    intro y hy
    have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _
      (Finset.mem_union_left _ h))
    have hyG : Env.Fresh y G := fun h => hy (Finset.mem_union_left _
      (Finset.mem_union_right _ h))
    have hyG' : Env.Fresh y G' := fun h => hy (Finset.mem_union_right _ h)
    have hyx := sc.ne_of_sourceFresh hyG
    simpa only [Typ.subst, Typ.subst_open _ hp hyx] using
      ihbody y hyL (sc.push y hyG hyG')
  case t => exact h

theorem Typed.subst {G : Ctx} {x : Var} {S : Typ} {t : Trm} {T : Typ}
    {p : Path} (h : Typed (G.push x S) t T) (hok : Env.Ok (G.push x S))
    (hx : x ∉ G.fvTypes) (hp : Typed G (.path p) (S.subst x p)) :
    Typed G (t.subst x p) (T.subst x p) := by
  apply h.substMiddle
  exact
    { headCtx := G
      tailCtx := Env.empty
      source_eq := rfl
      target_eq := rfl
      ok := hok
      headFresh := hx
      replacement := hp }

theorem Subtyp.subst {G : Ctx} {x : Var} {S T U : Typ} {p : Path}
    (h : Subtyp (G.push x S) T U) (hok : Env.Ok (G.push x S))
    (hx : x ∉ G.fvTypes) (hp : Typed G (.path p) (S.subst x p)) :
    Subtyp G (T.subst x p) (U.subst x p) := by
  apply h.substMiddle
  exact
    { headCtx := G
      tailCtx := Env.empty
      source_eq := rfl
      target_eq := rfl
      ok := hok
      headFresh := hx
      replacement := hp }

theorem Typed.substOpenPath {G : Ctx} {z : Var} {T U : Typ} {t : Trm}
    {p : Path} (hok : Env.Ok G) (hzG : Env.Fresh z G)
    (hzTypes : z ∉ G.fvTypes ∪ U.fv ∪ T.fv ∪ t.fv)
    (hbody : Typed (G.push z U) (t.open z) (T.open z))
    (hp : Typed G (.path p) U) :
    Typed G (t.openPath p) (T.openPath p) := by
  have hzU : z ∉ U.fv := fun h => hzTypes (by simp [h])
  have hzT : z ∉ T.fv := fun h => hzTypes (by simp [h])
  have hzt : z ∉ t.fv := fun h => hzTypes (by simp [h])
  have hzCtx : z ∉ G.fvTypes := fun h => hzTypes (by simp [h])
  have hp' : Typed G (.path p) (U.subst z p) := by
    simpa only [Typ.subst_eq_self_of_not_mem U hzU] using hp
  have hs := hbody.subst (Env.okPush hok hzG) hzCtx hp'
  rw [Trm.openPath_eq_subst_open_of_fresh t hzt hp.pathNamed]
  rw [Typ.openPath_eq_subst_open_of_fresh T hzT hp.pathNamed]
  exact hs

theorem Typed.substFreshOpenPath {L : Vars} {G : Ctx} {T : Typ}
    {u : Trm} {U : Typ} {p : Path} (hok : Env.Ok G)
    (hbody : ∀ x, x ∉ L → Typed (G.push x T) (u.open x) U)
    (hp : Typed G (.path p) T) : Typed G (u.openPath p) U := by
  obtain ⟨y, hy⟩ := Finset.exists_nat_subset_range
    (L ∪ G.dom ∪ G.fvTypes ∪ T.fv ∪ U.fv ∪ u.fv)
  have hyn : y ∉ L ∪ G.dom ∪ G.fvTypes ∪ T.fv ∪ U.fv ∪ u.fv := by
    intro hmem
    exact (Nat.lt_irrefl y) (Finset.mem_range.mp (hy hmem))
  have hyL : y ∉ L := by aesop
  have hyG : Env.Fresh y G := by aesop
  have hyCtx : y ∉ G.fvTypes := by aesop
  have hyT : y ∉ T.fv := by aesop
  have hyU : y ∉ U.fv := by aesop
  have hyu : y ∉ u.fv := by aesop
  have hp' : Typed G (.path p) (T.subst y p) := by
    simpa only [Typ.subst_eq_self_of_not_mem T hyT] using hp
  have hs := (hbody y hyL).subst (Env.okPush hok hyG) hyCtx hp'
  rw [← Trm.openPath_eq_subst_open_of_fresh u hyu hp.pathNamed] at hs
  simpa only [Typ.subst_eq_self_of_not_mem U hyU] using hs

omit [Signature] in
theorem Env.Extends.concatSameSuffix {G G' H : Env α}
    (he : Env.Extends G G') : Env.Extends (Env.concat G H) (Env.concat G' H) := by
  induction H with
  | nil => exact he
  | cons binding H ih =>
      obtain ⟨y, V⟩ := binding
      exact ih.push y V

theorem Typed.renameMiddle {G₁ G₂ : Ctx} {z x : Var} {T U : Typ}
    {t : Trm} (h : Typed (Env.concat (G₁.push z T) G₂) t U)
    (hzG₁ : z ∉ G₁.fvTypes) (hxG₁ : Env.Fresh x G₁) (hzx : z ≠ x)
    (hok : Env.Ok
      (Env.concat ((G₁.push x (T.subst z (.var x))).push z T) G₂)) :
    Typed (Env.concat (G₁.push x (T.subst z (.var x)))
      (Ctx.subst z (.var x) G₂))
      (t.subst z (.var x)) (U.subst z (.var x)) := by
  let Tx := T.subst z (.var x)
  let source := Env.concat ((G₁.push x Tx).push z T) G₂
  let target := Env.concat (G₁.push x Tx) (Ctx.subst z (.var x) G₂)
  have he₀ : Env.Extends (G₁.push z T) ((G₁.push x Tx).push z T) :=
    (Env.Extends.pushRight hxG₁ Tx).push z T
  have hweak : Typed source t U := by
    exact h.mono he₀.concatSameSuffix
  have hzHead : z ∉ Ctx.fvTypes (G₁.push x Tx) := by
    rw [Ctx.fvTypes_push]
    simp only [Finset.mem_union, not_or]
    exact ⟨Typ.selfFreshSubst T hzx, hzG₁⟩
  have htargetOk : Env.Ok target := by
    exact Env.Ok.removeMiddleSubst (G₁ := G₁.push x Tx) (G₂ := G₂)
      (x := z) (S := T) (p := .var x) hok
  have hxbind : Env.Binds x Tx target := by
    apply Env.Binds.middle_of_ok (G₁ := G₁) (G₂ := Ctx.subst z (.var x) G₂)
    exact htargetOk
  apply hweak.substMiddle
  exact
    { headCtx := G₁.push x Tx
      tailCtx := G₂
      source_eq := rfl
      target_eq := rfl
      ok := hok
      headFresh := hzHead
      replacement := by
        simpa [target, Tx, Trm.var] using Typed.var hxbind }

theorem TypedDefs.renameSelf {G : Ctx} {z x : Var} {fields : Fields}
    {S T : Typ} {ds : Defs}
    (h : TypedDefs z fields (G.push z S) ds T)
    (hzG : z ∉ G.fvTypes) (hxG : Env.Fresh x G) (hzx : z ≠ x)
    (hok : Env.Ok ((G.push x (S.subst z (.var x))).push z S)) :
    TypedDefs x fields (G.push x (S.subst z (.var x)))
      (ds.subst z (.var x)) (T.subst z (.var x)) := by
  apply TypedDefs.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun z fs E d D _ => ∀ {G : Ctx} {S : Typ} {x : Var}, E = G.push z S →
      z ∉ Ctx.fvTypes G → Env.Fresh x G → z ≠ x →
      Env.Ok ((G.push x (S.subst z (.var x))).push z S) →
      TypedDef x fs (G.push x (S.subst z (.var x)))
        (d.subst z (.var x)) (D.subst z (.var x)))
    (motive_3 := fun z fs E ds T _ => ∀ {G : Ctx} {S : Typ} {x : Var}, E = G.push z S →
      z ∉ Ctx.fvTypes G → Env.Fresh x G → z ≠ x →
      Env.Ok ((G.push x (S.subst z (.var x))).push z S) →
      TypedDefs x fs (G.push x (S.subst z (.var x)))
        (ds.subst z (.var x)) (T.subst z (.var x)))
    (motive_4 := fun _ _ _ _ => True)
  case typ =>
    intros
    exact .typ
  case all =>
    intro E R t U V z fs b ht iht G S x heq hzG hxG hzx hok
    subst E
    have ht' := ht.renameMiddle (G₁ := G) (G₂ := Env.empty)
      hzG hxG hzx (by simpa [Env.concat, Env.empty] using hok)
    simpa [Env.concat, Env.empty, Ctx.subst, Def.subst, Dec.subst, DefRhs.subst,
      Val.subst, Typ.subst] using TypedDef.all ht'
  case new =>
    intro z fs R b E q A body p hp ht hdefs htag ihdefs ihtag
      G S x heq hzG hxG hzx hok
    subst E
    have hnamed : (Path.var x).Named := ⟨x, rfl⟩
    have htag' := htag.renameMiddle (G₁ := G) (G₂ := Env.empty)
      hzG hxG hzx (by simpa [Env.concat, Env.empty] using hok)
    refine TypedDef.new (p.subst z (.var x)) ?_ ?_ ?_ ?_
    · simpa [hp, Path.subst, AVar.subst, Var.substPath, hzx,
        Path.var, Path.selectFields]
    · simpa only [Typ.subst] using
        Typ.tightBounds_subst (.bnd R) ht z (.var x)
    · simpa only [Def.subst, Dec.subst, DefRhs.subst, Val.subst,
        Defs.subst_openRecPath (.var x) hnamed z _ _ _,
        Typ.subst_openRecPath (.var x) hnamed z _ _ _,
        Path.subst_selectField] using
          ihdefs rfl hzG hxG hzx hok
    · simpa [Env.concat, Env.empty, Ctx.subst, Def.subst, Dec.subst, DefRhs.subst,
        Val.subst, Trm.subst, Typ.subst, Typ.openPath, Path.subst_selectField,
        Typ.subst_openRecPath (.var x) hnamed z _ _ _] using htag'
  case path =>
    intro E q R z fs b ht iht G S x heq hzG hxG hzx hok
    subst E
    have ht' := ht.renameMiddle (G₁ := G) (G₂ := Env.empty)
      hzG hxG hzx (by simpa [Env.concat, Env.empty] using hok)
    simpa [Env.concat, Env.empty, Ctx.subst, Def.subst, Dec.subst, DefRhs.subst,
      Typ.subst] using TypedDef.path ht'
  case one =>
    intro z fs E d D hd ih G S x heq hzG hxG hzx hok
    simpa only [Defs.subst, Typ.subst] using
      TypedDefs.one (ih heq hzG hxG hzx hok)
  case cons =>
    intro z fs E rest R d D hrest hd hno ihrest ihd
      G S x heq hzG hxG hzx hok
    simpa only [Defs.subst, Typ.subst, Dec.subst] using
      TypedDefs.cons (ihrest heq hzG hxG hzx hok)
        (ihd heq hzG hxG hzx hok) (Defs.hasnt_subst_label hno)
  case t => exact h
  all_goals intros; trivial

end CDot
