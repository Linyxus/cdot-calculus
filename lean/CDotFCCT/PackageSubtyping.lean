import CDotFCCT.Existentials

/-!
# Subtyping of continuation-encoded packages

The consumer's constraints are assumptions, including inconsistent ones. A package may
forget information when its original guards entail the new guards. In particular, bounded
members have contravariant lower bounds and covariant upper bounds.
-/

set_option autoImplicit false

namespace CDotFCCT

open FCCT FCCT.Syntax

theorem underGuards {subtyping : SubtypingContext}
    {sub sup : WFTy subtyping.typeDepth} (h : Subtype subtyping sub sup)
    (guards : List (WFConstraint subtyping.typeDepth)) :
    Subtype (assumeMany subtyping guards) sub sup :=
  h.mapAssumptions (fun guard membership =>
    @Subtype.hyp (assumeMany subtyping guards) guard
      (List.mem_append_right _ membership))

theorem qualifyLeft {subtyping : SubtypingContext}
    {guards : List (WFConstraint subtyping.typeDepth)} {body : WFTy subtyping.typeDepth}
    (evidence : Satisfies subtyping guards) :
    Subtype subtyping (qualify guards body) body := by
  induction guards with
  | nil => exact .refl
  | cons guard guards ih =>
      exact .trans (.constrainedLeft guard _ (evidence _ List.mem_cons_self))
        (ih (fun found membership => evidence found (List.mem_cons_of_mem _ membership)))

theorem qualifyRight {n : Nat} {assumptions : List (WFConstraint n)}
    {sub sup : WFTy n} (guards : List (WFConstraint n))
    (h : Subtype (assumeMany ⟨n, assumptions⟩ guards) sub sup) :
    Subtype ⟨n, assumptions⟩ sub (qualify guards sup) := by
  induction guards generalizing assumptions with
  | nil => exact h
  | cons guard guards ih =>
      refine .trans (@Subtype.constrainedRight ⟨n, assumptions⟩ guard sub)
        (@Subtype.constrainedCovariant ⟨n, assumptions⟩ guard sub (qualify guards sup)
          (ih (assumptions := guard :: assumptions) ?_))
      change Subtype ⟨n, (guard :: guards).reverse ++ assumptions⟩ sub sup at h
      rw [List.reverse_cons, List.append_assoc] at h
      exact h

/-- General package variance: a consumer may forget guards and widen its payload. -/
theorem existsCPSSubtype {subtyping : SubtypingContext}
    {sourceGuards targetGuards : List (WFConstraint (subtyping.typeDepth + 1))}
    {sourcePayload targetPayload : WFTy (subtyping.typeDepth + 1)}
    {answer : WFTy subtyping.typeDepth}
    (entails : Satisfies (assumeMany subtyping.bindType sourceGuards) targetGuards)
    (payload : Subtype (assumeMany subtyping.bindType sourceGuards)
      sourcePayload targetPayload) :
    Subtype subtyping (existsCPS sourceGuards sourcePayload answer)
      (existsCPS targetGuards targetPayload answer) :=
  .arrow (.forallCovariant _ _ (qualifyRight sourceGuards
    (.trans (qualifyLeft entails) (.arrow payload .refl)))) .refl

/-- FCCT's encoded member interface has exactly DOT's interval variance. -/
theorem boundedSubtype {subtyping : SubtypingContext}
    {lowerSource upperSource lowerTarget upperTarget : WFTy subtyping.typeDepth}
    {payload : WFTy (subtyping.typeDepth + 1)} {answer : WFTy subtyping.typeDepth}
    (lower : Subtype subtyping lowerTarget lowerSource)
    (upper : Subtype subtyping upperSource upperTarget) :
    Subtype subtyping (existsCPS (bounds lowerSource upperSource) payload answer)
      (existsCPS (bounds lowerTarget upperTarget) payload answer) := by
  refine existsCPSSubtype ?_ .refl
  change ∀ guard : WFConstraint (subtyping.typeDepth + 1),
    guard ∈ bounds lowerTarget upperTarget →
      Subtype (assumeMany subtyping.bindType (bounds lowerSource upperSource)) guard.sub guard.sup
  simp only [bounds, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨.trans (underGuards lower.weakenType (bounds lowerSource upperSource))
      (assumedGuard (subtyping := subtyping.bindType)
        (guards := bounds lowerSource upperSource) List.mem_cons_self),
    .trans (assumedGuard (subtyping := subtyping.bindType)
        (guard := WFConstraint.constr (WFTy.var 0 (Nat.zero_lt_succ _)) upperSource.weaken)
        (guards := bounds lowerSource upperSource) (List.mem_cons_of_mem _ List.mem_cons_self))
      (underGuards upper.weakenType (bounds lowerSource upperSource))⟩

end CDotFCCT
