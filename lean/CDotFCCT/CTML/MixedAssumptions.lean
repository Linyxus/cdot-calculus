import CDotFCCT.CTML.MixedTermWeakening
import CTMLCore.Declarative.Discharge

/-!
# Constraint transport for the mixed target

As in native CTML, `mapAssumptions` replaces each context assumption by a native
subtyping derivation in the target context. The transported typing may use ghost
inversion and any recursive scope. In particular, inserting fresh constraints
preserves arbitrary mixed payload derivations, not just native payload typings.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

variable {ghost : FieldName → Bool}

theorem InvertingSubtype.mapAssumptions {s : SubtypingContext}
    {sub sup : WFTy s.typeDepth} (h : InvertingSubtype ghost s sub sup)
    {target : List (WFConstraint s.typeDepth)}
    (resolve : ∀ constraint, constraint ∈ s.assumptions →
      Subtype ⟨s.typeDepth, target⟩ constraint.sub constraint.sup) :
    InvertingSubtype ghost ⟨s.typeDepth, target⟩ sub sup := by
  induction h with
  | native h => exact .native (h.mapAssumptions resolve)
  | nativeWith guards h evidence ih =>
      exact .nativeWith guards h (fun guard member => ih guard member resolve)
  | trans _ _ first second => exact .trans (first resolve) (second resolve)
  | inverse marked _ ih => exact .inverse marked (ih resolve)
  | rowInverse reflective member _ ih => exact .rowInverse reflective member (ih resolve)
  | cut guard _ _ inferred body =>
      refine .cut (s := ⟨_, target⟩) guard (inferred resolve) ?_
      refine body (target := guard :: target) ?_
      intro found membership
      rcases List.mem_cons.mp membership with equal | previous
      · subst found
        exact @Subtype.hyp ⟨_, guard :: target⟩ guard List.mem_cons_self
      · exact (resolve found previous).weakenAssumption guard
  | forallCovariant _ ih =>
      refine .forallCovariant ?_
      refine ih (target := target.map WFConstraint.weaken) ?_
      intro constraint membership
      obtain ⟨old, member, rfl⟩ := List.mem_map.mp membership
      simpa only [SubtypingContext.bindType, WFConstraint.weaken_sub,
        WFConstraint.weaken_sup] using
        (resolve old member).weakenType
  | constrainedCovariant guard _ ih =>
      refine .constrainedCovariant (s := ⟨_, target⟩) guard ?_
      refine ih (target := guard :: target) ?_
      intro found membership
      rcases List.mem_cons.mp membership with equal | previous
      · subst found
        exact @Subtype.hyp ⟨_, guard :: target⟩ guard List.mem_cons_self
      · exact (resolve found previous).weakenAssumption guard

theorem InvertingSubtype.weakenAssumption {s : SubtypingContext}
    {sub sup : WFTy s.typeDepth} (h : InvertingSubtype ghost s sub sup)
    (guard : WFConstraint s.typeDepth) : InvertingSubtype ghost (s.assume guard) sub sup :=
  h.mapAssumptions (target := guard :: s.assumptions) fun found member =>
    @Subtype.hyp (s.assume guard) found (List.mem_cons_of_mem guard member)

mutual
  /-- Replace every assumption by a proof, preserving local recursive declarations. -/
  theorem HasType.mapAssumptions {s : SubtypingContext} {context : TypingContext s.typeDepth}
      {term : Term} {type : WFTy s.typeDepth} (h : HasType ghost s context term type)
      {target : List (WFConstraint s.typeDepth)}
      (resolve : ∀ constraint, constraint ∈ s.assumptions →
        Subtype ⟨s.typeDepth, target⟩ constraint.sub constraint.sup) :
      HasType ghost ⟨s.typeDepth, target⟩ context term type :=
    match h with
    | .native h => .native (h.mapAssumptions resolve)
    | .subsumption h sub => .subsumption (h.mapAssumptions resolve) (sub.mapAssumptions resolve)
    | .abstraction h => .abstraction (h.mapAssumptions resolve)
    | .application function argument =>
        .application (function.mapAssumptions resolve) (argument.mapAssumptions resolve)
    | .record fields => .record (fields.mapAssumptions resolve)
    | .projection record => .projection (record.mapAssumptions resolve)
    | .ascription h sub => .ascription (h.mapAssumptions resolve) (sub.mapAssumptions resolve)
    | .forall context term body nonexpansive h => by
        refine @HasType.forall ghost ⟨s.typeDepth, target⟩ context term body nonexpansive ?_
        refine h.mapAssumptions (target := target.map WFConstraint.weaken) ?_
        intro constraint membership
        simp only [SubtypingContext.bindType] at membership ⊢
        rcases List.mem_map.mp membership with ⟨old, oldMembership, equal⟩
        subst equal
        simpa only [SubtypingContext.bindType, WFConstraint.weaken_sub, WFConstraint.weaken_sup]
          using (resolve old oldMembership).weakenType
    | .constrained guard body context term nonexpansive h => by
        refine @HasType.constrained ghost ⟨s.typeDepth, target⟩ guard body context term
          nonexpansive ?_
        refine h.mapAssumptions (target := guard :: target) ?_
        intro found membership
        rcases List.mem_cons.mp membership with equal | oldMembership
        · subst found
          exact @Subtype.hyp ⟨s.typeDepth, guard :: target⟩ guard List.mem_cons_self
        · exact (resolve found oldMembership).weakenAssumption guard
    | .intersection left right =>
        .intersection (left.mapAssumptions resolve) (right.mapAssumptions resolve)
    | .ifThen scrutinee sub branch =>
        .ifThen (scrutinee.mapAssumptions resolve) (sub.mapAssumptions resolve)
          (branch.mapAssumptions resolve)
    | .ifElse scrutinee sub branch =>
        .ifElse (scrutinee.mapAssumptions resolve) (sub.mapAssumptions resolve)
          (branch.mapAssumptions resolve)
    | .fixpoint function => .fixpoint (function.mapAssumptions resolve)
    | .recursiveSystem (size := size) system h => by
        refine .recursiveSystem system ?_
        refine h.mapAssumptions
          (target := (system.openContext ⟨s.typeDepth, target⟩).assumptions) ?_
        intro found membership
        rcases List.mem_append.mp membership with equation | outer
        · exact @Subtype.hyp (system.openContext ⟨s.typeDepth, target⟩) found
            (List.mem_append_left _ equation)
        · obtain ⟨old, member, rfl⟩ := List.mem_map.mp outer
          have weakened := (resolve old member).weakenTypes size
          have lifted := weakened.mapAssumptions
            (target := (system.openContext ⟨s.typeDepth, target⟩).assumptions)
            (fun guard member =>
              @Subtype.hyp (system.openContext ⟨s.typeDepth, target⟩) guard
                (List.mem_append_right _ member))
          set_option backward.isDefEq.respectTransparency false in
            simp only [WFConstraint.weakenBy_sub, WFConstraint.weakenBy_sup]
          exact lifted
    | .recursiveRecordSystem (size := size) system ordinary h => by
        refine .recursiveRecordSystem system ordinary ?_
        refine h.mapAssumptions
          (target := (system.openContext ⟨s.typeDepth, target⟩).assumptions) ?_
        intro found membership
        rcases List.mem_append.mp membership with equation | outer
        · exact @Subtype.hyp (system.openContext ⟨s.typeDepth, target⟩) found
            (List.mem_append_left _ equation)
        · obtain ⟨old, member, rfl⟩ := List.mem_map.mp outer
          have weakened := (resolve old member).weakenTypes size
          have lifted := weakened.mapAssumptions
            (target := (system.openContext ⟨s.typeDepth, target⟩).assumptions)
            (fun guard member =>
              @Subtype.hyp (system.openContext ⟨s.typeDepth, target⟩) guard
                (List.mem_append_right _ member))
          set_option backward.isDefEq.respectTransparency false in
            simp only [WFConstraint.weakenBy_sub, WFConstraint.weakenBy_sup]
          exact lifted
    | .recursiveCarrierSystem (size := size) system h => by
        refine .recursiveCarrierSystem system ?_
        refine h.mapAssumptions
          (target := (system.openContext ⟨s.typeDepth, target⟩).assumptions) ?_
        intro found membership
        rcases List.mem_append.mp membership with equation | outer
        · exact @Subtype.hyp (system.openContext ⟨s.typeDepth, target⟩) found
            (List.mem_append_left _ equation)
        · obtain ⟨old, member, rfl⟩ := List.mem_map.mp outer
          have weakened := (resolve old member).weakenTypes size
          have lifted := weakened.mapAssumptions
            (target := (system.openContext ⟨s.typeDepth, target⟩).assumptions)
            (fun guard member =>
              @Subtype.hyp (system.openContext ⟨s.typeDepth, target⟩) guard
                (List.mem_append_right _ member))
          set_option backward.isDefEq.respectTransparency false in
            simp only [WFConstraint.weakenBy_sub, WFConstraint.weakenBy_sup]
          exact lifted
    | .recursiveCarrierRuntime system h => by
        refine .recursiveCarrierRuntime system ?_
        refine h.mapAssumptions
          (target := (system.openContext ⟨s.typeDepth, target⟩).assumptions) ?_
        intro found membership
        rcases List.mem_append.mp membership with equation | outer
        · exact @Subtype.hyp (system.openContext ⟨s.typeDepth, target⟩) found
            (List.mem_append_left _ equation)
        · obtain ⟨old, member, rfl⟩ := List.mem_map.mp outer
          have weakened := (resolve old member).weakenTypes system.size
          have lifted := weakened.mapAssumptions
            (target := (system.openContext ⟨s.typeDepth, target⟩).assumptions)
            (fun guard member =>
              @Subtype.hyp (system.openContext ⟨s.typeDepth, target⟩) guard
                (List.mem_append_right _ member))
          set_option backward.isDefEq.respectTransparency false in
            simp only [WFConstraint.weakenBy_sub, WFConstraint.weakenBy_sup]
          exact lifted
    | .recursive definition h => by
        refine .recursive definition ?_
        refine h.mapAssumptions
          (target := (definition.native.openContext ⟨s.typeDepth, target⟩).assumptions) ?_
        intro found membership
        simp only [RecursiveType.openContext, SubtypingContext.assume,
          SubtypingContext.bindType] at membership
        rcases List.mem_cons.mp membership with foldEqual | rest
        · subst found
          exact @Subtype.hyp (definition.native.openContext ⟨s.typeDepth, target⟩)
            (WFConstraint.constr definition.native.body definition.native.name) List.mem_cons_self
        · rcases List.mem_cons.mp rest with unfoldEqual | previous
          · subst found
            exact @Subtype.hyp (definition.native.openContext ⟨s.typeDepth, target⟩)
              (WFConstraint.constr definition.native.name definition.native.body)
              (List.mem_cons_of_mem _ List.mem_cons_self)
          · rcases List.mem_map.mp previous with ⟨old, oldMembership, equal⟩
            subst found
            simp only [RecursiveType.openContext, SubtypingContext.assume,
              SubtypingContext.bindType]
            have unfolded := (resolve old oldMembership).weakenType.weakenAssumption
              (WFConstraint.constr definition.native.name definition.native.body)
            simpa only [SubtypingContext.assume, SubtypingContext.bindType,
              WFConstraint.weaken_sub, WFConstraint.weaken_sup] using
              unfolded.weakenAssumption
                (WFConstraint.constr definition.native.body definition.native.name)

  theorem FieldsHaveType.mapAssumptions {s : SubtypingContext}
      {context : TypingContext s.typeDepth} {names : List FieldName} {fields : TermFields names}
      {types : List (FieldName × WFTy s.typeDepth)}
      (h : FieldsHaveType ghost s context fields types)
      {target : List (WFConstraint s.typeDepth)}
      (resolve : ∀ constraint, constraint ∈ s.assumptions →
        Subtype ⟨s.typeDepth, target⟩ constraint.sub constraint.sup) :
      FieldsHaveType ghost ⟨s.typeDepth, target⟩ context fields types :=
    match h with
    | .nil => .nil
    | .cons value rest => .cons (value.mapAssumptions resolve) (rest.mapAssumptions resolve)
end

/-- Adding a bound preserves recursive typing. -/
theorem HasType.weakenAssumption {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {term : Term} {type : WFTy s.typeDepth}
    (h : HasType ghost s context term type) (guard : WFConstraint s.typeDepth) :
    HasType ghost (s.assume guard) context term type :=
  h.mapAssumptions (target := guard :: s.assumptions) fun found member =>
    @Subtype.hyp (s.assume guard) found (List.mem_cons_of_mem guard member)

/-- A proved bound can be removed from a recursive typing derivation. -/
theorem HasType.dischargeAssumption {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {term : Term} {type : WFTy s.typeDepth}
    {guard : WFConstraint s.typeDepth} (h : HasType ghost (s.assume guard) context term type)
    (evidence : Subtype s guard.sub guard.sup) : HasType ghost s context term type := by
  refine h.mapAssumptions (target := s.assumptions) ?_
  intro found membership
  rcases List.mem_cons.mp membership with equal | previous
  · subst found
    exact evidence
  · exact @Subtype.hyp s found previous


/-- The same constraint extension is available for a whole native field list. -/
theorem FieldsHaveType.weakenAssumption {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {names : List FieldName} {fields : TermFields names}
    {types : List (FieldName × WFTy s.typeDepth)}
    (h : FieldsHaveType ghost s context fields types) (guard : WFConstraint s.typeDepth) :
    FieldsHaveType ghost (s.assume guard) context fields types :=
  h.mapAssumptions (target := guard :: s.assumptions) fun found member =>
    @Subtype.hyp (s.assume guard) found (List.mem_cons_of_mem guard member)

theorem FieldsHaveType.dischargeAssumption {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {names : List FieldName} {fields : TermFields names}
    {types : List (FieldName × WFTy s.typeDepth)} {guard : WFConstraint s.typeDepth}
    (h : FieldsHaveType ghost (s.assume guard) context fields types)
    (evidence : Subtype s guard.sub guard.sup) :
    FieldsHaveType ghost s context fields types := by
  refine h.mapAssumptions (target := s.assumptions) ?_
  intro found membership
  rcases List.mem_cons.mp membership with equal | previous
  · subst found
    exact evidence
  · exact @Subtype.hyp s found previous

theorem InvertingSubtype.dischargeAssumption {s : SubtypingContext}
    {sub sup : WFTy s.typeDepth} {guard : WFConstraint s.typeDepth}
    (h : InvertingSubtype ghost (s.assume guard) sub sup)
    (evidence : Subtype s guard.sub guard.sup) : InvertingSubtype ghost s sub sup :=
  .cut guard (.native evidence) h

end CDotFCCT.CTML.Mixed
