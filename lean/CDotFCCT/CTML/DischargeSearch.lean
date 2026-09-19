import CDotFCCT.CTML.Existentials
import CTMLCore.Algorithmic.Refinement

/-!
# Checked discharge using CTML's existing constraint solver

The solver may return deferred constraints or fresh variables. A package constructor
must not mistake that for a proof of its guards. This adapter accepts only results
that leave the original type depth and assumption set unchanged, and extracts an
actual native subtyping derivation from the solver's refinement theorem. Its search
reuses CTML's rule dispatcher, failing a revisited lookup so that an alternative
bound can be tried instead of accepting a deferred obligation.

Failure or fuel exhaustion does not imply that the constraint is underivable.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.DischargeSearch

open CTMLCore

abbrev rigid (s : SubtypingContext) : AlgContext := ⟨s.typeDepth, fun _ => false, s.assumptions⟩

/-- A cyclic attempt fails locally so that the dispatcher can try another bound. -/
def rejectTrail (trail : Trail) (rec : Trail → SolveFn) : SolveFn := fun s guard =>
  if revisit : trail.key guard ∈ trail.keys then .failed
  else rec (trail.push (trail.key guard) revisit (trail.key_fits guard)) s guard

theorem rejectTrail_sound {rec : Trail → SolveFn} (sound : ∀ trail, (rec trail).Sound)
    (trail : Trail) : (rejectTrail trail rec).Sound := by
  intro s guard delta computed
  unfold rejectTrail at computed
  split at computed
  · cases computed
  · exact sound _ s guard delta computed

/-- Reuse CTML's rule dispatcher with a failing, rather than deferring, revisit cut. -/
def solveTrail : Nat → Trail → SolveFn
  | 0, _ => fun _ _ => .fuelOut
  | fuel + 1, trail =>
      stepWith (solveTrail fuel trail) (rejectTrail trail (solveTrail fuel))
        (elimWith (solveTrail fuel trail) fuel)

theorem solveTrail_sound : ∀ fuel trail, (solveTrail fuel trail).Sound
  | 0, _ => fun _ _ _ computed => by simp [solveTrail] at computed
  | fuel + 1, trail =>
      stepWith_sound (solveTrail_sound fuel trail)
        (rejectTrail_sound (solveTrail_sound fuel) trail)
        (elimWith_sound (solveTrail_sound fuel trail) fuel)

def solve (fuel : Nat) : SolveFn := fun s guard => solveTrail fuel (Trail.start s guard) s guard

theorem solve_sound (fuel : Nat) : (solve fuel).Sound :=
  fun s guard delta computed => solveTrail_sound fuel _ s guard delta computed

theorem unchanged_sound {algorithm : SolveFn} (sound : algorithm.Sound) {s : SubtypingContext}
    {guard : WFConstraint s.typeDepth} {delta : Delta s.typeDepth}
    (computed : algorithm (rigid s) guard = .ok delta)
    (sameDepth : delta.target = s.typeDepth) (noAssumptions : delta.fresh = []) :
    Subtype s guard.sub guard.sup := by
  rcases delta with ⟨depth, valid, assumptions⟩
  change depth = s.typeDepth at sameDepth
  subst depth
  change assumptions = [] at noAssumptions
  subst assumptions
  have proof := (sound (rigid s) guard _ computed).sound
  change Derives ((rigid s).after valid []).erase (guard.weakenTo valid) at proof
  exact Derives.ofEq (congrArg AlgContext.erase (AlgContext.after_nil (rigid s) valid))
    (congrArg WFConstraint.raw (WFConstraint.weakenTo_refl valid guard)) proof

def dischargeUsing (algorithm : SolveFn) (sound : algorithm.Sound)
    (s : SubtypingContext) (guard : WFConstraint s.typeDepth) :
    Outcome (PLift (Subtype s guard.sub guard.sup)) :=
  match computed : algorithm (rigid s) guard with
  | .failed => .failed
  | .fuelOut => .fuelOut
  | .ok delta =>
      if sameDepth : delta.target = s.typeDepth then
        if noAssumptions : delta.fresh = [] then
          .ok ⟨unchanged_sound sound computed sameDepth noAssumptions⟩
        else .failed
      else .failed

def discharge (fuel : Nat) (s : SubtypingContext) (guard : WFConstraint s.typeDepth) :
    Outcome (PLift (Subtype s guard.sub guard.sup)) :=
  dischargeUsing (solve fuel) (solve_sound fuel) s guard

/-- Every guard is proved in the original context; earlier goals never become assumptions. -/
def dischargeAll (fuel : Nat) (s : SubtypingContext) :
    (guards : List (WFConstraint s.typeDepth)) → Outcome (PLift (Satisfies s guards))
  | [] => .ok ⟨fun _ member => False.elim (List.not_mem_nil member)⟩
  | guard :: guards => do
      let first ← discharge fuel s guard
      let rest ← dischargeAll fuel s guards
      return ⟨by
        intro found member
        exact (List.mem_cons.mp member).elim (fun same => same ▸ first.down)
          (rest.down found)⟩

/-- Proved hints can guide the solver without enlarging the resulting assumption set. -/
theorem removeHints {s : SubtypingContext} {sub sup : WFTy s.typeDepth}
    (hints : List (WFConstraint s.typeDepth)) (evidence : Satisfies s hints)
    (proof : Subtype (assumeMany s hints) sub sup) : Subtype s sub sup := by
  refine proof.mapAssumptions ?_
  exact fun guard member => (List.mem_append.mp member).elim
    (fun present => evidence guard (List.mem_reverse.mp present))
    (fun present => @Subtype.hyp s guard present)

def dischargeWithHints (fuel : Nat) (s : SubtypingContext)
    (hints : List (WFConstraint s.typeDepth)) (evidence : Satisfies s hints)
    (guards : List (WFConstraint s.typeDepth)) : Outcome (PLift (Satisfies s guards)) := do
  let proved ← dischargeAll fuel (assumeMany s hints) guards
  return ⟨fun guard member => removeHints hints evidence (proved.down guard member)⟩

end CDotFCCT.CTML.DischargeSearch
