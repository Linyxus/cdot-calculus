import CTMLCore.Declarative.Soundness
import CTMLCore.Declarative.Discharge

/-!
# Continuation-encoded constrained existentials over CTML Core

At a fixed CPS answer type `R`, `∃A. [guards(A)] × payload(A)` is represented by
`(∀A. guards(A) ⇒ payload(A) → R) → R`. The answer is outside the witness's scope.
Packing must prove the instantiated guards; the consumer may assume them. These are
derived CTML Core typing rules, with no extension to its syntax, subtyping, or axioms.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

/-- A sequence of ordinary FCCT constraint abstractions. -/
def qualify {n : Nat} (guards : List (WFConstraint n)) (body : WFTy n) : WFTy n :=
  guards.foldr WFTy.constrained body

/-- The constraints become assumptions in their introduction order. -/
def assumeMany (subtyping : SubtypingContext)
    (guards : List (WFConstraint subtyping.typeDepth)) : SubtypingContext :=
  ⟨subtyping.typeDepth, guards.reverse ++ subtyping.assumptions⟩

/-- All the evidence required to discharge a list of guards. -/
def Satisfies (subtyping : SubtypingContext)
    (guards : List (WFConstraint subtyping.typeDepth)) : Prop :=
  ∀ guard ∈ guards, Subtype subtyping guard.sub guard.sup

/-- The consumer introduces one abstract witness and may assume all its constraints. -/
def consumer {n : Nat} (guards : List (WFConstraint (n + 1)))
    (payload : WFTy (n + 1)) (answer : WFTy n) : WFTy n :=
  WFTy.all (qualify guards (WFTy.arrow payload answer.weaken))

/-- An existential in CPS, with an answer type independent of its witness. -/
def existsCPS {n : Nat} (guards : List (WFConstraint (n + 1)))
    (payload : WFTy (n + 1)) (answer : WFTy n) : WFTy n :=
  WFTy.arrow (consumer guards payload answer) answer

/-- Packing erases the witness and its subtyping proofs: `λk. k value`. -/
def pack (value : Term) : Term := .abs (.app (.var 0) (value.lift 1))

/-- Evaluate a payload before packaging it, to retain call-by-value evaluation order. -/
def packCBV (term : Term) : Term := .app (.abs (pack (.var 0))) term

/-- Bounds are ordinary constraints on the same abstract witness. -/
def bounds {n : Nat} (lower upper : WFTy n) : List (WFConstraint (n + 1)) :=
  [WFConstraint.constr lower.weaken (WFTy.var 0 (Nat.zero_lt_succ n)),
   WFConstraint.constr (WFTy.var 0 (Nat.zero_lt_succ n)) upper.weaken]

/-- Every abstracted guard is available inside the consumer. -/
theorem assumedGuard {subtyping : SubtypingContext}
    {guards : List (WFConstraint subtyping.typeDepth)}
    {guard : WFConstraint subtyping.typeDepth} (membership : guard ∈ guards) :
    Subtype (assumeMany subtyping guards) guard.sub guard.sup :=
  @Subtype.hyp (assumeMany subtyping guards) guard
    (List.mem_append_left _ (List.mem_reverse.mpr membership))

/-- Packing a bounded witness requires exactly its lower and upper bound proofs. -/
theorem boundsSatisfies {subtyping : SubtypingContext}
    {lower upper witness : WFTy subtyping.typeDepth}
    (lowerBound : Subtype subtyping lower witness)
    (upperBound : Subtype subtyping witness upper) :
    Satisfies subtyping ((bounds lower upper).map (·.instantiate witness)) := by
  simp only [Satisfies, bounds, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq]
  change Subtype subtyping (lower.weaken.instantiate witness) witness ∧
    Subtype subtyping witness (upper.weaken.instantiate witness)
  simpa only [WFTy.weaken_instantiate_cancel] using And.intro lowerBound upperBound

/-- A consumer can be instantiated at a witness whose guards have been proved. -/
theorem consumerInstance {subtyping : SubtypingContext}
    {guards : List (WFConstraint (subtyping.typeDepth + 1))}
    {payload : WFTy (subtyping.typeDepth + 1)} {answer witness : WFTy subtyping.typeDepth}
    (evidence : Satisfies subtyping (guards.map (·.instantiate witness))) :
    Subtype subtyping (consumer guards payload answer)
      (WFTy.arrow (payload.instantiate witness) answer) := by
  refine .trans (Subtype.forallLeft (argument := witness)) ?_
  induction guards with
  | nil =>
      change Subtype subtyping
        (WFTy.arrow (payload.instantiate witness) (answer.weaken.instantiate witness)) _
      rw [WFTy.weaken_instantiate_cancel]
      exact .refl
  | cons guard guards ih =>
      change Subtype subtyping
        (WFTy.constrained (guard.instantiate witness)
          ((qualify guards (WFTy.arrow payload answer.weaken)).instantiate witness)) _
      exact .trans (.constrainedLeft _ _ (evidence _ List.mem_cons_self))
        (ih (fun found membership => evidence found (List.mem_cons_of_mem _ membership)))

/-- A typed payload and proofs of its instantiated guards produce a typed CPS package. -/
theorem packTyping {subtyping : SubtypingContext}
    {context : TypingContext subtyping.typeDepth}
    {guards : List (WFConstraint (subtyping.typeDepth + 1))}
    {payload : WFTy (subtyping.typeDepth + 1)} {answer witness : WFTy subtyping.typeDepth}
    {value : Term} (hValue : HasType subtyping context value (payload.instantiate witness))
    (evidence : Satisfies subtyping (guards.map (·.instantiate witness))) :
    HasType subtyping context (pack value) (existsCPS guards payload answer) :=
  .abstraction (.application
    ((HasType.var _ 0 _ .here).subsumption (consumerInstance evidence))
    (hValue.weakenFront (consumer guards payload answer)))

/-- Unlike `pack`, this form evaluates its payload before returning the package. -/
theorem packCBVTyping {subtyping : SubtypingContext}
    {context : TypingContext subtyping.typeDepth}
    {guards : List (WFConstraint (subtyping.typeDepth + 1))}
    {payload : WFTy (subtyping.typeDepth + 1)} {answer witness : WFTy subtyping.typeDepth}
    {term : Term} (hTerm : HasType subtyping context term (payload.instantiate witness))
    (evidence : Satisfies subtyping (guards.map (·.instantiate witness))) :
    HasType subtyping context (packCBV term) (existsCPS guards payload answer) :=
  .application (.abstraction (packTyping (HasType.var _ 0 _ .here) evidence)) hTerm

theorem packCBVStep {value : Term} (hValue : Value value) :
    Step (packCBV value) (pack value) := .appBeta _ _ hValue

/-- Constraint abstraction is valid for every nonexpansive consumer, even under inconsistent
guards. No consistency premise is needed until a package supplies a witness. -/
theorem qualifyTyping {n : Nat} {assumptions : List (WFConstraint n)}
    {context : TypingContext n} {term : Term} {body : WFTy n}
    (guards : List (WFConstraint n)) (nonexpansive : Nonexpansive term)
    (h : HasType (assumeMany ⟨n, assumptions⟩ guards) context term body) :
    HasType ⟨n, assumptions⟩ context term (qualify guards body) := by
  induction guards generalizing assumptions with
  | nil => exact h
  | cons guard guards ih =>
      refine @HasType.constrained ⟨n, assumptions⟩ guard (qualify guards body) context term
        nonexpansive (ih (assumptions := guard :: assumptions) ?_)
      change HasType ⟨n, (guard :: guards).reverse ++ assumptions⟩ context term body at h
      rw [List.reverse_cons, List.append_assoc] at h
      exact h

/-- The consumer is checked once under a fresh witness and its guards. Its lambda form
meets FCCT's value restriction, even when the body performs computation. -/
theorem consumerTyping {subtyping : SubtypingContext}
    {context : TypingContext subtyping.typeDepth}
    {guards : List (WFConstraint (subtyping.typeDepth + 1))}
    {payload : WFTy (subtyping.typeDepth + 1)} {answer : WFTy subtyping.typeDepth}
    {body : Term}
    (hBody : HasType (assumeMany subtyping.bindType guards)
      (context.bindType.bind payload) (body.liftTy 1) answer.weaken) :
    HasType subtyping context (.abs body) (consumer guards payload answer) :=
  .forall _ _ _ (.value (.abs _))
    (qualifyTyping guards (.value (.abs _)) (.abstraction hBody))

/-- Existential elimination keeps the witness scoped over the entire continuation. -/
theorem unpackTyping {subtyping : SubtypingContext}
    {context : TypingContext subtyping.typeDepth}
    {guards : List (WFConstraint (subtyping.typeDepth + 1))}
    {payload : WFTy (subtyping.typeDepth + 1)} {answer : WFTy subtyping.typeDepth}
    {package body : Term}
    (hPackage : HasType subtyping context package (existsCPS guards payload answer))
    (hBody : HasType (assumeMany subtyping.bindType guards)
      (context.bindType.bind payload) (body.liftTy 1) answer.weaken) :
    HasType subtyping context (.app package (.abs body)) answer :=
  .application hPackage (consumerTyping hBody)

end CDotFCCT.CTML
