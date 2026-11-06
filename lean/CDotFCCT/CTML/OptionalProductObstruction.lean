import CDotFCCT.CTML.MixedInterpretation
import CTMLCore.Declarative.IndexedTransport

/-!
# A gap obstruction for optional product carriers

Replacing labelled unions by products preserves simultaneous positive observations.
It still cannot characterize an arbitrary cross-component subtype relation by one
uniform upper candidate when candidate witnesses may have observation gaps. This
file tests the proposed product with paired positive and negative optional slots.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.OptionalProduct

open CTMLCore (WFTy WFConstraint)
open CTMLCore.Syntax CTMLCore.Indexed

def gap : Candidate := fun _ => (fun _ => False, fun _ => False)

def top : Candidate := fun _ => (fun _ => True, fun _ => False)

def unit : Candidate := interpret (fun _ => true) (fun _ => gap) (.cls "Unit")

def optional (payload : Candidate) : Candidate :=
  joint .union unit (TransparentRecord.record "value" payload)

/-- Four distinct slots preserve both observations of each component. -/
def product (member child : Candidate) : Candidate :=
  joint .intersection
    (joint .intersection
      (TransparentRecord.record "member+" (optional member))
      (TransparentRecord.record "member-" (optional (negative member))))
    (joint .intersection
      (TransparentRecord.record "child+" (optional child))
      (TransparentRecord.record "child-" (optional (negative child))))

def optionalTy {depth : Nat} (payload : WFTy depth) : WFTy depth :=
  WFTy.union (WFTy.cls "Unit") (WFTy.record "value" payload)

def productTy {depth : Nat} (member child : WFTy depth) : WFTy depth :=
  WFTy.intersection
    (WFTy.intersection
      (WFTy.record "member+" (optionalTy member))
      (WFTy.record "member-" (optionalTy (WFTy.neg member))))
    (WFTy.intersection
      (WFTy.record "child+" (optionalTy child))
      (WFTy.record "child-" (optionalTy (WFTy.neg child))))

/-- The tested model is exactly the interpretation of the proposed native type syntax. -/
theorem interpret_product {depth : Nat} (env : Environment) (member child : WFTy depth) :
    interpret (fun _ => true) env (productTy member child).raw =
      product (interpret (fun _ => true) env member.raw)
        (interpret (fun _ => true) env child.raw) := rfl

private def defaultFields : TermFields ["member+", "member-", "child+", "child-"] :=
  .cons "member+" (.record "Unit" .nil)
    (.cons "member-" (.record "Unit" .nil)
      (.cons "child+" (.record "Unit" .nil)
        (.cons "child-" (.record "Unit" .nil) .nil (by decide)) (by decide))
      (by decide)) (by decide)

def defaultTerm : Term := .record "Product" defaultFields

private theorem default_observed (payload : Candidate) (n : Nat) {field : FieldName}
    (lookup : TermFields.Lookup defaultFields field (.record "Unit" .nil)) :
    TransparentRecord.observes field (optional payload n).1 defaultTerm :=
  ⟨"Product", _, defaultFields, .record "Unit" .nil, rfl, lookup, .inl ⟨[], .nil, rfl⟩⟩

/-- The bad tuple's product remains positively inhabited, as do all other tuples. -/
theorem default_positive (member child : Candidate) (n : Nat) :
    (product member child n).1 defaultTerm :=
  ⟨⟨default_observed member n .here,
      default_observed (negative member) n (.there .here)⟩,
    ⟨default_observed child n (.there (.there .here)),
      default_observed (negative child) n (.there (.there (.there .here)))⟩⟩

/-- Observation-wise inclusion, unlike subtyping, transports both polarities forward. -/
private def ObservationsLe (left right : Candidate) : Prop :=
  ∀ n term, ((left n).1 term → (right n).1 term) ∧
    ((left n).2 term → (right n).2 term)

private theorem ObservationsLe.refl (candidate : Candidate) :
    ObservationsLe candidate candidate := fun _ _ => ⟨id, id⟩

private theorem ObservationsLe.negative {left right : Candidate}
    (included : ObservationsLe left right) :
    ObservationsLe (negative left) (negative right) :=
  fun n term => ⟨(included n term).2, (included n term).1⟩

private theorem ObservationsLe.joint (kind : Joint) {left right left' right' : Candidate}
    (first : ObservationsLe left left') (second : ObservationsLe right right') :
    ObservationsLe (joint kind left right) (joint kind left' right') := by
  intro n term
  cases kind
  · exact ⟨Or.imp (first n term).1 (second n term).1,
      And.imp (first n term).2 (second n term).2⟩
  · exact ⟨And.imp (first n term).1 (second n term).1,
      Or.imp (first n term).2 (second n term).2⟩

private theorem ObservationsLe.record {left right : Candidate}
    (included : ObservationsLe left right) (field : FieldName) :
    ObservationsLe (TransparentRecord.record field left)
      (TransparentRecord.record field right) :=
  fun n _ => ⟨TransparentRecord.observes_mono (fun value => (included n value).1),
    TransparentRecord.observesAll_mono (fun value => (included n value).2)⟩

private theorem ObservationsLe.optional {left right : Candidate}
    (included : ObservationsLe left right) : ObservationsLe (optional left) (optional right) :=
  (ObservationsLe.refl unit).joint .union (included.record "value")

private theorem ObservationsLe.product {member child member' child' : Candidate}
    (members : ObservationsLe member member') (children : ObservationsLe child child') :
    ObservationsLe (product member child) (product member' child') :=
  ((members.optional.record "member+").joint .intersection
    (members.negative.optional.record "member-")).joint .intersection
    ((children.optional.record "child+").joint .intersection
      (children.negative.optional.record "child-"))

private theorem gap_le (candidate : Candidate) : ObservationsLe gap candidate :=
  fun _ _ => ⟨False.elim, False.elim⟩

/-- Two legal diagonal products already cover this illegal off-diagonal product. -/
theorem gap_crossed (n : Nat) :
    Includes (product gap top)
      (joint .union (product top top) (product gap gap)) n := by
  intro k _ term
  exact ⟨fun observed => .inl
    (((gap_le top).product (.refl top) k term).1 observed),
    fun rejected =>
      (((ObservationsLe.refl gap).product (gap_le top) k term).2 rejected.2)⟩

/-- Both witness choices in the counterexample satisfy consistency and downward closure. -/
theorem counterexample_candidates :
    Downward gap ∧ Downward top ∧
      (∀ n term, ¬ ((gap n).1 term ∧ (gap n).2 term)) ∧
      (∀ n term, ¬ ((top n).1 term ∧ (top n).2 term)) := by
  exact ⟨fun _ _ _ _ => ⟨id, id⟩, fun _ _ _ _ => ⟨id, id⟩,
    fun _ _ observed => observed.1, fun _ _ observed => observed.2⟩

def EncodesRelation (bound : Candidate) (n : Nat) : Prop :=
  ∀ member child,
    Includes (product member child) bound n ↔ Includes child member n

/-- This failure concerns every upper candidate, not only existential type syntax. -/
theorem no_uniform_bound (n : Nat) : ¬ ∃ bound, EncodesRelation bound n := by
  rintro ⟨bound, encodes⟩
  have first := (encodes top top).mpr (Includes.refl top n)
  have second := (encodes gap gap).mpr (Includes.refl gap n)
  have crossed : Includes (product gap top) bound n :=
    (gap_crossed n).trans (fun k within term =>
      ⟨fun observed => observed.elim (first k within term).1 (second k within term).1,
        fun rejected =>
          ⟨(first k within term).2 rejected, (second k within term).2 rejected⟩⟩)
  exact (((encodes gap top).mp crossed) 0 (Nat.zero_le n) (.var 0)).1 trivial

def Admissible (candidate : Candidate) : Prop :=
  Downward candidate ∧ ∀ n term, ¬ ((candidate n).1 term ∧ (candidate n).2 term)

theorem gap_admissible : Admissible gap :=
  ⟨counterexample_candidates.1, counterexample_candidates.2.2.1⟩

theorem top_admissible : Admissible top :=
  ⟨counterexample_candidates.2.1, counterexample_candidates.2.2.2⟩

/-- Excluding contradictory candidates still leaves the counterexample. -/
theorem no_consistent_uniform_bound (n : Nat) :
    ¬ ∃ bound, ∀ member child, Admissible member → Admissible child →
      (Includes (product member child) bound n ↔ Includes child member n) := by
  rintro ⟨bound, encodes⟩
  have first := (encodes top top top_admissible top_admissible).mpr (Includes.refl top n)
  have second := (encodes gap gap gap_admissible gap_admissible).mpr (Includes.refl gap n)
  have crossed : Includes (product gap top) bound n :=
    (gap_crossed n).trans (fun k within term =>
      ⟨fun observed => observed.elim (first k within term).1 (second k within term).1,
        fun rejected =>
          ⟨(first k within term).2 rejected, (second k within term).2 rejected⟩⟩)
  exact (((encodes gap top gap_admissible top_admissible).mp crossed)
    0 (Nat.zero_le n) (.var 0)).1 trivial

def existential (body : Candidate → Candidate) : Candidate :=
  negative (universal (fun argument => negative (body (prefixClosure argument))))

def requireGuard (guard : Nat → Prop) (body : Candidate) : Candidate :=
  negative (constrained guard (negative body))

/-- Hiding both components gives a uniform candidate for the proposed relational bound. -/
def relationBound : Candidate :=
  existential (fun child => existential (fun member =>
    requireGuard (Includes child member) (product member child)))

def existentialTy {depth : Nat} (body : WFTy (depth + 1)) : WFTy depth :=
  WFTy.neg (WFTy.all (WFTy.neg body))

def requireGuardTy {depth : Nat} (guard : WFConstraint depth) (body : WFTy depth) :
    WFTy depth := WFTy.neg (WFTy.constrained guard (WFTy.neg body))

def relationBoundTy : WFTy 0 :=
  existentialTy (existentialTy
    (requireGuardTy (WFConstraint.constr (WFTy.var 1 (by decide)) (WFTy.var 0 (by decide)))
      (productTy (WFTy.var 0 (by decide)) (WFTy.var 1 (by decide)))))

theorem interpret_relationBound (env : Environment) :
    interpret (fun _ => true) env relationBoundTy.raw = relationBound := rfl

theorem diagonal_included (candidate : Candidate) (closed : Downward candidate) (n : Nat) :
    Includes (product candidate candidate) relationBound n := by
  intro k _ term
  constructor
  · intro observed
    refine ⟨candidate, candidate, ?_⟩
    simpa only [prefixClosure_eq closed, negative, requireGuard, constrained] using
      And.intro (Includes.refl candidate k) observed
  · intro rejected
    have diagonal := rejected candidate candidate k (Nat.le_refl k)
    simpa only [prefixClosure_eq closed, negative] using
      diagonal (Includes.refl (prefixClosure candidate) k)

/-- The actual existential/constraint syntax accepts the bad tuple already at index zero. -/
theorem existential_counterexample (n : Nat) :
    Includes (product gap top) relationBound n ∧ ¬ Includes top gap n := by
  refine ⟨(gap_crossed n).trans ?_, ?_⟩
  · have first := diagonal_included top counterexample_candidates.2.1 n
    have second := diagonal_included gap counterexample_candidates.1 n
    exact fun k within term =>
      ⟨fun observed => observed.elim (first k within term).1 (second k within term).1,
        fun rejected => ⟨(first k within term).2 rejected, (second k within term).2 rejected⟩⟩
  · intro included
    exact (included 0 (Nat.zero_le n) (.var 0)).1 trivial

end CDotFCCT.CTML.Mixed.OptionalProduct
