import CDotFCCT.CTML.CarrierEquationInterpretation
import CDotFCCT.CTML.ComplementedProduct

/-!
# Complemented ghost codes and pure record equations

This checks a restricted semantic domain for type codes, separate from runtime
payload types. No complement rule is added to native or mixed subtyping.
Both-polarity downward closure makes complemented observations independent of
the step index. Reflective records preserve complementation by inspecting their
payload structurally, so record guards need not be replaced with arrows.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.ComplementedGhostCodes

open CTMLCore (WFTy)
open CTMLCore.Syntax CTMLCore.Indexed

def Complementary (candidate : Candidate) : Prop :=
  ∀ n term, (candidate n).2 term ↔ ¬ (candidate n).1 term

def ComplementaryAt (candidate : Candidate) (n : Nat) : Prop :=
  ∀ term, (candidate n).2 term ↔ ¬ (candidate n).1 term

def Static (candidate : Candidate) : Prop := ∀ n, candidate n = candidate 0

theorem complementary_guard {candidate : Candidate} (complete : Complementary candidate)
    (n : Nat) : ComplementedProduct.Complemented candidate n := by
  intro k _ term
  exact ⟨fun _ => (Classical.em ((candidate k).1 term)).elim Or.inl
      (fun absent => .inr ((complete k term).mpr absent)),
    fun both => (complete k term).mp both.1 both.2⟩

theorem guards_complementary {candidate : Candidate}
    (complete : ∀ n, ComplementedProduct.Complemented candidate n) :
    Complementary candidate := by
  intro n term
  constructor
  · exact fun rejected observed =>
      (complete n n (Nat.le_refl n) term).2 ⟨rejected, observed⟩
  · intro absent
    exact ((complete n n (Nat.le_refl n) term).1 trivial).resolve_left absent

theorem guard_complementaryAt {candidate : Candidate} {n k : Nat}
    (complete : ComplementedProduct.Complemented candidate n) (within : k ≤ n) :
    ComplementaryAt candidate k := by
  intro term
  constructor
  · exact fun rejected observed => (complete k within term).2 ⟨rejected, observed⟩
  · intro absent
    exact ((complete k within term).1 trivial).resolve_left absent

theorem record_complementary {candidate : Candidate} (complete : Complementary candidate)
    (field : FieldName) : Complementary (TransparentRecord.record field candidate) :=
  fun n _ =>
    ⟨fun all ⟨className, names, fields, value, equal, lookup, observed⟩ =>
      (complete n value).mp (all className names fields value equal lookup) observed,
     fun absent className names fields value equal lookup =>
      (complete n value).mpr
        (fun observed => absent ⟨className, names, fields, value, equal, lookup, observed⟩)⟩

theorem downward_static {candidate : Candidate} (complete : Complementary candidate)
    (downward : Downward candidate) : Static candidate := by
  intro n
  apply Prod.ext <;> funext term <;> apply propext
  · refine ⟨(downward 0 n (Nat.zero_le n) term).1, ?_⟩
    intro observed
    by_contra absent
    exact (complete 0 term).mp
      ((downward 0 n (Nat.zero_le n) term).2 ((complete n term).mpr absent)) observed
  · exact ⟨(downward 0 n (Nat.zero_le n) term).2, fun rejected =>
      (complete n term).mpr (fun observed =>
        (complete 0 term).mp rejected ((downward 0 n (Nat.zero_le n) term).1 observed))⟩

theorem negative_complementary {candidate : Candidate} (complete : Complementary candidate) :
    Complementary (negative candidate) := by
  intro n term
  simpa only [negative, not_not] using (not_congr (complete n term)).symm

theorem joint_complementary (kind : Joint) {left right : Candidate}
    (first : Complementary left) (second : Complementary right) :
    Complementary (joint kind left right) := by
  intro n term
  cases kind <;> simp only [joint, first n term, second n term, not_or, not_and_or]

variable {ghost : FieldName → Bool} {depth size : Nat}

def Leaves (property : WFTy depth → Prop) :
    CarrierEquation.Expr ghost depth size → Prop
  | .leaf type => property type
  | .ref _ => True
  | .neg body => Leaves property body
  | .joint _ left right => Leaves property left ∧ Leaves property right
  | .record _ _ body => Leaves property body

def LeavesComplementary (parameters : CarrierEquation.Parameters depth) :
    CarrierEquation.Expr ghost depth size → Prop :=
  Leaves (fun type => Complementary (parameters type))

def LeavesComplemented (parameters : CarrierEquation.Parameters depth) (n : Nat) :
    CarrierEquation.Expr ghost depth size → Prop :=
  Leaves (fun type => ComplementedProduct.Complemented (parameters type) n)

def LeavesComplementaryAt (parameters : CarrierEquation.Parameters depth) (n : Nat) :
    CarrierEquation.Expr ghost depth size → Prop :=
  Leaves (fun type => ComplementaryAt (parameters type) n)

/-- Transport the evidence attached to the occurring leaves of a pure expression. -/
theorem leaves_mono (expression : CarrierEquation.Expr ghost depth size)
    {first second : WFTy depth → Prop} (implies : ∀ type, first type → second type)
    (leaves : Leaves first expression) : Leaves second expression := by
  induction expression with
  | leaf type => exact implies type leaves
  | ref _ => trivial
  | neg _ ih => exact ih leaves
  | joint _ _ _ left right => exact ⟨left leaves.1, right leaves.2⟩
  | record _ _ _ ih => exact ih leaves

theorem denote_complementary (expression : CarrierEquation.Expr ghost depth size)
    {parameters : CarrierEquation.Parameters depth} {selves : Fin size → Candidate}
    (leaves : LeavesComplementary parameters expression)
    (references : ∀ index, Complementary (selves index)) :
    Complementary (expression.denote parameters selves) := by
  induction expression with
  | leaf _ => exact leaves
  | ref index => exact references index
  | neg _ ih => exact negative_complementary (ih leaves)
  | joint kind _ _ first second => exact joint_complementary kind (first leaves.1) (second leaves.2)
  | record field _ _ ih => exact record_complementary (ih leaves) field

private theorem lookup_smaller {names : List FieldName} {fields : TermFields names}
    {field : FieldName} {value : Term} (lookup : TermFields.Lookup fields field value) :
    sizeOf value < sizeOf fields := by
  induction lookup with
  | here => simp only [TermFields.cons.sizeOf_spec]; omega
  | there _ ih => simp only [TermFields.cons.sizeOf_spec]; omega

private theorem lookup_record_smaller {names : List FieldName} {fields : TermFields names}
    {field : FieldName} {value : Term} (className : ClassName)
    (lookup : TermFields.Lookup fields field value) :
    sizeOf value < sizeOf (Term.record className fields) := by
  have smaller := lookup_smaller lookup
  simp only [Term.record.sizeOf_spec]
  omega

private theorem record_complementary_local (field : FieldName) (n : Nat) (term : Term)
    {payload : Candidate}
    (complete : ∀ value, sizeOf value < sizeOf term →
      ((payload n).2 value ↔ ¬ (payload n).1 value)) :
    (TransparentRecord.record field payload n).2 term ↔
      ¬ (TransparentRecord.record field payload n).1 term :=
  ⟨fun all ⟨className, names, fields, value, equal, lookup, observed⟩ =>
    (complete value (equal.symm ▸ lookup_record_smaller className lookup)).mp
      (all className names fields value equal lookup) observed,
   fun absent className names fields value equal lookup =>
    (complete value (equal.symm ▸ lookup_record_smaller className lookup)).mpr
      (fun observed => absent ⟨className, names, fields, value, equal, lookup, observed⟩)⟩

private theorem denote_complementary_below (expression : CarrierEquation.Expr ghost depth size)
    {parameters : CarrierEquation.Parameters depth} {selves : Fin size → Candidate}
    {bound n : Nat} (leaves : LeavesComplementaryAt parameters n expression)
    (references : ∀ index term, sizeOf term < bound →
      ((selves index n).2 term ↔ ¬ (selves index n).1 term))
    (term : Term) (small : sizeOf term < bound) :
    (expression.denote parameters selves n).2 term ↔
      ¬ (expression.denote parameters selves n).1 term := by
  induction expression generalizing term with
  | leaf _ => exact leaves term
  | ref index => exact references index term small
  | neg body ih =>
      simpa only [CarrierEquation.Expr.denote, negative, not_not] using
        (not_congr (ih leaves term small)).symm
  | joint kind first second ihFirst ihSecond =>
      cases kind <;> simp only [CarrierEquation.Expr.denote, joint,
        ihFirst leaves.1 term small, ihSecond leaves.2 term small, not_or, not_and_or]
  | record field _ body ih =>
      exact record_complementary_local field n term
        (fun value smaller => ih leaves value (Nat.lt_trans smaller small))

private theorem guarded_complementary_below (expression : CarrierEquation.Expr ghost depth size)
    (guarded : expression.Guarded)
    {parameters : CarrierEquation.Parameters depth} {selves : Fin size → Candidate}
    {bound n : Nat} (leaves : LeavesComplementaryAt parameters n expression)
    (references : ∀ index term, sizeOf term < bound →
      ((selves index n).2 term ↔ ¬ (selves index n).1 term))
    (term : Term) (small : sizeOf term ≤ bound) :
    (expression.denote parameters selves n).2 term ↔
      ¬ (expression.denote parameters selves n).1 term := by
  induction expression generalizing term with
  | leaf _ => exact leaves term
  | ref _ => exact guarded.elim
  | neg body ih =>
      simpa only [CarrierEquation.Expr.denote, negative, not_not] using
        (not_congr (ih guarded leaves term small)).symm
  | joint kind first second ihFirst ihSecond =>
      cases kind <;> simp only [CarrierEquation.Expr.denote, joint,
        ihFirst guarded.1 leaves.1 term small, ihSecond guarded.2 leaves.2 term small,
        not_or, not_and_or]
  | record field _ body _ =>
      exact record_complementary_local field n term
        (fun value smaller => denote_complementary_below body leaves references value
          (Nat.lt_of_lt_of_le smaller small))

/-- Every solution of the pure equations is complementary at the current index. -/
theorem equations_complementaryAt (system : CarrierEquation.System ghost depth size)
    {parameters : CarrierEquation.Parameters depth} {selves : Fin size → Candidate} {n : Nat}
    (leaves : ∀ index, LeavesComplementaryAt parameters n (system.body index))
    (equations : ∀ index, selves index n = (system.body index).denote parameters selves n)
    (index : Fin size) : ComplementaryAt (selves index) n := by
  intro term
  have complete : ∀ fuel term, sizeOf term < fuel → ∀ index,
      ((selves index n).2 term ↔ ¬ (selves index n).1 term) := by
    intro fuel
    induction fuel with
    | zero => exact fun _ smaller => (Nat.not_lt_zero _ smaller).elim
    | succ fuel ih =>
        intro value small component
        rw [equations component]
        exact guarded_complementary_below (system.body component) (system.guarded component)
          (leaves component) (fun found value smaller => ih value smaller found)
          value (Nat.le_of_lt_succ small)
  exact complete (sizeOf term + 1) term (Nat.lt_succ_self _) index

/-- Pure ghost equations preserve complement, including negative recursive references. -/
theorem solution_complementary (system : CarrierEquation.System ghost depth size)
    {parameters : CarrierEquation.Parameters depth}
    (leaves : ∀ index, LeavesComplementary parameters (system.body index))
    (index : Fin size) : Complementary (system.solution parameters index) :=
  fun n => equations_complementaryAt system
    (fun component => leaves_mono (system.body component) (fun _ complete => complete n)
      (leaves component))
    (fun component => congrFun (system.solution_equation parameters component) n) index

/-- A prefix of equation equalities suffices; no particular solution environment is chosen. -/
theorem equations_guard (system : CarrierEquation.System ghost depth size)
    {parameters : CarrierEquation.Parameters depth} {selves : Fin size → Candidate} {n : Nat}
    (leaves : ∀ index, LeavesComplemented parameters n (system.body index))
    (equations : ∀ index, Agree n (selves index) ((system.body index).denote parameters selves))
    (index : Fin size) : ComplementedProduct.Complemented (selves index) n := by
  intro k within term
  have complete := equations_complementaryAt system
    (fun component => leaves_mono (system.body component)
      (fun _ complete => guard_complementaryAt complete within) (leaves component))
    (fun component => equations component k within) index term
  exact ⟨fun _ => (Classical.em ((selves index k).1 term)).elim Or.inl
      (fun absent => .inr (complete.mpr absent)),
    fun both => complete.mp both.1 both.2⟩

private def clipped (parameters : CarrierEquation.Parameters depth) (n : Nat) :
    CarrierEquation.Parameters depth := fun type k => parameters type (min k n)

private theorem clipped_complementary {candidate : Candidate} {n : Nat}
    (complete : ComplementedProduct.Complemented candidate n) :
    Complementary (fun k => candidate (min k n)) := by
  intro k term
  constructor
  · exact fun rejected observed =>
      (complete (min k n) (Nat.min_le_right k n) term).2 ⟨rejected, observed⟩
  · intro absent
    exact ((complete (min k n) (Nat.min_le_right k n) term).1 trivial).resolve_left absent

/-- Ambient completeness guards need hold only through the current observation index. -/
theorem solution_guard (system : CarrierEquation.System ghost depth size)
    {parameters : CarrierEquation.Parameters depth} {n : Nat}
    (leaves : ∀ index, LeavesComplemented parameters n (system.body index))
    (index : Fin size) : ComplementedProduct.Complemented (system.solution parameters index) n := by
  have guarded := complementary_guard (solution_complementary system
    (parameters := clipped parameters n)
    (fun component => leaves_mono (system.body component)
      (fun _ complete => clipped_complementary complete) (leaves component)) index) n
  intro k within term
  have equal := system.solution_congr (left := clipped parameters n) (right := parameters)
    (n := k) (fun _ => congrArg _ (Nat.min_eq_left within)) index
  simpa only [joint, negative, equal] using guarded k within term

theorem interpretation_guard (system : CarrierEquation.System ghost depth size)
    (env : Environment) (n : Nat)
    (leaves : ∀ index, LeavesComplemented (fun type => interpret ghost env type.raw) n
      (system.body index)) (index : Fin size) :
    ComplementedProduct.Complemented (system.interpretation env index) n :=
  solution_guard system leaves index

theorem interpretation_complementary (system : CarrierEquation.System ghost depth size)
    (env : Environment)
    (leaves : ∀ index, LeavesComplementary (fun type => interpret ghost env type.raw)
      (system.body index)) (index : Fin size) :
    Complementary (system.interpretation env index) :=
  solution_complementary system leaves index

theorem interpretation_static (system : CarrierEquation.System ghost depth size)
    (env : Environment)
    (leaves : ∀ index, LeavesComplementary (fun type => interpret ghost env type.raw)
      (system.body index)) (index : Fin size) :
    Static (system.interpretation env index) :=
  downward_static (interpretation_complementary system env leaves index)
    (system.downward env index)

/-- A negative recursive cycle has an ordinary finite-term ghost interpretation. -/
def negativeCycle : CarrierEquation.System (fun _ => true) 0 1 where
  body := fun _ => .record "code" rfl (.neg (.ref ⟨0, by decide⟩))
  guarded := fun _ => trivial

theorem negativeCycle_complementary (env : Environment) :
    Complementary (negativeCycle.interpretation env ⟨0, by decide⟩) :=
  interpretation_complementary negativeCycle env (fun _ => trivial) _

theorem negativeCycle_static (env : Environment) :
    Static (negativeCycle.interpretation env ⟨0, by decide⟩) :=
  interpretation_static negativeCycle env (fun _ => trivial) _

end CDotFCCT.CTML.Mixed.ComplementedGhostCodes
