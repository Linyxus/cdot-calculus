import CDotFCCT.CTML.CarrierEquationSyntax

/-!
# Finite simultaneous pure ghost equations

Every recursive occurrence is beneath a reflective record. At a fixed observation
index, a record inspects only a proper field subterm. Finite unfoldings therefore
stabilize on each finite term, without positivity or an arrow guard.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierEquation

open CTMLCore (WFTy)
open CTMLCore.Syntax CTMLCore.Indexed

variable {ghost : FieldName → Bool} {depth size : Nat}

abbrev Parameters (depth : Nat) := WFTy depth → Candidate

def Expr.denote (parameters : Parameters depth) (selves : Fin size → Candidate) :
    Expr ghost depth size → Candidate
  | .leaf type => parameters type
  | .ref index => selves index
  | .neg body => negative (body.denote parameters selves)
  | .joint kind left right => CTMLCore.Indexed.joint kind (left.denote parameters selves)
      (right.denote parameters selves)
  | .record field _ body => TransparentRecord.record field (body.denote parameters selves)

private def point (candidate : Candidate) (n : Nat) (term : Term) : Prop × Prop :=
  ((candidate n).1 term, (candidate n).2 term)

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

private theorem record_point_congr {left right : Candidate} {n : Nat} (field : FieldName)
    (term : Term)
    (agree : ∀ value, sizeOf value < sizeOf term → point left n value = point right n value) :
    point (TransparentRecord.record field left) n term =
      point (TransparentRecord.record field right) n term := by
  apply Prod.ext <;> apply propext
  · constructor
    · rintro ⟨className, names, fields, value, equal, lookup, observed⟩
      exact ⟨className, names, fields, value, equal, lookup,
        Eq.mp (congrArg Prod.fst (agree value
          (equal.symm ▸ lookup_record_smaller className lookup))) observed⟩
    · rintro ⟨className, names, fields, value, equal, lookup, observed⟩
      exact ⟨className, names, fields, value, equal, lookup,
        Eq.mpr (congrArg Prod.fst (agree value
          (equal.symm ▸ lookup_record_smaller className lookup))) observed⟩
  · constructor
    · intro observed className names fields value equal lookup
      exact Eq.mp (congrArg Prod.snd (agree value
        (equal.symm ▸ lookup_record_smaller className lookup)))
        (observed className names fields value equal lookup)
    · intro observed className names fields value equal lookup
      exact Eq.mpr (congrArg Prod.snd (agree value
        (equal.symm ▸ lookup_record_smaller className lookup)))
        (observed className names fields value equal lookup)

private theorem point_negative_congr {left right : Candidate} {n : Nat} {term : Term}
    (agree : point left n term = point right n term) :
    point (negative left) n term = point (negative right) n term :=
  congrArg (fun observed : Prop × Prop => (observed.2, observed.1)) agree

private theorem point_joint_congr (kind : Joint)
    {left₁ left₂ right₁ right₂ : Candidate} {n : Nat} {term : Term}
    (left : point left₁ n term = point left₂ n term)
    (right : point right₁ n term = point right₂ n term) :
    point (joint kind left₁ right₁) n term = point (joint kind left₂ right₂) n term :=
  match kind with
  | .union => congrArg₂ (fun (a b : Prop × Prop) => (a.1 ∨ b.1, a.2 ∧ b.2)) left right
  | .intersection => congrArg₂ (fun (a b : Prop × Prop) => (a.1 ∧ b.1, a.2 ∨ b.2)) left right

private def Below (bound n : Nat) (left right : Fin size → Candidate) : Prop :=
  ∀ index term, sizeOf term < bound → point (left index) n term = point (right index) n term

private theorem Expr.denote_below (expression : Expr ghost depth size)
    {parameters : Parameters depth} {left right : Fin size → Candidate} {bound n : Nat}
    (agree : Below bound n left right) (term : Term) (small : sizeOf term < bound) :
    point (expression.denote parameters left) n term =
      point (expression.denote parameters right) n term := by
  induction expression generalizing term with
  | leaf => rfl
  | ref index => exact agree index term small
  | neg body ih => exact point_negative_congr (ih term small)
  | joint kind first second ihFirst ihSecond =>
      exact point_joint_congr kind (ihFirst term small) (ihSecond term small)
  | record field marked body ih =>
      exact record_point_congr field term
        (fun value smaller => ih value (Nat.lt_trans smaller small))

private theorem Expr.guarded_below (expression : Expr ghost depth size)
    (guarded : expression.Guarded) {parameters : Parameters depth}
    {left right : Fin size → Candidate} {bound n : Nat} (agree : Below bound n left right)
    (term : Term) (small : sizeOf term ≤ bound) :
    point (expression.denote parameters left) n term =
      point (expression.denote parameters right) n term := by
  induction expression generalizing term with
  | leaf => rfl
  | ref => exact False.elim guarded
  | neg body ih => exact point_negative_congr (ih guarded term small)
  | joint kind first second ihFirst ihSecond =>
      exact point_joint_congr kind (ihFirst guarded.1 term small) (ihSecond guarded.2 term small)
  | record field marked body _ =>
      exact record_point_congr field term (fun value smaller =>
        body.denote_below agree value (Nat.lt_of_lt_of_le smaller small))

def System.approximate (system : System ghost depth size) (parameters : Parameters depth) :
    Nat → Fin size → Candidate
  | 0, _ => fun _ => (fun _ => False, fun _ => False)
  | fuel + 1, index => (system.body index).denote parameters (system.approximate parameters fuel)

/-- Each term observes only the finite unfolding prefix long enough for its proper subterms. -/
def System.solution (system : System ghost depth size) (parameters : Parameters depth)
    (index : Fin size) : Candidate := fun n =>
  (fun term => (system.approximate parameters (sizeOf term + 1) index n).1 term,
   fun term => (system.approximate parameters (sizeOf term + 1) index n).2 term)

private theorem System.approximate_agree (system : System ghost depth size)
    (parameters : Parameters depth) (n fuel extra : Nat) :
    Below fuel n (system.approximate parameters fuel)
      (system.approximate parameters (fuel + extra)) := by
  induction fuel with
  | zero => exact fun _ _ smaller => False.elim (Nat.not_lt_zero _ smaller)
  | succ fuel ih =>
      intro index term small
      simpa only [Nat.succ_add, System.approximate] using
        (system.body index).guarded_below (system.guarded index)
          (parameters := parameters) ih term (by omega)

private theorem System.solution_approximate (system : System ghost depth size)
    (parameters : Parameters depth) (n fuel : Nat) :
    Below fuel n (system.solution parameters) (system.approximate parameters fuel) := by
  intro index term small
  have enough : sizeOf term + 1 ≤ fuel := by omega
  have agree := system.approximate_agree parameters n (sizeOf term + 1)
    (fuel - (sizeOf term + 1)) index term (by omega)
  simpa only [Nat.add_sub_of_le enough, point, System.solution] using agree

theorem System.solution_equation (system : System ghost depth size)
    (parameters : Parameters depth) (index : Fin size) :
    system.solution parameters index =
      (system.body index).denote parameters (system.solution parameters) := by
  funext n
  apply Prod.ext <;> funext term
  · have agree := (system.body index).guarded_below (system.guarded index)
      (parameters := parameters)
      (system.solution_approximate parameters n (sizeOf term)) term (Nat.le_refl _)
    exact (congrArg Prod.fst agree).symm
  · have agree := (system.body index).guarded_below (system.guarded index)
      (parameters := parameters)
      (system.solution_approximate parameters n (sizeOf term)) term (Nat.le_refl _)
    exact (congrArg Prod.snd agree).symm

theorem Expr.denote_downward (expression : Expr ghost depth size)
    {parameters : Parameters depth} {selves : Fin size → Candidate}
    (leaves : ∀ type, Downward (parameters type)) (references : ∀ index, Downward (selves index)) :
    Downward (expression.denote parameters selves) := by
  induction expression with
  | leaf type => exact leaves type
  | ref index => exact references index
  | neg body ih => exact fun m n within term =>
      ⟨(ih m n within term).2, (ih m n within term).1⟩
  | joint kind left right ihLeft ihRight =>
      intro m n within term
      have left := ihLeft m n within term
      have right := ihRight m n within term
      cases kind with
      | union => exact ⟨Or.imp left.1 right.1, And.imp left.2 right.2⟩
      | intersection => exact ⟨And.imp left.1 right.1, Or.imp left.2 right.2⟩
  | record field _ _ ih => exact TransparentRecord.downward ih field

private theorem System.approximate_downward (system : System ghost depth size)
    {parameters : Parameters depth} (leaves : ∀ type, Downward (parameters type)) (fuel : Nat) :
    ∀ index, Downward (system.approximate parameters fuel index) := by
  induction fuel with
  | zero => exact fun _ _ _ _ _ => ⟨id, id⟩
  | succ fuel ih => exact fun index => (system.body index).denote_downward leaves ih

theorem System.solution_downward (system : System ghost depth size)
    {parameters : Parameters depth} (leaves : ∀ type, Downward (parameters type))
    (index : Fin size) : Downward (system.solution parameters index) :=
  fun m n within term =>
    system.approximate_downward leaves (sizeOf term + 1) index m n within term

/-- Pure equations inspect independent leaves only at the current observation index. -/
theorem Expr.denote_congr (expression : Expr ghost depth size)
    {left right : Parameters depth} {leftSelf rightSelf : Fin size → Candidate} {n : Nat}
    (leaves : ∀ type, left type n = right type n)
    (references : ∀ index, leftSelf index n = rightSelf index n) :
    expression.denote left leftSelf n = expression.denote right rightSelf n := by
  induction expression with
  | leaf type => exact leaves type
  | ref index => exact references index
  | neg body ih => exact congrArg Prod.swap ih
  | joint kind first second ihFirst ihSecond =>
      cases kind <;> simp only [denote, CTMLCore.Indexed.joint, ihFirst, ihSecond]
  | record field _ body ih => exact TransparentRecord.congr ih

private theorem System.approximate_congr (system : System ghost depth size)
    {left right : Parameters depth} {n : Nat} (leaves : ∀ type, left type n = right type n)
    (fuel : Nat) : ∀ index,
    system.approximate left fuel index n = system.approximate right fuel index n := by
  induction fuel with
  | zero => exact fun _ => rfl
  | succ fuel ih => exact fun index => (system.body index).denote_congr leaves ih

theorem System.solution_congr (system : System ghost depth size)
    {left right : Parameters depth} {n : Nat} (leaves : ∀ type, left type n = right type n)
    (index : Fin size) : system.solution left index n = system.solution right index n := by
  apply Prod.ext <;> funext term
  · simpa only [System.solution] using congrArg (fun observed : Observation => observed.1 term)
      (system.approximate_congr leaves (sizeOf term + 1) index)
  · simpa only [System.solution] using congrArg (fun observed : Observation => observed.2 term)
      (system.approximate_congr leaves (sizeOf term + 1) index)

theorem System.solution_agree (system : System ghost depth size)
    {left right : Parameters depth} {n : Nat}
    (leaves : ∀ type, Agree n (left type) (right type)) (index : Fin size) :
    Agree n (system.solution left index) (system.solution right index) :=
  fun k within => system.solution_congr (fun type => leaves type k within) index

end CDotFCCT.CTML.Mixed.CarrierEquation
