import CDotFCCT.CTML.OptionalProductObstruction

/-!
# Optional product carriers with complemented ghost witnesses

The existing guard `Top ≤ A ∪ ¬A` excludes gaps and contradictions in both
observations of A. Restricting type-code witnesses by this guard repairs the
uniform relational optional-product bound. Runtime payloads are not restricted.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.ComplementedProduct

open CTMLCore (WFTy WFConstraint)
open CTMLCore.Syntax CTMLCore.Indexed OptionalProduct

def Complemented (candidate : Candidate) (n : Nat) : Prop :=
  Includes top (joint .union candidate (negative candidate)) n

def bound : Candidate :=
  existential (fun child => existential (fun member =>
    requireGuard (Complemented member) (requireGuard (Complemented child)
      (requireGuard (Includes child member) (product member child)))))

private theorem observes_at {field : FieldName} {payload : Term → Prop}
    {className : ClassName} {names : List FieldName} {fields : TermFields names}
    {value : Term} (lookup : TermFields.Lookup fields field value) :
    TransparentRecord.observes field payload (.record className fields) ↔ payload value := by
  constructor
  · rintro ⟨otherClass, otherNames, otherFields, otherValue, equal, otherLookup, observed⟩
    cases equal
    exact lookup.deterministic otherLookup ▸ observed
  · exact fun observed => ⟨className, names, fields, value, rfl, lookup, observed⟩

private theorem optional_wrapped (candidate : Candidate) (n : Nat) (value : Term) :
    (optional candidate n).1 (TransparentRecord.singleton "value" value) ↔
      (candidate n).1 value := by
  constructor
  · intro observed
    rcases observed with ⟨names, fields, equal⟩ | observed
    · simp [TransparentRecord.singleton] at equal
    · exact TransparentRecord.observes_singleton.mp observed
  · exact fun observed => .inr (TransparentRecord.observes_singleton.mpr observed)

private def witnessFields (value : Term) :
    TermFields ["member+", "member-", "child+", "child-"] :=
  .cons "member+" (.record "Unit" .nil)
    (.cons "member-" (TransparentRecord.singleton "value" value)
      (.cons "child+" (TransparentRecord.singleton "value" value)
        (.cons "child-" (.record "Unit" .nil) .nil (by decide)) (by decide))
      (by decide)) (by decide)

def witnessTerm (value : Term) : Term := .record "Product" (witnessFields value)

private theorem witness_positive (member child : Candidate) (n : Nat) (value : Term) :
    (product member child n).1 (witnessTerm value) ↔
      (member n).2 value ∧ (child n).1 value := by
  constructor
  · intro observed
    exact ⟨(optional_wrapped (negative member) n value).mp
        ((observes_at (.there .here)).mp observed.1.2),
      (optional_wrapped child n value).mp
        ((observes_at (.there (.there .here))).mp observed.2.1)⟩
  · rintro ⟨memberNegative, childPositive⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (observes_at .here).mpr (.inl ⟨[], .nil, rfl⟩)
    · exact (observes_at (.there .here)).mpr
        ((optional_wrapped (negative member) n value).mpr memberNegative)
    · exact (observes_at (.there (.there .here))).mpr
        ((optional_wrapped child n value).mpr childPositive)
    · exact (observes_at (.there (.there (.there .here)))).mpr (.inl ⟨[], .nil, rfl⟩)

/-- The existential bound forbids one term being negative in A and positive in C. -/
theorem excludes_cross {member child : Candidate} {n k : Nat}
    (included : Includes (product member child) bound n) (within : k ≤ n) (value : Term)
    (memberNegative : (member k).2 value) (childPositive : (child k).1 value) : False := by
  obtain ⟨otherChild, otherMember, complete, _, relation, observed⟩ :=
    (included k within (witnessTerm value)).1
      ((witness_positive member child k value).mpr ⟨memberNegative, childPositive⟩)
  have parts := (witness_positive _ _ k value).mp observed
  exact (complete k (Nat.le_refl k) value).2
    ⟨parts.1, (relation k (Nat.le_refl k) value).1 parts.2⟩

/-- Total observations suffice for reflection; the guards also guarantee consistency. -/
theorem reflects {member child : Candidate} {n : Nat}
    (members : Complemented member n) (children : Complemented child n)
    (included : Includes (product member child) bound n) : Includes child member n := by
  intro k within value
  constructor
  · intro observed
    rcases (members k within value).1 trivial with positive | negative
    · exact positive
    · exact (excludes_cross included within value negative observed).elim
  · intro observed
    rcases (children k within value).1 trivial with positive | negative
    · exact (excludes_cross included within value observed positive).elim
    · exact negative

theorem accepts {member child : Candidate} {n : Nat}
    (memberClosed : Downward member) (childClosed : Downward child)
    (members : Complemented member n) (children : Complemented child n)
    (relation : Includes child member n) : Includes (product member child) bound n := by
  intro k within value
  constructor
  · intro observed
    refine ⟨child, member, ?_⟩
    simpa only [prefixClosure_eq memberClosed, prefixClosure_eq childClosed,
      negative, requireGuard, constrained, Complemented] using
      And.intro (members.below within)
        (And.intro (children.below within) (And.intro (relation.below within) observed))
  · intro rejected
    have chosen := rejected child member
    simp only [prefixClosure_eq memberClosed, prefixClosure_eq childClosed,
      negative, requireGuard, constrained] at chosen
    exact chosen k (Nat.le_refl k) (members.below within)
      k (Nat.le_refl k) (children.below within) k (Nat.le_refl k) (relation.below within)

/-- One uniform scalar upper candidate now characterizes the desired relation. -/
theorem characterizes {member child : Candidate} {n : Nat}
    (memberClosed : Downward member) (childClosed : Downward child)
    (members : Complemented member n) (children : Complemented child n) :
    Includes (product member child) bound n ↔ Includes child member n :=
  ⟨reflects members children, accepts memberClosed childClosed members children⟩

def complementGuard {depth : Nat} (type : WFTy depth) : WFConstraint depth :=
  WFConstraint.constr WFTy.top (WFTy.union type (WFTy.neg type))

theorem interpret_complementGuard {depth : Nat} (ghost : FieldName → Bool)
    (env : Environment) (type : WFTy depth) (n : Nat) :
    interpretGuard ghost env (complementGuard type).raw n =
      Complemented (interpret ghost env type.raw) n := rfl

def boundTy : WFTy 0 :=
  existentialTy (existentialTy
    (requireGuardTy (complementGuard (WFTy.var 0 (by decide)))
      (requireGuardTy (complementGuard (WFTy.var 1 (by decide)))
        (requireGuardTy
          (WFConstraint.constr (WFTy.var 1 (by decide)) (WFTy.var 0 (by decide)))
          (productTy (WFTy.var 0 (by decide)) (WFTy.var 1 (by decide)))))))

/-- The repaired upper candidate uses only existing universals, negation, and constraints. -/
theorem interpret_boundTy (env : Environment) :
    interpret (fun _ => true) env boundTy.raw = bound := rfl

/-- The uniform characterization applies to actual type interpretations under actual guards. -/
theorem guarded_type_characterizes {depth : Nat} (env : Environment)
    (member child : WFTy depth) (n : Nat)
    (members : interpretGuard (fun _ => true) env (complementGuard member).raw n)
    (children : interpretGuard (fun _ => true) env (complementGuard child).raw n) :
    Includes (interpret (fun _ => true) env (productTy member child).raw)
        (interpret (fun _ => true) env boundTy.raw) n ↔
      interpretGuard (fun _ => true) env (WFConstraint.constr child member).raw n := by
  simpa only [interpret_product, interpret_boundTy, interpretGuard, WFConstraint.constr] using
    characterizes (interpret_downward (fun _ => true) member.raw env)
      (interpret_downward (fun _ => true) child.raw env) members children

end CDotFCCT.CTML.Mixed.ComplementedProduct
