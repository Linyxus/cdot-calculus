import CDotFCCT.CTML.CarrierEquationSyntax
import CDotFCCT.CTML.MixedCarrierLayout

/-!
# Correlated carrier slots using Boolean residuals

For a complemented ghost code C, the constraint C ≤ A is equivalent to
Top ≤ ¬C ∪ A. The residual is pure Boolean syntax, so a derived carrier slot
may contain it without putting a recursive constraint beneath a ghost field.
These are derivations in the existing subtyping rules, not additional axioms.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierRelationSlots

open CTMLCore CTMLCore.Syntax

def residual {depth : Nat} (sub sup : WFTy depth) : WFTy depth :=
  WFTy.union (WFTy.neg sub) sup

def complete {depth : Nat} (type : WFTy depth) : WFTy depth :=
  WFTy.union type (WFTy.neg type)

theorem native_noncontradiction {s : SubtypingContext} {type : WFTy s.typeDepth}
    (complemented : Subtype s WFTy.top (complete type)) :
    Subtype s (WFTy.intersection type (WFTy.neg type)) WFTy.bottom :=
  (Subtype.leInter (Subtype.interLeft.trans (Subtype.negDouble .upper)) Subtype.interRight).trans
    ((Subtype.negDeMorgan .union).trans
      ((Subtype.neg (complemented.trans (Subtype.unionLe .leUnionRight .leUnionLeft))).trans
        (Subtype.negInversion (Subtype.leTop.trans (Subtype.negDouble .upper)))))

theorem native_intro {s : SubtypingContext} {sub sup : WFTy s.typeDepth}
    (complemented : Subtype s WFTy.top (complete sub)) (included : Subtype s sub sup) :
    Subtype s WFTy.top (residual sub sup) :=
  complemented.trans (Subtype.unionLe (included.trans .leUnionRight) .leUnionLeft)

theorem native_elim {s : SubtypingContext} {sub sup : WFTy s.typeDepth}
    (complemented : Subtype s WFTy.top (complete sub))
    (asserted : Subtype s WFTy.top (residual sub sup)) : Subtype s sub sup :=
  (Subtype.leInter .refl (Subtype.leTop.trans asserted)).trans
    (Subtype.interDistrib.trans
      (Subtype.unionLe ((native_noncontradiction complemented).trans .botLe) .interRight))

private theorem fromTwo {ghost : FieldName → Bool} {s : SubtypingContext}
    (first second : WFConstraint s.typeDepth) {sub sup : WFTy s.typeDepth}
    (derive : Subtype ⟨s.typeDepth, [first, second]⟩ sub sup)
    (firstProof : InvertingSubtype ghost s first.sub first.sup)
    (secondProof : InvertingSubtype ghost s second.sub second.sup) :
    InvertingSubtype ghost s sub sup :=
  .nativeWith [first, second] derive (fun _ member =>
    (List.mem_cons.mp member).elim (fun equal => equal.symm ▸ firstProof)
      (fun later => (List.mem_singleton.mp later).symm ▸ secondProof))

theorem introResidual {ghost : FieldName → Bool} {s : SubtypingContext}
    {sub sup : WFTy s.typeDepth}
    (complemented : InvertingSubtype ghost s WFTy.top (complete sub))
    (included : InvertingSubtype ghost s sub sup) :
    InvertingSubtype ghost s WFTy.top (residual sub sup) :=
  fromTwo (WFConstraint.constr WFTy.top (complete sub)) (WFConstraint.constr sub sup)
    (native_intro
      (@Subtype.hyp ⟨s.typeDepth, [WFConstraint.constr WFTy.top (complete sub),
        WFConstraint.constr sub sup]⟩ _ List.mem_cons_self)
      (@Subtype.hyp ⟨s.typeDepth, [WFConstraint.constr WFTy.top (complete sub),
        WFConstraint.constr sub sup]⟩ _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    complemented included

theorem elimResidual {ghost : FieldName → Bool} {s : SubtypingContext}
    {sub sup : WFTy s.typeDepth}
    (complemented : InvertingSubtype ghost s WFTy.top (complete sub))
    (asserted : InvertingSubtype ghost s WFTy.top (residual sub sup)) :
    InvertingSubtype ghost s sub sup :=
  fromTwo (WFConstraint.constr WFTy.top (complete sub))
    (WFConstraint.constr WFTy.top (residual sub sup))
    (native_elim
      (@Subtype.hyp ⟨s.typeDepth, [WFConstraint.constr WFTy.top (complete sub),
        WFConstraint.constr WFTy.top (residual sub sup)]⟩ _ List.mem_cons_self)
      (@Subtype.hyp ⟨s.typeDepth, [WFConstraint.constr WFTy.top (complete sub),
        WFConstraint.constr WFTy.top (residual sub sup)]⟩ _
          (List.mem_cons_of_mem _ List.mem_cons_self))) complemented asserted

inductive Label where
  | member
  | child
  | relation
  deriving DecidableEq

def support : List Label := [.member, .child, .relation]

def components {depth : Nat} (member child : WFTy depth) : Label → WFTy depth
  | .member => member
  | .child => child
  | .relation => residual child member

def carrier {depth : Nat} (member child : WFTy depth) : WFTy depth :=
  CarrierLayout.precise support (components member child)

def view {depth : Nat} : WFTy depth :=
  (CarrierLayout.slot support .relation (by decide)).view WFTy.top WFTy.top (fun _ => WFTy.top)

theorem relation_elim {s : SubtypingContext} {member child : WFTy s.typeDepth}
    (complemented : InvertingSubtype carrierPolicy s WFTy.top (complete child))
    (included : InvertingSubtype carrierPolicy s (carrier member child) view) :
    InvertingSubtype carrierPolicy s child member := by
  have precise := CarrierLayout.precise_eq_slot (support := support)
    (label := Label.relation) (by decide) (components member child)
  exact elimResidual complemented
    (memberLowerBound (CarrierLayout.slot support .relation (by decide))
      (carrierPolicy_names support) (.native .refl)
        (precise ▸ (show InvertingSubtype carrierPolicy s
          (CarrierLayout.precise support (components member child)) view from included)))

theorem relation_intro {s : SubtypingContext} {member child : WFTy s.typeDepth}
    (complemented : InvertingSubtype carrierPolicy s WFTy.top (complete child))
    (included : InvertingSubtype carrierPolicy s child member) :
    InvertingSubtype carrierPolicy s (carrier member child) view := by
  rw [carrier, CarrierLayout.precise_eq_slot (label := Label.relation) (by decide)]
  exact memberVariance (CarrierLayout.slot support .relation (by decide))
    (introResidual complemented included) (.native .leTop) (fun _ _ => .native .leTop)

theorem characterizes {s : SubtypingContext} {member child : WFTy s.typeDepth}
    (complemented : InvertingSubtype carrierPolicy s WFTy.top (complete child)) :
    InvertingSubtype carrierPolicy s (carrier member child) view ↔
      InvertingSubtype carrierPolicy s child member :=
  ⟨relation_elim complemented, relation_intro complemented⟩

/-- Derived correlation remains inside the already solved pure grammar. -/
def equationComponents {depth size : Nat}
    (member child : CarrierEquation.Expr carrierPolicy depth size) :
    Label → CarrierEquation.Expr carrierPolicy depth size
  | .member => member
  | .child => child
  | .relation => .union (.neg child) member

def equationBody {depth size : Nat}
    (member child : CarrierEquation.Expr carrierPolicy depth size) :
    CarrierEquation.Expr carrierPolicy depth size :=
  .precise support (carrierPolicy_names support) (equationComponents member child)

theorem equationBody_guarded {depth size : Nat}
    (member child : CarrierEquation.Expr carrierPolicy depth size) :
    (equationBody member child).Guarded :=
  CarrierEquation.Expr.precise_guarded support (carrierPolicy_names support) _

theorem equationBody_compile {depth size : Nat}
    (member child : CarrierEquation.Expr carrierPolicy depth size) :
    (equationBody member child).compile = carrier member.compile child.compile := by
  rw [equationBody, CarrierEquation.Expr.compile_precise]
  exact congrArg (CarrierLayout.precise support)
    (funext (fun label => match label with
      | .member => rfl
      | .child => rfl
      | .relation => rfl))

theorem bottomDiagonal :
    InvertingSubtype carrierPolicy SubtypingContext.empty
      (carrier WFTy.bottom WFTy.bottom) view :=
  relation_intro
    (.native ((Subtype.negInversion
      ((Subtype.negDouble .lower).trans (Subtype.extremum .bottom))).trans .leUnionRight))
    (.native .refl)

theorem topDiagonal :
    InvertingSubtype carrierPolicy SubtypingContext.empty
      (carrier WFTy.top WFTy.top) view :=
  relation_intro (.native .leUnionLeft) (.native .refl)

/-- Computing the residual rules out the crossed tuple that independent slots admitted. -/
theorem rejectsCrossed :
    ¬ InvertingSubtype carrierPolicy SubtypingContext.empty
      (carrier WFTy.bottom WFTy.top) view :=
  fun included => Mixed.noCollapse
    (empty_validates carrierPolicy (fun _ _ => (fun _ => False, fun _ => False)) 0)
    (relation_elim (.native .leUnionLeft) included)

end CDotFCCT.CTML.Mixed.CarrierRelationSlots
