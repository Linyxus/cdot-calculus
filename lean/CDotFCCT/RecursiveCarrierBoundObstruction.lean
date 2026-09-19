import CDotFCCT.CarrierTranslation
import CDotFCCT.CTML.ObservationViews

/-!
# A relational obligation for first-class recursive carrier bounds

A source recursive upper bound can relate two components of the unknown subject:
its child carrier lies below its own abstract member. A fixed upper bound on the
current union-of-labelled-alternatives representation is closed under mixing
components from accepted rows, so that bound alone cannot express this relation.
This concerns the current carrier representation, not all FCCT encodings.
-/

set_option autoImplicit false

namespace CDotFCCT.RecursiveCarrierBoundObstruction

open CDot CTMLCore CTMLCore.Syntax CTML.Mixed CarrierTranslation
open CarrierLayout

section Mixing

universe u
variable {Label : Type u} [DecidableEq Label]

private theorem rowMember {s : SubtypingContext} (labels : List FieldName)
    (types : FieldName → WFTy s.typeDepth) {field : FieldName} (present : field ∈ labels) :
    Subtype s (WFTy.record field (types field)) (row labels types) := by
  induction labels with
  | nil => exact (List.not_mem_nil present).elim
  | cons first rest ih =>
      rcases List.mem_cons.mp present with rfl | later
      · exact .leUnionLeft
      · exact (ih later).trans .leUnionRight

private theorem rowLe {s : SubtypingContext} (labels : List FieldName)
    (types : FieldName → WFTy s.typeDepth) (bound : WFTy s.typeDepth)
    (included : ∀ field ∈ labels, Subtype s (WFTy.record field (types field)) bound) :
    Subtype s (row labels types) bound := by
  induction labels with
  | nil => exact .botLe
  | cons first rest ih =>
      exact .unionLe (included first List.mem_cons_self)
        (ih (fun field present => included field (List.mem_cons_of_mem first present)))

def mix {depth : Nat} (choose : Label → Bool) (left right : Label → WFTy depth) :
    Label → WFTy depth := fun label => if choose label then left label else right label

private theorem components_mix {depth : Nat} (support entries : List Label)
    (choose : Label → Bool) (left right : Label → WFTy depth) (field : FieldName) :
    components support entries (mix choose left right) field =
        components support entries left field ∨
      components support entries (mix choose left right) field =
        components support entries right field := by
  induction entries with
  | nil => exact .inl rfl
  | cons label rest ih =>
      by_cases lower : field = name support label false
      · cases chosen : choose label <;> simp [components, mix, lower, chosen]
      · by_cases upper : field = name support label true
        · cases chosen : choose label <;> simp [components, mix, upper, chosen]
        · simpa only [components, ite_eq_right lower, ite_eq_right upper] using ih

/-- Every mixture of complete component pairs lies below the union of its two original rows. -/
theorem precise_mix {s : SubtypingContext} (support : List Label) (choose : Label → Bool)
    (left right : Label → WFTy s.typeDepth) :
    Subtype s (precise support (mix choose left right))
      (WFTy.union (precise support left) (precise support right)) := by
  apply rowLe
  intro field present
  rcases components_mix support support choose left right field with first | second
  · rw [first]
    exact (rowMember (names support) (components support support left) present).trans .leUnionLeft
  · rw [second]
    exact (rowMember (names support) (components support support right) present).trans .leUnionRight

end Mixing

/-- The closure property holds for every semantic target bound, regardless of its syntax. -/
theorem precise_mix_included {Label : Type*} [DecidableEq Label] {depth : Nat}
    (ghost : FieldName → Bool) (support : List Label) (choose : Label → Bool)
    (left right : Label → WFTy depth) (env : Indexed.Environment)
    (bound : Indexed.Candidate) (n : Nat)
    (leftIncluded : Indexed.Includes (interpret ghost env (precise support left).raw) bound n)
    (rightIncluded : Indexed.Includes (interpret ghost env (precise support right).raw) bound n) :
    Indexed.Includes (interpret ghost env (precise support (mix choose left right)).raw) bound n :=
  (subtype_sound ghost (precise_mix (s := ⟨depth, []⟩) support choose left right) env n
    (fun _ member => nomatch member)).trans (fun k within term =>
      ⟨fun observed => observed.elim (leftIncluded k within term).1
          (rightIncluded k within term).1,
        fun rejected => ⟨(leftIncluded k within term).2 rejected,
          (rightIncluded k within term).2 rejected⟩⟩)

local instance : Signature where
  TypLabel := String
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

/-- The recursive binder scopes over both the member declaration and the field's selection. -/
def recursiveBody : Typ :=
  .and (.rcd (.typ "A" .bot .top))
    (.rcd (.trm "a" (.path (.select (.bound 0) []) "A")))

def recursiveType : Typ := .bnd recursiveBody

def sourceContext : Ctx :=
  [(1, .path (.var 0) "X"), (0, .rcd (.typ "X" .bot recursiveType))]

def abstractMember :
    Core.Typing sourceContext (.var 0) (.rcd (.typ "X" .bot recursiveType)) :=
  .var (.there (by decide) .here)

def subject : Core.Typing sourceContext (.var 1) (.path (.var 0) "X") := .var .here

def recursiveSubject : Core.Typing sourceContext (.var 1) recursiveType :=
  .sub subject (.selHi abstractMember)

/-- Opening an abstract recursive upper bound relates two components of the unknown subject. -/
def dependentField :
    Core.Typing sourceContext (.path ((Path.var 1).selectField "a")) (.path (.var 1) "A") :=
  .newElim (.sub (.recElim recursiveSubject) .andRight)

def abstractSelfMember : Core.Typing sourceContext (.var 1) (.rcd (.typ "A" .bot .top)) :=
  .sub (.recElim recursiveSubject) .andLeft

/-- Reintroducing the field view does not choose or reveal the abstract member's witness. -/
def recoveredView :
    Core.Typing sourceContext (.var 1) (.rcd (.trm "a" (.path (.var 1) "A"))) :=
  .rcdIntro dependentField

theorem dependentField_source :
    CDot.Typed sourceContext (.path ((Path.var 1).selectField "a")) (.path (.var 1) "A") :=
  dependentField.source

def support : List Slot := [.payload, .member "A", .present "a", .child "a"]

def componentsFor (member child : WFTy 0) : Slot → WFTy 0 :=
  fun slot => if slot = .member "A" then member
    else if slot = .child "a" then child else WFTy.top

def chooseMember (slot : Slot) : Bool := slot == .member "A"

theorem mixedComponents :
    mix chooseMember (componentsFor WFTy.bottom WFTy.bottom)
      (componentsFor WFTy.top WFTy.top) = componentsFor WFTy.bottom WFTy.top := by
  funext slot
  by_cases member : slot = .member "A"
  · simp [mix, chooseMember, componentsFor, member]
  · simp [mix, chooseMember, componentsFor, member]

/-- Two legal independent choices already force acceptance of the crossed invalid choice. -/
theorem crossed_included (env : Indexed.Environment) (bound : Indexed.Candidate) (n : Nat)
    (bottom : Indexed.Includes
      (interpret carrierPolicy env (precise support (componentsFor WFTy.bottom WFTy.bottom)).raw)
      bound n)
    (top : Indexed.Includes
      (interpret carrierPolicy env (precise support (componentsFor WFTy.top WFTy.top)).raw)
      bound n) :
    Indexed.Includes
      (interpret carrierPolicy env (precise support (componentsFor WFTy.bottom WFTy.top)).raw)
      bound n := by
  simpa only [mixedComponents] using precise_mix_included carrierPolicy support chooseMember
    (componentsFor WFTy.bottom WFTy.bottom) (componentsFor WFTy.top WFTy.top) env bound n bottom top

/-- The missing relation is between this subject's child and this subject's abstract member. -/
def EncodesRelation (env : Indexed.Environment) (n : Nat) (bound : Indexed.Candidate) : Prop :=
  ∀ member child : WFTy 0,
    Indexed.Includes
        (interpret carrierPolicy env (precise support (componentsFor member child)).raw) bound n ↔
      Indexed.Includes (interpret carrierPolicy env child.raw)
        (interpret carrierPolicy env member.raw) n

/-- No single upper candidate characterizes the relation on the unchanged precise-row layout. -/
theorem no_uniform_bound (env : Indexed.Environment) (n : Nat) :
    ¬ ∃ bound, EncodesRelation env n bound := by
  rintro ⟨bound, encodes⟩
  have bottom := (encodes WFTy.bottom WFTy.bottom).mpr (Indexed.Includes.refl _ n)
  have top := (encodes WFTy.top WFTy.top).mpr (Indexed.Includes.refl _ n)
  have crossed := (encodes WFTy.bottom WFTy.top).mp
    (crossed_included env bound n bottom top)
  exact (crossed 0 (Nat.zero_le n) (.var 0)).1 trivial

/-- A possible derived correlation witness; its components need not choose a canonical member. -/
def assertion {depth : Nat} (guard : WFConstraint depth) : WFTy depth :=
  WFTy.neg (WFTy.constrained guard WFTy.bottom)

/-- Constraint truth can be represented semantically by a computed extra component. -/
theorem assertion_iff {depth : Nat} (ghost : FieldName → Bool) (guard : WFConstraint depth)
    (env : Indexed.Environment) (n : Nat) :
    Indexed.Includes (interpret ghost env (WFTy.top : WFTy depth).raw)
        (interpret ghost env (assertion guard).raw) n ↔
      interpretGuard ghost env guard.raw n := by
  constructor
  · intro included
    exact ((included n (Nat.le_refl n) (.var 0)).1 trivial).1
  · intro holds k within term
    have earlier := interpretGuard_downward ghost guard.raw env within holds
    exact ⟨fun _ => ⟨earlier, trivial⟩,
      fun impossible => impossible k (Nat.le_refl k) earlier⟩

/-- This prototype recovers exactly the cross-component relation when its witness is computed. -/
theorem relation_assertion_iff (member child : WFTy 0) (env : Indexed.Environment) (n : Nat) :
    Indexed.Includes (interpret carrierPolicy env (WFTy.top : WFTy 0).raw)
        (interpret carrierPolicy env (assertion (WFConstraint.constr child member)).raw) n ↔
      Indexed.Includes (interpret carrierPolicy env child.raw)
        (interpret carrierPolicy env member.raw) n :=
  assertion_iff carrierPolicy (WFConstraint.constr child member) env n

/-- Four arbitrary components: payload, abstract member, field presence, and child carrier. -/
def dictionaryComponents {depth : Nat} : Slot → WFTy (depth + 4) :=
  fun slot => if slot = .payload then WFTy.var 3 (by omega)
    else if slot = .member "A" then WFTy.var 2 (by omega)
    else if slot = .present "a" then WFTy.var 1 (by omega)
    else if slot = .child "a" then WFTy.var 0 (by omega) else WFTy.top

def dictionaryMembership {depth : Nat} (abstractType : WFTy depth) :
    WFConstraint (depth + 4) :=
  WFConstraint.constr (precise support dictionaryComponents)
    abstractType.weaken.weaken.weaken.weaken

/-- The member's declared Bottom/Top bounds are automatic; field presence and dependency remain. -/
def dictionarySat {depth : Nat} : WFTy (depth + 4) :=
  WFTy.intersection
    (assertion (WFConstraint.constr WFTy.top (WFTy.var 1 (by omega))))
    (assertion (WFConstraint.constr (WFTy.var 0 (by omega)) (WFTy.var 2 (by omega))))

def dictionaryBody {depth : Nat} (abstractType : WFTy depth) : WFTy (depth + 4) :=
  WFTy.constrained (dictionaryMembership abstractType) dictionarySat

/-- A proposed upper-bound dictionary quantifies witnesses instead of fixing the member A. -/
def dictionary {depth : Nat} (abstractType : WFTy depth) : WFTy depth :=
  WFTy.all (WFTy.all (WFTy.all (WFTy.all (dictionaryBody abstractType))))

def opened (s : SubtypingContext) : SubtypingContext :=
  s.bindType.bindType.bindType.bindType

set_option backward.isDefEq.respectTransparency false in
private theorem dictionary_open {s : SubtypingContext} (abstractType : WFTy s.typeDepth) :
    Subtype (opened s) (dictionary abstractType).weaken.weaken.weaken.weaken
      (dictionaryBody abstractType) := by
  have first := CTML.Coercion.openUniversal (s := s)
    (WFTy.all (WFTy.all (WFTy.all (dictionaryBody abstractType))))
  have second := CTML.Coercion.openUniversal (s := s.bindType)
    (WFTy.all (WFTy.all (dictionaryBody abstractType)))
  have third := CTML.Coercion.openUniversal (s := s.bindType.bindType)
    (WFTy.all (dictionaryBody abstractType))
  have fourth := CTML.Coercion.openUniversal (s := s.bindType.bindType.bindType)
    (dictionaryBody abstractType)
  exact first.weakenType.weakenType.weakenType.trans
    (second.weakenType.weakenType.trans (third.weakenType.trans fourth))

set_option backward.isDefEq.respectTransparency false in
/-- Existing native rules extract SAT for an arbitrary admitted subject, without selecting A. -/
theorem dictionary_extract {s : SubtypingContext} (abstractType : WFTy s.typeDepth)
    (upperDictionary : Subtype s WFTy.top (dictionary abstractType))
    (membership : Subtype (opened s) (dictionaryMembership abstractType).sub
      (dictionaryMembership abstractType).sup) :
    Subtype (opened s) WFTy.top (dictionarySat (depth := s.typeDepth)) :=
  upperDictionary.weakenType.weakenType.weakenType.weakenType.trans
    ((dictionary_open abstractType).trans
      (@Subtype.constrainedLeft (opened s) (dictionaryMembership abstractType)
        (dictionarySat (depth := s.typeDepth)) membership))

/-- The extracted predicate has the intended meaning for arbitrary member and child candidates. -/
theorem dictionary_relation {s : SubtypingContext} (abstractType : WFTy s.typeDepth)
    (upperDictionary : Subtype s WFTy.top (dictionary abstractType))
    (membership : Subtype (opened s) (dictionaryMembership abstractType).sub
      (dictionaryMembership abstractType).sup)
    (env : Indexed.Environment) (n : Nat) (valid : Validates carrierPolicy (opened s) env n) :
    Indexed.Includes (interpret carrierPolicy env (.var 0))
      (interpret carrierPolicy env (.var 2)) n := by
  have asserted := subtype_sound carrierPolicy
    ((dictionary_extract abstractType upperDictionary membership).trans .interRight) env n valid
  exact (assertion_iff carrierPolicy
    (WFConstraint.constr (WFTy.var 0 (by change 0 < s.typeDepth + 4; omega))
      (WFTy.var 2 (by change 2 < s.typeDepth + 4; omega))) env n).mp asserted

end CDotFCCT.RecursiveCarrierBoundObstruction
