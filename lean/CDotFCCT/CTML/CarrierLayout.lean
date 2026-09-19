import CDotFCCT.CTML.CarrierBounds

/-!
# Allocating paired carrier slots from finite source-label support

Source type labels need no global embedding into strings. The finite support
determines one lower slot and one upper slot per member label. All carrier views
use this same allocation, independently of their witness types or source paths.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Transparent.CarrierLayout

open CTMLCore CTMLCore.Syntax

def code (index : Nat) (upper : Bool) : FieldName :=
  String.ofList (List.replicate (2 * index + if upper then 1 else 0) 'm')

theorem code_injective {left right : Nat} {leftUpper rightUpper : Bool}
    (equal : code left leftUpper = code right rightUpper) :
    left = right ∧ leftUpper = rightUpper := by
  have lengths := congrArg String.length equal
  simp only [code, String.length_ofList, List.length_replicate] at lengths
  cases leftUpper <;> cases rightUpper <;> simp_all <;> omega

universe u
variable {Label : Type u} [DecidableEq Label]

def name (support : List Label) (label : Label) (upper : Bool) : FieldName :=
  code (support.idxOf label) upper

theorem name_injective {support : List Label} {left right : Label}
    {leftUpper rightUpper : Bool} (present : left ∈ support)
    (equal : name support left leftUpper = name support right rightUpper) :
    left = right ∧ leftUpper = rightUpper :=
  let same := code_injective equal
  ⟨(List.idxOf_inj present).mp same.1, same.2⟩

def names (support : List Label) : List FieldName :=
  support.flatMap (fun label => [name support label false, name support label true])

theorem name_present {support : List Label} {label : Label}
    (present : label ∈ support) (upper : Bool) : name support label upper ∈ names support :=
  List.mem_flatMap.mpr ⟨label, present, by cases upper <;> simp⟩

def slot (support : List Label) (label : Label) (present : label ∈ support) :
    MemberSlot (names support) :=
  ⟨name support label false, name support label true,
    fun equal => Bool.noConfusion (name_injective present equal).2,
    name_present present false, name_present present true⟩

theorem slot_congr {support : List Label} {left right : Label} (equal : left = right)
    (leftPresent : left ∈ support) (rightPresent : right ∈ support) :
    slot support left leftPresent = slot support right rightPresent := by
  subst right
  rfl

theorem distinctSides (support : List Label) (left right : Label) :
    name support left false ≠ name support right true :=
  fun equal => Bool.noConfusion (code_injective equal).2

def components {depth : Nat} (support : List Label) (entries : List Label)
    (types : Label → WFTy depth) (field : FieldName) : WFTy depth :=
  match entries with
  | [] => WFTy.top
  | label :: rest =>
      if field = name support label false then WFTy.neg (types label)
      else if field = name support label true then types label
      else components support rest types field

theorem components_at {depth : Nat} {support entries : List Label} {label : Label}
    (present : label ∈ support) (entry : label ∈ entries) (types : Label → WFTy depth)
    (upper : Bool) : components support entries types (name support label upper) =
      if upper then types label else WFTy.neg (types label) := by
  induction entries with
  | nil => exact (List.not_mem_nil entry).elim
  | cons first rest ih =>
      by_cases same : label = first
      · subst first
        cases upper with
        | false => simp [components]
        | true => simp [components, Ne.symm (distinctSides support label label)]
      · simpa [components,
          show name support label upper ≠ name support first false from
            fun equal => same (name_injective present equal).1,
          show name support label upper ≠ name support first true from
            fun equal => same (name_injective present equal).1] using
          ih (List.mem_of_ne_of_mem same entry)

def precise {depth : Nat} (support : List Label) (types : Label → WFTy depth) : WFTy depth :=
  row (names support) (components support support types)

theorem components_eq_slot {depth : Nat} {support : List Label} {label : Label}
    (present : label ∈ support) (types : Label → WFTy depth) :
    components support support types = (slot support label present).components
      (types label) (types label) (components support support types) := by
  funext field
  by_cases atLower : field = name support label false
  · simp [MemberSlot.components, slot, atLower, components_at present present types false]
  · by_cases atUpper : field = name support label true
    · simp [MemberSlot.components, slot, atUpper, components_at present present types true,
        Ne.symm (distinctSides support label label)]
    · simp [MemberSlot.components, slot, atLower, atUpper]

theorem precise_eq_slot {depth : Nat} {support : List Label} {label : Label}
    (present : label ∈ support) (types : Label → WFTy depth) :
    precise support types = (slot support label present).precise (types label)
      (components support support types) :=
  congrArg (row (names support)) (components_eq_slot present types)

theorem precise_bounds {s : SubtypingContext} {support : List Label} {label : Label}
    (present : label ∈ support) {left right : Label → WFTy s.typeDepth}
    (included : InvertingSubtype s (precise support left) (precise support right)) :
    InvertingSubtype s (left label) (right label) ∧
      InvertingSubtype s (right label) (left label) := by
  have atSlot := (precise_eq_slot present left) ▸
    (precise_eq_slot present right) ▸ included
  exact ⟨(slot support label present).upperBound (.native .refl) atSlot,
    (slot support label present).lowerBound (.native .refl) atSlot⟩
theorem precise_symmetric {s : SubtypingContext} {support : List Label}
    {left right : Label → WFTy s.typeDepth}
    (included : InvertingSubtype s (precise support left) (precise support right)) :
    InvertingSubtype s (precise support right) (precise support left) := by
  refine InvertingSubtype.rowMono (names support) (fun field member => ?_)
  obtain ⟨label, present, found⟩ := List.mem_flatMap.mp member
  rcases List.mem_cons.mp found with rfl | found
  · simpa only [components_at present present, Bool.false_eq_true, ite_false] using
      (precise_bounds present included).1.neg
  · obtain rfl := List.mem_singleton.mp found
    simpa only [components_at present present, ite_true] using
      (precise_bounds present included).2

end CDotFCCT.CTML.Transparent.CarrierLayout
