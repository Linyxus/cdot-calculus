import CDotFCCT.CTML.CarrierPackages
import CTMLCore.Language.TypeBlocks

/-! # Moving carrier interfaces under outer type binders -/

set_option autoImplicit false

namespace CDotFCCT.CTML.Transparent.CarrierLayout

open CTMLCore CTMLCore.Syntax

universe u
variable {Label : Type u} [DecidableEq Label]

theorem components_liftAt {depth : Nat} (support entries : List Label)
    (types : Label → WFTy depth) (field : FieldName) (index : Nat) (valid : index ≤ depth) :
    (components support entries types field).liftAt index valid =
      components support entries (fun label => (types label).liftAt index valid) field := by
  induction entries with
  | nil => rfl
  | cons first rest ih =>
      simp only [components]
      split
      · rfl
      · split
        · rfl
        · exact ih

theorem precise_liftAt {depth : Nat} (support : List Label)
    (types : Label → WFTy depth) (index : Nat) (valid : index ≤ depth) :
    (precise support types).liftAt index valid =
      precise support (fun label => (types label).liftAt index valid) := by
  unfold precise
  have commute (fields : List FieldName) :
      (row fields (components support support types)).liftAt index valid =
        row fields (components support support
          (fun label => (types label).liftAt index valid)) := by
    induction fields with
    | nil => rfl
    | cons first rest ih =>
        simpa only [row, WFTy.union, WFTy.liftAt_joint, WFTy.liftAt_record,
          components_liftAt] using congrArg
            (WFTy.union (WFTy.record first (components support support
              (fun label => (types label).liftAt index valid) first))) ih
  exact commute _

theorem bindComponent_liftAt {depth : Nat} (types : Label → WFTy depth)
    (label : Label) (index : Nat) (valid : index ≤ depth) :
    (fun selected => (bindComponent types label selected).liftAt (index + 1) (by omega)) =
      bindComponent (fun selected => (types selected).liftAt index valid) label := by
  funext selected
  by_cases same : selected = label
  · simp only [bindComponent, same, ite_true]
    apply WFTy.eq_of_raw_eq
    simp [WFTy.liftAt, WFTy.var, Ty.liftAt]
  · simp only [bindComponent, same, ite_false]
    exact WFTy.liftAt_weaken valid (types selected)

theorem telescope_liftAt (support : List Label) (payload : Label) (remaining : List Label)
    {depth : Nat} (types : Label → WFTy depth) (view : WFTy depth)
    (index : Nat) (valid : index ≤ depth) :
    (telescope support payload remaining types view).liftAt index valid =
      telescope support payload remaining (fun selected => (types selected).liftAt index valid)
        (view.liftAt index valid) := by
  induction remaining generalizing depth index with
  | nil =>
      simp only [telescope, Interface.liftAt]
      have constraint :
          (WFConstraint.constr (precise support types) view).liftAt index valid =
            WFConstraint.constr
              (precise support (fun selected => (types selected).liftAt index valid))
              (view.liftAt index valid) := by
        exact congrArg (fun sub => WFConstraint.constr sub (view.liftAt index valid))
          (precise_liftAt _ _ _ _)
      rw [constraint]
  | cons label rest ih =>
      simp only [telescope, Interface.liftAt]
      rw [ih, bindComponent_liftAt, WFTy.liftAt_weaken]

theorem interface_liftAt (support : List Label) (payload : Label) {depth : Nat}
    (view : WFTy depth) (index : Nat) (valid : index ≤ depth) :
    (interface support payload view).liftAt index valid =
      interface support payload (view.liftAt index valid) := by
  unfold interface
  rw [telescope_liftAt]
  rfl

theorem consumer_liftAt (support : List Label) (payload : Label) {depth : Nat}
    (view answer : WFTy depth) (index : Nat) (valid : index ≤ depth) :
    ((interface support payload view).consumer answer).liftAt index valid =
      (interface support payload (view.liftAt index valid)).consumer
        (answer.liftAt index valid) := by
  rw [Interface.consumer_liftAt, interface_liftAt]

theorem consumer_weakenBy (support : List Label) (payload : Label) {depth : Nat}
    (view answer : WFTy depth) (amount : Nat) :
    ((interface support payload view).consumer answer).weakenBy amount =
      (interface support payload (view.weakenBy amount)).consumer (answer.weakenBy amount) := by
  induction amount with
  | zero => simp only [WFTy.weakenBy_zero]
  | succ amount ih =>
      rw [WFTy.weakenBy_succ, ih]
      exact (consumer_liftAt support payload _ _ 0 (Nat.zero_le _)).trans
        (congrArg₂ (fun view answer => (interface support payload view).consumer answer)
          (view.weakenBy_succ amount).symm (answer.weakenBy_succ amount).symm)

theorem package_weakenBy (support : List Label) (payload : Label) {depth : Nat}
    (view answer : WFTy depth) (amount : Nat) :
    ((interface support payload view).package answer).weakenBy amount =
      (interface support payload (view.weakenBy amount)).package (answer.weakenBy amount) :=
  congrArg (WFTy.arrow · (answer.weakenBy amount))
    (consumer_weakenBy support payload view answer amount)

end CDotFCCT.CTML.Transparent.CarrierLayout
