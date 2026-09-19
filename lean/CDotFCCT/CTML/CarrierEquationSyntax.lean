import CDotFCCT.CTML.MixedCarrierLayout

/-!
# Finite pure carrier equations

Outer types may use the complete target syntax, but cannot mention the new
recursive block. Recursive references are exposed only through Boolean operations
and reflective records. `Guarded` requires a record on every path to a recursive
reference. This module defines syntax and compilation, without a recursion rule.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierEquation

open CTMLCore CTMLCore.Syntax

/-- The pure part of a carrier equation, with an independent outer type at each leaf. -/
inductive Expr (ghost : FieldName → Bool) (depth size : Nat) where
  | leaf : WFTy depth → Expr ghost depth size
  | ref : Fin size → Expr ghost depth size
  | neg : Expr ghost depth size → Expr ghost depth size
  | joint : Joint → Expr ghost depth size → Expr ghost depth size → Expr ghost depth size
  | record (field : FieldName) : ghost field = true →
      Expr ghost depth size → Expr ghost depth size

namespace Expr

variable {ghost : FieldName → Bool} {depth size : Nat}

universe u

def union (left right : Expr ghost depth size) : Expr ghost depth size :=
  .joint .union left right

def intersection (left right : Expr ghost depth size) : Expr ghost depth size :=
  .joint .intersection left right

/-- Every recursive reference lies below a reflective record constructor. -/
def Guarded : Expr ghost depth size → Prop
  | .leaf _ => True
  | .ref _ => False
  | .neg body => body.Guarded
  | .joint _ left right => left.Guarded ∧ right.Guarded
  | .record _ _ _ => True

/-- Component zero names de Bruijn variable zero; outer variables skip the entire block. -/
def compile : Expr ghost depth size → WFTy (depth + size)
  | .leaf type => type.weakenBy size
  | .ref index => WFTy.var index (Nat.lt_of_lt_of_le index.isLt (Nat.le_add_left _ _))
  | .neg body => WFTy.neg body.compile
  | .joint kind left right => WFTy.joint kind left.compile right.compile
  | .record field _ body => WFTy.record field body.compile

@[simp] theorem compile_leaf (type : WFTy depth) :
    (Expr.leaf type : Expr ghost depth size).compile = type.weakenBy size := rfl

@[simp] theorem compile_ref (index : Fin size) :
    (Expr.ref index : Expr ghost depth size).compile =
      WFTy.var index (Nat.lt_of_lt_of_le index.isLt (Nat.le_add_left _ _)) := rfl

/-- Ghost carrier rows retain the existing union-of-labelled-alternatives syntax. -/
def row (labels : List FieldName) (marked : ∀ field ∈ labels, ghost field = true)
    (entries : FieldName → Expr ghost depth size) : Expr ghost depth size :=
  match labels with
  | [] => .leaf WFTy.bottom
  | field :: rest => .union (.record field (marked field List.mem_cons_self) (entries field))
      (row rest (fun found member => marked found (List.mem_cons_of_mem field member)) entries)

theorem row_guarded (labels : List FieldName)
    (marked : ∀ field ∈ labels, ghost field = true) (entries : FieldName → Expr ghost depth size) :
    (row labels marked entries).Guarded :=
  match labels with
  | [] => trivial
  | field :: rest => ⟨trivial,
      row_guarded rest (fun found member => marked found (List.mem_cons_of_mem field member))
        entries⟩

theorem compile_row (labels : List FieldName)
    (marked : ∀ field ∈ labels, ghost field = true) (entries : FieldName → Expr ghost depth size) :
    (row labels marked entries).compile =
      Mixed.row labels (fun field => (entries field).compile) :=
  match labels with
  | [] => rfl
  | field :: rest => congrArg (WFTy.union (WFTy.record field (entries field).compile))
      (compile_row rest (fun found member => marked found (List.mem_cons_of_mem field member))
        entries)

/-- The existing paired-slot member view, before compiling the recursive references. -/
def view {labels : List FieldName} (slot : Transparent.MemberSlot labels)
    (marked : ∀ field ∈ labels, ghost field = true)
    (lower upper : Expr ghost depth size) (rest : FieldName → Expr ghost depth size) :
    Expr ghost depth size :=
  row labels marked (fun field =>
    if field = slot.lower then .neg lower else if field = slot.upper then upper else rest field)

theorem view_guarded {labels : List FieldName} (slot : Transparent.MemberSlot labels)
    (marked : ∀ field ∈ labels, ghost field = true)
    (lower upper : Expr ghost depth size) (rest : FieldName → Expr ghost depth size) :
    (view slot marked lower upper rest).Guarded := row_guarded _ _ _

theorem compile_view {labels : List FieldName} (slot : Transparent.MemberSlot labels)
    (marked : ∀ field ∈ labels, ghost field = true)
    (lower upper : Expr ghost depth size) (rest : FieldName → Expr ghost depth size) :
    (view slot marked lower upper rest).compile =
      slot.view lower.compile upper.compile (fun field => (rest field).compile) := by
  rw [view, compile_row]
  apply congrArg (Mixed.row labels)
  funext field
  by_cases atLower : field = slot.lower <;> by_cases atUpper : field = slot.upper <;>
    simp [Transparent.MemberSlot.components, atLower, atUpper, Ne.symm slot.different, compile]

/-- The expression counterpart of the existing finite precise-carrier components. -/
def components {Label : Type u} [DecidableEq Label] (support entries : List Label)
    (types : Label → Expr ghost depth size) (field : FieldName) : Expr ghost depth size :=
  match entries with
  | [] => .leaf WFTy.top
  | label :: rest =>
      if field = CarrierLayout.name support label false then .neg (types label)
      else if field = CarrierLayout.name support label true then types label
      else components support rest types field

theorem compile_components {Label : Type u} [DecidableEq Label] (support entries : List Label)
    (types : Label → Expr ghost depth size) (field : FieldName) :
    (components support entries types field).compile =
      CarrierLayout.components support entries (fun label => (types label).compile) field := by
  induction entries with
  | nil => rfl
  | cons label rest ih =>
      simp only [components, CarrierLayout.components]
      split
      · rfl
      · split
        · rfl
        · exact ih

/-- Precise carriers can contain an arbitrary finite vector of recursive references. -/
def precise {Label : Type u} [DecidableEq Label] (support : List Label)
    (marked : ∀ field ∈ CarrierLayout.names support, ghost field = true)
    (types : Label → Expr ghost depth size) : Expr ghost depth size :=
  row (CarrierLayout.names support) marked (components support support types)

theorem precise_guarded {Label : Type u} [DecidableEq Label] (support : List Label)
    (marked : ∀ field ∈ CarrierLayout.names support, ghost field = true)
    (types : Label → Expr ghost depth size) : (precise support marked types).Guarded :=
  row_guarded _ _ _

theorem compile_precise {Label : Type u} [DecidableEq Label] (support : List Label)
    (marked : ∀ field ∈ CarrierLayout.names support, ghost field = true)
    (types : Label → Expr ghost depth size) :
    (precise support marked types).compile =
      CarrierLayout.precise support (fun label => (types label).compile) :=
  (compile_row _ _ _).trans (congrArg (Mixed.row (CarrierLayout.names support))
    (funext (compile_components support support types)))

/-- The whole-child equation for `a = self`, retaining every other outer component. -/
def wholeChild {Label : Type u} [DecidableEq Label] (support : List Label)
    (marked : ∀ field ∈ CarrierLayout.names support, ghost field = true)
    (child : Label) (self : Fin size) (parameters : Label → WFTy depth) : Expr ghost depth size :=
  precise support marked
    (fun label => if label = child then .ref self else .leaf (parameters label))

theorem wholeChild_guarded {Label : Type u} [DecidableEq Label] (support : List Label)
    (marked : ∀ field ∈ CarrierLayout.names support, ghost field = true)
    (child : Label) (self : Fin size) (parameters : Label → WFTy depth) :
    (wholeChild support marked child self parameters).Guarded := precise_guarded _ _ _

theorem compile_wholeChild {Label : Type u} [DecidableEq Label] (support : List Label)
    (marked : ∀ field ∈ CarrierLayout.names support, ghost field = true)
    (child : Label) (self : Fin size) (parameters : Label → WFTy depth) :
    (wholeChild support marked child self parameters).compile =
      CarrierLayout.precise support (fun label => if label = child then
        WFTy.var self (Nat.lt_of_lt_of_le self.isLt (Nat.le_add_left _ _))
        else (parameters label).weakenBy size) := by
  rw [wholeChild, compile_precise]
  apply congrArg (CarrierLayout.precise support)
  funext label
  split <;> rfl

/-- The recursive member body `A = {a : self.A}` uses one whole-child upper slot. -/
def fieldSelf {labels : List FieldName} (slot : Transparent.MemberSlot labels)
    (marked : ∀ field ∈ labels, ghost field = true) (self : Fin size) : Expr ghost depth size :=
  view slot marked (.leaf WFTy.bottom) (.ref self) (fun _ => .leaf WFTy.top)

theorem fieldSelf_guarded {labels : List FieldName} (slot : Transparent.MemberSlot labels)
    (marked : ∀ field ∈ labels, ghost field = true) (self : Fin size) :
    (fieldSelf (depth := depth) slot marked self).Guarded := view_guarded _ _ _ _ _

theorem compile_fieldSelf {labels : List FieldName} (slot : Transparent.MemberSlot labels)
    (marked : ∀ field ∈ labels, ghost field = true) (self : Fin size) :
    (fieldSelf (depth := depth) slot marked self).compile =
      slot.view WFTy.bottom
        (WFTy.var self (Nat.lt_of_lt_of_le self.isLt (Nat.le_add_left _ _))) (fun _ => WFTy.top) :=
  compile_view _ _ _ _ _

/-- The recursive member body `A = {X : self.A .. self.A}` retains both polarities. -/
def memberSelf {labels : List FieldName} (slot : Transparent.MemberSlot labels)
    (marked : ∀ field ∈ labels, ghost field = true) (self : Fin size) : Expr ghost depth size :=
  view slot marked (.ref self) (.ref self) (fun _ => .leaf WFTy.top)

theorem memberSelf_guarded {labels : List FieldName} (slot : Transparent.MemberSlot labels)
    (marked : ∀ field ∈ labels, ghost field = true) (self : Fin size) :
    (memberSelf (depth := depth) slot marked self).Guarded := view_guarded _ _ _ _ _

theorem compile_memberSelf {labels : List FieldName} (slot : Transparent.MemberSlot labels)
    (marked : ∀ field ∈ labels, ghost field = true) (self : Fin size) :
    (memberSelf (depth := depth) slot marked self).compile =
      slot.view (WFTy.var self (Nat.lt_of_lt_of_le self.isLt (Nat.le_add_left _ _)))
        (WFTy.var self (Nat.lt_of_lt_of_le self.isLt (Nat.le_add_left _ _))) (fun _ => WFTy.top) :=
  compile_view _ _ _ _ _

/-- Direct recursive aliases remain an explicit obligation outside this guarded grammar. -/
theorem ref_not_guarded (index : Fin size) : ¬ (Expr.ref index : Expr ghost depth size).Guarded :=
  id

end Expr

/-- A finite block of mutually recursive pure carrier equations. -/
structure System (ghost : FieldName → Bool) (depth size : Nat) where
  body : Fin size → Expr ghost depth size
  guarded : ∀ index, (body index).Guarded

def System.compile {ghost : FieldName → Bool} {depth size : Nat}
    (system : System ghost depth size) (index : Fin size) : WFTy (depth + size) :=
  (system.body index).compile

end CDotFCCT.CTML.Mixed.CarrierEquation
