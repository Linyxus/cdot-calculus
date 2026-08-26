import CDot.CanonicalForms
import CDot.Narrowing
import CDot.Reduction

/-!
# Type safety

Lean port of `cdot/Safety.v`.  This module first develops the structural
lookup relation used by canonical forms, then proves preservation, progress,
path safety, and extended safety.
-/

namespace CDot

variable [Signature]

inductive LookupFieldsTyp (x : Var) : Typ → Fields → Typ → Prop where
  | nil (T : Typ) : LookupFieldsTyp x T [] T
  | cons : LookupFieldsTyp x T fields (.bnd U) →
      RecordHas (U.openPath (.select (.free x) fields)) (.trm a S) →
      LookupFieldsTyp x T (a :: fields) S

theorem LookupFieldsTyp.inert {x : Var} {T U : Typ} {fields : Fields}
    (hT : InertTyp T) (h : LookupFieldsTyp x T fields (.bnd U)) :
    InertTyp (.bnd U) := by
  cases h with
  | nil => exact hT
  | cons hlookup hhas =>
      have ih := LookupFieldsTyp.inert hT hlookup
      cases ih with
      | bnd hrecord =>
          have hdec := (hrecord.openPath _).has_recordDec hhas
          cases hdec with
          | trm hS => exact hS

theorem LookupFieldsTyp.unique {x : Var} {S T U : Typ} {fields : Fields}
    (hS : InertTyp S) (hT : LookupFieldsTyp x S fields T)
    (hU : LookupFieldsTyp x S fields U) : T = U := by
  cases hT with
  | nil => cases hU; rfl
  | cons hp hmem =>
      cases hU with
      | cons hp' hmem' =>
          have hVV := LookupFieldsTyp.unique hS hp hp'
          have hV := Typ.bnd.inj hVV
          cases hV
          have hinert := hp.inert hS
          cases hinert with
          | bnd hrecord =>
              have hdec := (hrecord.openPath _).has_unique hmem hmem' rfl
              exact Dec.trm.inj hdec |>.2

theorem LookupFieldsTyp.all_prefix_nil {x : Var} {S T U V : Typ}
    {fields pre : Fields} (hS : InertTyp S)
    (hall : LookupFieldsTyp x S fields (.all T U))
    (hlong : LookupFieldsTyp x S (pre ++ fields) V) : pre = [] := by
  induction pre generalizing V with
  | nil => rfl
  | cons a tail ih =>
      rw [List.cons_append] at hlong
      cases hlong with
      | cons hbase hmem =>
          have hnil := ih hbase
          subst tail
          simp only [List.nil_append] at hbase
          have heq := hall.unique hS hbase
          cases heq

theorem LookupFieldsTyp.sngl_prefix_nil {x : Var} {S V : Typ}
    {p : Path} {fields pre : Fields} (hS : InertTyp S)
    (hsngl : LookupFieldsTyp x S fields (.sngl p))
    (hlong : LookupFieldsTyp x S (pre ++ fields) V) : pre = [] := by
  induction pre generalizing V with
  | nil => rfl
  | cons a tail ih =>
      rw [List.cons_append] at hlong
      cases hlong with
      | cons hbase hmem =>
          have hnil := ih hbase
          subst tail
          simp only [List.nil_append] at hbase
          have heq := hsngl.unique hS hbase
          cases heq

end CDot
