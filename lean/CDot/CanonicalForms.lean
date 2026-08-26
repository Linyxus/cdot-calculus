import CDot.GeneralToTight
import CDot.Lookup
import CDot.Substitution

/-!
# Canonical forms and lookup preservation

Lean port of `cdot/CanonicalForms.v`.  This file connects definition typing,
precise path typing, and runtime lookup.  The results are consumed by progress
and preservation in `CDot.Safety`.
-/

namespace CDot

variable [Signature]

def DefRhs.toTrm : DefRhs → Trm
  | .path p => .path p
  | .val v => .val v

theorem TypedDefs.objectTyping {G : Ctx} {x : Var} {fields : Fields}
    {ds : Defs} {T : Typ} {a : Signature.TrmLabel} {rhs : DefRhs} {V : Typ}
    (hdefs : TypedDefs x fields G ds T) (hhas : ds.Has (.trm a rhs))
    (hrecord : RecordHas T (.trm a V)) :
    (∃ U t, rhs = .val (.lambda U t) ∧ Typed G rhs.toTrm V) ∨
    (∃ q A U ds', rhs = .val (.new q A U ds') ∧
      TypedDefs x (a :: fields) G
        (ds'.openPath ((Path.var x).selectFields (a :: fields)))
        (U.openPath ((Path.var x).selectFields (a :: fields))) ∧
      Typed G (.path ((Path.var x).selectFields (a :: fields)))
        ((.path q A : Typ).openPath ((Path.var x).selectFields (a :: fields))) ∧
      V = .bnd U) ∨
    (∃ q S, rhs = .path q ∧ V = .sngl q ∧ Typed G (.path q) S) := by
  obtain ⟨d, hd, htyped⟩ := hdefs.recordHas hrecord
  cases htyped with
  | all ht =>
      have heq := Defs.has_injective hhas hd (by rfl)
      cases heq
      left
      exact ⟨_, _, rfl, ht⟩
  | new p hp htight hbody htag =>
      have heq := Defs.has_injective hhas hd (by rfl)
      cases heq
      right; left
      subst p
      refine ⟨_, _, _, _, rfl, ?_, ?_, rfl⟩
      · simpa [Path.var, Path.selectFields, Path.selectField] using hbody
      · simpa [Path.var, Path.selectFields, Path.selectField] using htag
  | path ht =>
      have heq := Defs.has_injective hhas hd (by rfl)
      cases heq
      right; right
      exact ⟨_, _, rfl, rfl, ht⟩

end CDot
