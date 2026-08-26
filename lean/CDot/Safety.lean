import CDot.CanonicalForms
import CDot.ContextTransport
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

theorem TypedDefs.singletonRhsTyped {x : Var} {fields : Fields} {G : Ctx}
    {ds : Defs} {T : Typ} {a : Signature.TrmLabel} {q : Path}
    (hdefs : TypedDefs x fields G ds T)
    (hhas : RecordHas T (.trm a (.sngl q))) :
    ∃ U, Typed G (.path q) U := by
  obtain ⟨d, hd, htyped⟩ := hdefs.recordHas hhas
  cases htyped with
  | path hq => exact ⟨_, hq⟩

theorem LookupFieldsTyp.defsTyping {extra : Fields} {z : Var}
    {fields : Fields} {G : Ctx} {ds : Defs} {T S U : Typ}
    (hdefs : TypedDefs z fields G ds
      (T.openPath (.select (.free z) fields)))
    (hS : InertTyp S)
    (hbase : LookupFieldsTyp z S fields (.bnd T))
    (hlong : LookupFieldsTyp z S (extra ++ fields) (.bnd U)) :
    ∃ ds', TypedDefs z (extra ++ fields) G ds'
      (U.openPath (.select (.free z) (extra ++ fields))) := by
  induction extra generalizing U with
  | nil =>
      simp only [List.nil_append] at hlong ⊢
      have heq := hbase.unique hS hlong
      have hTU := Typ.bnd.inj heq
      subst U
      exact ⟨ds, hdefs⟩
  | cons a tail ih =>
      rw [List.cons_append] at hlong
      cases hlong with
      | cons hprefix hmember =>
          obtain ⟨ds', hds'⟩ := ih hprefix
          obtain ⟨d, hd, htyped⟩ := hds'.recordHas hmember
          cases htyped with
          | new p hp htight hnested htag =>
              subst p
              exact ⟨_, by
                simpa only [List.cons_append, Path.selectField] using hnested⟩

theorem PreciseFlow.sourceLookup {G : Ctx} {x : Var} {S T U : Typ}
    {fields : Fields} (hi : Inert G) (hb : Env.Binds x S G)
    (h : PreciseFlow G (.select (.free x) fields) T U) :
    LookupFieldsTyp x S fields T := by
  induction fields generalizing T U with
  | nil =>
      have hb' : Env.Binds x T G := by
        apply PreciseFlow.binds_of_var
        simpa only [Path.var] using h
      have heq := hb.functional hb'
      subst T
      exact .nil S
  | cons a tail ih =>
      change PreciseFlow G ((Path.select (.free x) tail).selectField a) T U at h
      obtain ⟨R, hprefix⟩ := h.backtrackRecord
      obtain ⟨V, rfl⟩ := hprefix.recordSource_bnd hi
      exact .cons (ih hprefix) (hprefix.recordHas_of_bnd hi .one)

theorem PreciseVal.newDefsAt {G : Ctx} {r : Path}
    {A : Signature.TypLabel} {T : Typ} {ds : Defs} {x : Var}
    (h : PreciseVal G (.new r A T ds) (.bnd T))
    (hi : Inert G) (hxG : Env.Fresh x G) :
    TypedDefs x [] (G.push x (.bnd T)) (ds.open x) (T.open x) := by
  cases h with
  | newIntro L hdefs hself =>
      let avoid := L ∪ G.dom ∪ G.fvTypes ∪ T.fv ∪ ds.fv ∪ {x}
      obtain ⟨z, hzrange⟩ := Finset.exists_nat_subset_range avoid
      have hz : z ∉ avoid := by
        intro hmem
        exact (Nat.lt_irrefl z) (Finset.mem_range.mp (hzrange hmem))
      have hzL : z ∉ L := by aesop
      have hzG : Env.Fresh z G := by aesop
      have hzTypes : z ∉ G.fvTypes := by aesop
      have hzT : z ∉ T.fv := by aesop
      have hzds : z ∉ ds.fv := by aesop
      have hzx : z ≠ x := by aesop
      have hzPush : Env.Fresh z (G.push x ((T.open z).subst z (.var x))) := by
        intro hmem
        simp only [Env.dom, Env.push, List.map_cons, List.mem_toFinset,
          List.mem_cons] at hmem
        rcases hmem with hzx' | hmem
        · exact hzx hzx'
        · exact hzG (by
            simpa only [Env.dom, List.mem_toFinset] using hmem)
      have hokx : Env.Ok (G.push x ((T.open z).subst z (.var x))) :=
        Env.okPush hi.ok hxG
      have hren := (hdefs z hzL).renameSelf hzTypes hxG hzx
        (Env.okPush hokx hzPush)
      have hnamed : (Path.var x).Named := ⟨x, rfl⟩
      have hTopen := Typ.openPath_eq_subst_open_of_fresh T hzT hnamed
      have hdsopen := Defs.openPath_eq_subst_open_of_fresh ds hzds hnamed
      simp only [Typ.openRec_eq_openRecPath_var] at hTopen
      simp only [Defs.openRec_eq_openRecPath_var] at hdsopen
      simp only [Typ.openRec_eq_openRecPath_var,
        Defs.openRec_eq_openRecPath_var] at hren
      rw [← hTopen, ← hdsopen] at hren
      have hren' : TypedDefs x [] (G.push x (T.open x))
          (ds.open x) (T.open x) := by
        simpa only [Typ.openRec_eq_openRecPath_var,
          Defs.openRec_eq_openRecPath_var] using hren
      exact hren'.openSelfContext (Env.okPush hi.ok hxG)

theorem PreciseVal.wfPush {G : Ctx} {v : Val} {T : Typ} {x : Var}
    (h : PreciseVal G v T) (hi : Inert G) (hwf : Wf G)
    (hxG : Env.Fresh x G) : Wf (G.push x T) := by
  cases h with
  | @allIntro G S body U L hbody =>
      refine .push hwf hxG ?_
      intro fields q hflow
      have hi' : Inert (G.push x (.all S U)) := .push hi .all hxG
      have hlookup := hflow.sourceLookup hi' (Env.Binds.here)
      have hlookup' : LookupFieldsTyp x (.all S U) (fields ++ []) (.sngl q) := by
        simpa only [List.append_nil] using hlookup
      have hnil := LookupFieldsTyp.all_prefix_nil
        (pre := fields) InertTyp.all (.nil _) hlookup'
      subst fields
      cases hlookup
  | @newIntro r A G T ds L hdefs hself =>
      have hp : PreciseVal G (.new r A T ds) (.bnd T) :=
        .newIntro L hdefs hself
      have hroot := hp.newDefsAt hi hxG
      refine .push hwf hxG ?_
      intro fields q hflow
      have hi' : Inert (G.push x (.bnd T)) := .push hi hp.inertTyp hxG
      have hlookup := hflow.sourceLookup hi' (Env.Binds.here)
      cases fields with
      | nil => cases hlookup
      | cons a tail =>
          cases hlookup with
          | cons hprefix hmember =>
              rw [← List.append_nil tail] at hprefix
              have hroot' : TypedDefs x [] (G.push x (.bnd T))
                  (ds.open x) (T.openPath (.select (.free x) [])) := by
                simpa only [Typ.openRec_eq_openRecPath_var, Path.var] using hroot
              obtain ⟨nested, hnested⟩ := LookupFieldsTyp.defsTyping
                (extra := tail) (z := x) hroot' hp.inertTyp (.nil _) hprefix
              rw [← List.append_nil tail] at hmember
              obtain ⟨U, hq⟩ := hnested.singletonRhsTyped hmember
              obtain ⟨V, hq₃⟩ := hq.precise3Exists hi'
              exact hq₃.precise2Exists

theorem Typed.valTyping {G : Ctx} {v : Val} {T : Typ} {x : Var}
    (h : Typed G (.val v) T) (hi : Inert G) (hwf : Wf G)
    (hxG : Env.Fresh x G) :
    ∃ U, PreciseVal G v U ∧ Subtyp G U T ∧ InertTyp U ∧
      Wf (G.push x U) := by
  obtain ⟨U, hp, hsub, hU⟩ := h.valAllocationType
  exact ⟨U, hp, hsub, hU, hp.wfPush hi hwf hxG⟩

theorem WellTyped.dom_eq {G : Ctx} {store : Sta}
    (h : WellTyped G store) : G.dom = store.dom := by
  induction h with
  | empty => rfl
  | push h hxG hxStore hv ih =>
      rename_i G store x v T
      simpa [Env.dom, Env.push] using congrArg (fun s => insert x s) ih

theorem WellTyped.freshContext {G : Ctx} {store : Sta} {x : Var}
    (h : WellTyped G store) (hx : Env.Fresh x store) : Env.Fresh x G := by
  unfold Env.Fresh at hx ⊢
  rw [h.dom_eq]
  exact hx

end CDot
