import CDot.GeneralToTight
import CDot.Lookup
import CDot.ContextTransport
import CDot.Narrowing
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

theorem WellTyped.bindsValue {G : Ctx} {σ : Sta} (hwt : WellTyped G σ)
    {x : Var} {T : Typ} (hb : Env.Binds x T G) :
    ∃ v, Env.Binds x v σ ∧ Typed G (.val v) T := by
  induction hwt with
  | empty => exact False.elim hb.empty_false
  | @push G σ y v U hwt hyG hyσ hv ih =>
      cases hb with
      | here =>
          exact ⟨v, .here, hv.mono (.pushRight hyG _)⟩
      | there hxy hb =>
          obtain ⟨w, hw, htyped⟩ := ih hb
          exact ⟨w, .there hxy hw, htyped.mono (.pushRight hyG _)⟩

/-- Locate a store binding together with the context prefix in which its value
was originally typed. -/
theorem WellTyped.bindsValueSplit {G : Ctx} {σ : Sta}
    (hwt : WellTyped G σ) {x : Var} {T : Typ}
    (hb : Env.Binds x T G) :
    ∃ G₀ G₁ v,
      G = Env.concat (G₀.push x T) G₁ ∧
      Env.Binds x v σ ∧ Typed G₀ (.val v) T := by
  induction hwt with
  | empty => exact False.elim hb.empty_false
  | @push G σ y v U hwt hyG hyσ hv ih =>
      cases hb with
      | here =>
          exact ⟨G, (Env.empty : Ctx), v, rfl, .here, hv⟩
      | there hxy hb =>
          obtain ⟨G₀, G₁, w, hG, hw, htyped⟩ := ih hb
          refine ⟨G₀, G₁.push y U, w, ?_, .there hxy hw, htyped⟩
          simpa [Env.concat, Env.push] using congrArg (fun E => E.push y U) hG

theorem Inert.concatLeft {G H : Ctx} (h : Inert (Env.concat G H)) :
    Inert G := by
  induction H with
  | nil => simpa [Env.concat] using h
  | cons binding H ih =>
      obtain ⟨x, T⟩ := binding
      apply ih
      exact h.prefix

theorem Wf.concatLeft {G H : Ctx} (h : Wf (Env.concat G H)) : Wf G := by
  induction H with
  | nil => simpa [Env.concat] using h
  | cons binding H ih =>
      obtain ⟨x, T⟩ := binding
      apply ih
      exact h.prefix

theorem Env.Extends.leftConcat {G H : Env α}
    (hok : Env.Ok (Env.concat G H)) : Env.Extends G (Env.concat G H) := by
  induction H with
  | nil => simpa [Env.concat] using Env.Extends.refl G
  | cons binding H ih =>
      obtain ⟨x, a⟩ := binding
      change List.Nodup (x :: (Env.concat G H).map Prod.fst) at hok
      have htail := (List.nodup_cons.mp hok).2
      have hfresh : Env.Fresh x (Env.concat G H) := by
        simpa only [Env.Fresh, Env.dom, List.mem_toFinset] using
          (List.nodup_cons.mp hok).1
      exact (ih htail).trans (.pushRight hfresh a)

theorem TypedDefs.mono {x : Var} {fields : Fields} {G G' : Ctx}
    {ds : Defs} {T : Typ} (h : TypedDefs x fields G ds T)
    (hok : Env.Ok G) (he : Env.Extends G G') (hok' : Env.Ok G') :
    TypedDefs x fields G' ds T :=
  h.transport ⟨hok, hok', fun {_ _} hb => Typed.var (he hb)⟩

theorem TypedDefs.narrow {x : Var} {fields : Fields} {G G' : Ctx}
    {ds : Defs} {T : Typ} (h : TypedDefs x fields G ds T)
    (hsub : Subenv G' G) : TypedDefs x fields G' ds T := by
  apply h.transport
  refine ⟨hsub.ok.2, hsub.ok.1, ?_⟩
  intro y U hb
  obtain ⟨S, hbS, hSU⟩ := hsub.binds hb
  exact .sub (.var hbS) hSU

theorem Defs.hasTermOpenSource {ds : Defs} {p : Path}
    {a : Signature.TrmLabel} {rhs : DefRhs}
    (h : (ds.openPath p).Has (.trm a rhs)) :
    ∃ raw, ds.Has (.trm a raw) ∧ raw.openPath p = rhs := by
  cases ds with
  | nil =>
      change (Defs.nil.get (.trm a)) = some (.trm a rhs) at h
      simp [Defs.get] at h
  | cons ds d =>
      cases d with
      | typ A T =>
          change (Defs.cons (ds.openPath p) (.typ A (T.openPath p))).get
            (.trm a) = some (.trm a rhs) at h
          apply Defs.hasTermOpenSource (ds := ds)
          change (ds.openPath p).get (.trm a) = some (.trm a rhs)
          simpa [Defs.get, Def.label] using h
      | trm b raw =>
          change (Defs.cons (ds.openPath p) (.trm b (raw.openPath p))).get
            (.trm a) = some (.trm a rhs) at h
          by_cases hba : b = a
          · subst b
            have heq : raw.openPath p = rhs := by
              have hd : Def.trm a (raw.openPath p) = Def.trm a rhs := by
                exact Option.some.inj (by
                  simpa [Defs.get, Def.label] using h)
              exact (Def.trm.inj hd).2
            exact ⟨raw, by simp [Defs.Has, Defs.get], heq⟩
          · obtain ⟨raw', hraw', hopen⟩ := Defs.hasTermOpenSource (ds := ds) (by
              change (ds.openPath p).get (.trm a) = some (.trm a rhs)
              simpa [Defs.get, Def.label, hba] using h)
            exact ⟨raw', by
              simpa [Defs.Has, Defs.get, Def.label, hba] using hraw', hopen⟩
termination_by sizeOf ds
decreasing_by all_goals simp_all; omega

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

theorem InvertibleVal.bndValueShape {G : Ctx} {v : Val} {T : Typ}
    (h : InvertibleVal G v (.bnd T)) :
    ∃ r A U ds, v = .new r A U ds := by
  generalize heq : Typ.bnd T = V at h
  induction h generalizing T with
  | precise h =>
      cases heq
      cases h with
      | newIntro => exact ⟨_, _, _, _, rfl⟩
  | recPQ _ _ _ _ ih =>
      cases heq
      exact ih rfl

theorem Typed.valBndToNew {G : Ctx} {v : Val} {T : Typ}
    (h : Typed G (.val v) (.bnd T)) (hi : Inert G) :
    ∃ r A U ds T',
      v = .new r A U ds ∧
      PreciseVal G (.new r A U ds) (.bnd U) ∧
      ReplComposition G T' T := by
  have hr := (h.toTight hi).valReplacement hi
  obtain ⟨T', hinv, hcomp⟩ := hr.bndToInvertible
  obtain ⟨r, A, U, ds, hv⟩ := hinv.bndValueShape
  subst v
  obtain ⟨T'', heq, hp, hcomp'⟩ := hinv.newToPrecise
  cases heq
  exact ⟨r, A, U, ds, T', rfl, hp, hcomp⟩

theorem Typed.valBndToNewCommon {G : Ctx} {v : Val} {T : Typ}
    (h : Typed G (.val v) (.bnd T)) (hi : Inert G) :
    ∃ r A U ds,
      v = .new r A U ds ∧
      PreciseVal G (.new r A U ds) (.bnd U) ∧
      CommonRepl G T U := by
  have hr := (h.toTight hi).valReplacement hi
  obtain ⟨W, hinv, hWT⟩ := hr.bndToInvertible
  obtain ⟨r, A, U, ds, hv⟩ := hinv.bndValueShape
  subst v
  obtain ⟨W', heq, hp, hWU⟩ := hinv.newToPrecise
  have hWW' := Typ.bnd.inj heq
  subst W'
  exact ⟨r, A, U, ds, rfl, hp, W, hWT, hWU⟩

theorem PreciseVal.newDefsAtBinding {G : Ctx} {r : Path}
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

inductive LookupClass (G : Ctx) (p : Path) : Typ → DefRhs → Prop where
  | lambda : Typed G (.val (.lambda S body)) T →
      LookupClass G p T (.val (.lambda S body))
  | object (x : Var) (fields : Fields) :
      p = (Path.var x).selectFields fields →
      TypedDefs x fields G (ds.openPath p) (U.openPath p) →
      CommonRepl G T U →
      LookupClass G p (.bnd T) (.val (.new r A U ds))
  | path : Typed G (.path q) U → LookupClass G p (.sngl r) (.path q)

theorem PreciseFlow.lookupClass {G : Ctx} {σ : Sta} {p : Path} {T U : Typ}
    (h : PreciseFlow G p T U) (hi : Inert G) (hwt : WellTyped G σ) :
    ∃ rhs, LookupStep σ (.path p) rhs ∧ LookupClass G p T rhs := by
  induction h with
  | bind hok hb =>
      rename_i x T
      obtain ⟨G₀, G₁, v, hG, hvStore, hv⟩ := hwt.bindsValueSplit hb
      subst G
      have hiHead : Inert (G₀.push x T) := hi.concatLeft
      cases hiHead with
      | @push _ _ _ hi₀ hT hx =>
          have heHead : Env.Extends (G₀.push x T)
              (Env.concat (G₀.push x T) G₁) :=
            Env.Extends.leftConcat hi.ok
          have heBase : Env.Extends G₀ (Env.concat (G₀.push x T) G₁) :=
            (Env.Extends.pushRight hx T).trans heHead
          cases hT with
          | all =>
              obtain ⟨L, S, body, rfl, hdom, hbody⟩ := hv.valAllToLambda hi₀
              exact ⟨.val (.lambda S body), .var hvStore,
                .lambda (hv.mono heBase)⟩
          | @bnd T labels hrecord =>
              obtain ⟨r, A, S, ds, rfl, hp, hc⟩ :=
                hv.valBndToNewCommon hi₀
              have hiPrec : Inert (G₀.push x (.bnd S)) :=
                .push hi₀ hp.inertTyp hx
              have hiActual : Inert (G₀.push x (.bnd T)) :=
                .push hi₀ (.bnd hrecord) hx
              have hdefsPrec := hp.newDefsAtBinding hi₀ hx
              have hsub : Subtyp G₀ (.bnd T) (.bnd S) :=
                hc.bnd.subtypes.1
              have hdefsHead := hdefsPrec.narrow
                (Subenv.last hsub hiActual.ok hiPrec.ok)
              have hdefsFull := hdefsHead.mono hiActual.ok heHead hi.ok
              have hdefsFull' : TypedDefs x []
                  (Env.concat (G₀.push x (.bnd T)) G₁)
                  (ds.openPath (Path.var x)) (S.openPath (Path.var x)) := by
                simpa only [Defs.openRec_eq_openRecPath_var,
                  Typ.openRec_eq_openRecPath_var] using hdefsFull
              exact ⟨.val (.new r A S ds), .var hvStore,
                .object x [] rfl hdefsFull' (hc.mono heBase hi.ok)⟩
  | fld hprefix ih =>
      rename_i p T a V
      have hrecordTarget : RecordType (.rcd (.trm a V)) := by
        rcases (hprefix.inertSngl hi).2 with hbad | hrecord
        · exact False.elim hbad.rcd_false
        · exact hrecord
      obtain ⟨R, hT⟩ := hprefix.recordTypeSource_bnd hi hrecordTarget
      subst T
      obtain ⟨rhs, hstep, hclass⟩ := ih
      cases hclass with
      | lambda hv =>
          obtain ⟨r, A, S, ds, heq, hp, hc⟩ := hv.valBndToNewCommon hi
          cases heq
      | object x fields hp hdefs hc =>
          rename_i r A S ds
          subst p
          let current := (Path.var x).selectFields fields
          have hstatic : RecordHas (R.openPath current) (.trm a V) :=
            hprefix.recordHas_of_bnd hi .one
          obtain ⟨V', hmember, hcMember⟩ :=
            (hc.openPath current).recordHas hstatic
          obtain ⟨d, hdOpen, htyped⟩ := hdefs.recordHas hmember
          cases htyped with
          | all ht =>
              obtain ⟨raw, hdRaw, hopen⟩ :=
                Defs.hasTermOpenSource (ds := ds) hdOpen
              have hselect : LookupStep σ (.path (current.selectField a))
                  (raw.openPath current) := .selectVal hstep hdRaw
              rw [hopen] at hselect
              exact ⟨_, hselect, .lambda (.sub ht hcMember.subtypes.2)⟩
          | new base hbase htight hnested htag =>
              obtain ⟨raw, hdRaw, hopen⟩ :=
                Defs.hasTermOpenSource (ds := ds) hdOpen
              have hselect : LookupStep σ (.path (current.selectField a))
                  (raw.openPath current) := .selectVal hstep hdRaw
              subst base
              obtain ⟨Vstatic, hV, hcNested⟩ := hcMember.rightBnd
              subst V
              rw [hopen] at hselect
              exact ⟨_, hselect, .object x (a :: fields) rfl
                (by simpa [current, Path.var, Path.selectField,
                    Path.selectFields] using hnested)
                hcNested⟩
          | path hq =>
              obtain ⟨raw, hdRaw, hopen⟩ :=
                Defs.hasTermOpenSource (ds := ds) hdOpen
              have hselect : LookupStep σ (.path (current.selectField a))
                  (raw.openPath current) := .selectVal hstep hdRaw
              obtain ⟨r', hV⟩ := hcMember.rightSngl
              subst V
              rw [hopen] at hselect
              exact ⟨_, hselect, .path hq⟩
  | «open» h ih => exact ih
  | andLeft h ih => exact ih
  | andRight h ih => exact ih

theorem Typed.valPreciseSubtype {G : Ctx} {v : Val} {T : Typ}
    (h : Typed G (.val v) T) :
    ∃ U, PreciseVal G v U ∧ Subtyp G U T := by
  apply Typed.rec
    (motive_1 := fun G t T _ => ∀ v, t = .val v →
      ∃ U, PreciseVal G v U ∧ Subtyp G U T)
    (motive_2 := fun _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True)
  case allIntro =>
    intro G S t U L hbody ih v heq
    cases heq
    exact ⟨.all S U, .allIntro L hbody, .refl⟩
  case newIntro =>
    intro p A G U ds L hdefs hself ihdefs ihself v heq
    cases heq
    exact ⟨.bnd U, .newIntro L hdefs hself, .refl⟩
  case sub =>
    intro G t S T ht hs ih iht v heq
    obtain ⟨U, hp, hUS⟩ := ih v heq
    exact ⟨U, hp, .trans hUS hs⟩
  case var => intros; contradiction
  case allElim => intros; contradiction
  case newElim => intros; contradiction
  case rcdIntro => intros; contradiction
  case letE => intros; contradiction
  case caseE => intros; contradiction
  case sngl => intros; contradiction
  case self => intros; contradiction
  case pathElim => intros; contradiction
  case recIntro => intros; contradiction
  case recElim => intros; contradiction
  case andIntro => intros; contradiction
  all_goals first | rfl | (intros; trivial)

theorem Typed.valAllocationType {G : Ctx} {v : Val} {T : Typ}
    (h : Typed G (.val v) T) :
    ∃ U, PreciseVal G v U ∧ Subtyp G U T ∧ InertTyp U := by
  obtain ⟨U, hp, hsub⟩ := h.valPreciseSubtype
  exact ⟨U, hp, hsub, hp.inertTyp⟩

end CDot
