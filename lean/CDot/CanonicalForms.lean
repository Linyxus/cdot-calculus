import CDot.GeneralToTight
import CDot.Lookup
import CDot.Reduction
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

theorem Typed.renameLast {G : Ctx} {z x : Var} {S T : Typ} {t : Trm}
    (h : Typed (G.push z S) t T) (hzG : z ∉ G.fvTypes)
    (hxG : Env.Fresh x G) (hzx : z ≠ x)
    (hok : Env.Ok ((G.push x (S.subst z (.var x))).push z S)) :
    Typed (G.push x (S.subst z (.var x)))
      (t.subst z (.var x)) (T.subst z (.var x)) := by
  have hr := h.renameMiddle (G₁ := G) (G₂ := Env.empty)
    hzG hxG hzx (by simpa [Env.concat, Env.empty] using hok)
  simpa [Env.concat, Env.empty, Ctx.subst] using hr

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

theorem PreciseVal.newTagAtBinding {G : Ctx} {r : Path}
    {A : Signature.TypLabel} {T : Typ} {ds : Defs} {x : Var}
    (h : PreciseVal G (.new r A T ds) (.bnd T))
    (hi : Inert G) (hxG : Env.Fresh x G) :
    Typed (G.push x (.bnd T)) (.path (.var x))
      ((.path r A : Typ).open x) := by
  cases h with
  | newIntro L hdefs hself =>
      let tag : Typ := .path r A
      let avoid := L ∪ G.dom ∪ G.fvTypes ∪ T.fv ∪ tag.fv ∪ {x}
      obtain ⟨z, hzrange⟩ := Finset.exists_nat_subset_range avoid
      have hz : z ∉ avoid := by
        intro hmem
        exact (Nat.lt_irrefl z) (Finset.mem_range.mp (hzrange hmem))
      have hzL : z ∉ L := by aesop
      have hzG : Env.Fresh z G := by aesop
      have hzTypes : z ∉ G.fvTypes := by aesop
      have hzT : z ∉ T.fv := by aesop
      have hzTag : z ∉ tag.fv := by aesop
      have hzx : z ≠ x := by aesop
      have hzPush : Env.Fresh z (G.push x ((T.open z).subst z (.var x))) := by
        intro hmem
        simp only [Env.dom, Env.push, List.map_cons, List.mem_toFinset,
          List.mem_cons] at hmem
        rcases hmem with hzx' | hmem
        · exact hzx hzx'
        · exact hzG (by simpa only [Env.dom, List.mem_toFinset] using hmem)
      have hokx : Env.Ok (G.push x ((T.open z).subst z (.var x))) :=
        Env.okPush hi.ok hxG
      have hren := (hself z hzL).renameLast hzTypes hxG hzx
        (Env.okPush hokx hzPush)
      have hnamed : (Path.var x).Named := ⟨x, rfl⟩
      have hTopen := Typ.openPath_eq_subst_open_of_fresh T hzT hnamed
      have hTagOpen := Typ.openPath_eq_subst_open_of_fresh tag hzTag hnamed
      simp only [Typ.openRec_eq_openRecPath_var] at hTopen hTagOpen
      simp only [tag] at hTagOpen
      simp only [Typ.openRec_eq_openRecPath_var] at hren
      rw [← hTopen, ← hTagOpen] at hren
      have hren' : Typed (G.push x (T.open x)) (.path (.var x))
          (tag.open x) := by
        simpa [tag, Trm.subst, Path.subst, Path.var, AVar.subst,
          Var.substPath, hzx, Typ.openRec_eq_openRecPath_var] using hren
      exact hren'.openSelfContext (Env.okPush hi.ok hxG)

inductive LookupClass (G : Ctx) (p : Path) : Typ → DefRhs → Prop where
  | lambda : Typed G (.val (.lambda S body)) (.all T U) →
      LookupClass G p (.all T U) (.val (.lambda S body))
  | object (G₀ G₁ : Ctx) (x : Var) (pT : Typ) (fields : Fields) :
      G = Env.concat (G₀.push x pT) G₁ →
      p = (Path.var x).selectFields fields →
      TypedDefs x fields G (ds.openPath p) (U.openPath p) →
      Typed G (.path p) ((.path r A : Typ).openPath p) →
      CommonRepl G₀ T U → CommonRepl G T U →
      LookupClass G p (.bnd T) (.val (.new r A U ds))
  | path (G₀ G₁ : Ctx) (x : Var) (pT : Typ) (fields : Fields) :
      G = Env.concat (G₀.push x pT) G₁ →
      p = (Path.var x).selectFields fields →
      Typed G (.path q) S →
      CommonRepl G₀ (.sngl r) (.sngl q) →
      CommonRepl G (.sngl r) (.sngl q) →
      LookupClass G p (.sngl r) (.path q)

def PreciseAliases (G : Ctx) (p q : Path) : Prop :=
  ∃ r,
    (r = p ∨ PreciseTyping3 G p (.sngl r)) ∧
    (r = q ∨ PreciseTyping3 G q (.sngl r))

theorem PreciseAliases.field {G : Ctx} {p q : Path}
    {a : Signature.TrmLabel} {T : Typ} (hi : Inert G)
    (h : PreciseAliases G p q)
    (hp : PreciseTyping3 G (p.selectField a) T) :
    ∃ U, PreciseTyping3 G (q.selectField a) U ∧
      PreciseAliases G (p.selectField a) (q.selectField a) := by
  obtain ⟨r, hpr, hqr⟩ := h
  have hr : ∃ V, PreciseTyping3 G (r.selectField a) V := by
    rcases hpr with rfl | hpr
    · exact ⟨T, hp⟩
    · exact hpr.fieldOtherExists hi hp
  obtain ⟨V, hr⟩ := hr
  have hq : ∃ U, PreciseTyping3 G (q.selectField a) U := by
    rcases hqr with rfl | hqr
    · exact ⟨V, hr⟩
    · exact ⟨_, hqr.fieldSngl hr⟩
  obtain ⟨U, hq⟩ := hq
  refine ⟨U, hq, r.selectField a, ?_, ?_⟩
  · rcases hpr with rfl | hpr
    · exact Or.inl rfl
    · exact Or.inr (hpr.fieldSnglFromLeft hi hp)
  · rcases hqr with rfl | hqr
    · exact Or.inl rfl
    · exact Or.inr (hqr.fieldSngl hr)

theorem PreciseAliases.transferRecord {G : Ctx} {p q : Path} {T : Typ}
    (hi : Inert G) (hrecord : RecordType T)
    (h : PreciseAliases G p q) (hp : PreciseTyping3 G p T) :
    PreciseTyping3 G q T := by
  obtain ⟨r, hpr, hqr⟩ := h
  have hr : PreciseTyping3 G r T := by
    rcases hpr with rfl | hpr
    · exact hp
    · exact hp.invertSngl_record hi hrecord hpr
  rcases hqr with rfl | hqr
  · exact hr
  · exact hqr.snglTrans3 hr

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
              have htagPrec := hp.newTagAtBinding hi₀ hx
              have hsub : Subtyp G₀ (.bnd T) (.bnd S) :=
                hc.bnd.subtypes.1
              have hdefsHead := hdefsPrec.narrow
                (Subenv.last hsub hiActual.ok hiPrec.ok)
              have htagHead := htagPrec.narrow
                (Subenv.last hsub hiActual.ok hiPrec.ok)
              have hdefsFull := hdefsHead.mono hiActual.ok heHead hi.ok
              have htagFull := htagHead.mono heHead
              have hdefsFull' : TypedDefs x []
                  (Env.concat (G₀.push x (.bnd T)) G₁)
                  (ds.openPath (Path.var x)) (S.openPath (Path.var x)) := by
                simpa only [Defs.openRec_eq_openRecPath_var,
                  Typ.openRec_eq_openRecPath_var] using hdefsFull
              exact ⟨.val (.new r A S ds), .var hvStore,
                .object G₀ G₁ x (.bnd T) [] rfl rfl hdefsFull'
                  (by simpa only [Typ.openRec_eq_openRecPath_var] using htagFull)
                  hc (hc.mono heBase hi.ok)⟩
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
      | object G₀ G₁ x pT fields hG hp hdefs htag hc₀ hc =>
          rename_i r A S ds
          subst p
          let current := (Path.var x).selectFields fields
          have hstatic : RecordHas (R.openPath current) (.trm a V) :=
            hprefix.recordHas_of_bnd hi .one
          obtain ⟨V', hmember, hcMember⟩ :=
            (hc.openPath current).recordHas hstatic
          obtain ⟨V₀, hmember₀, hcMember₀⟩ :=
            (hc₀.openPath current).recordHas hstatic
          have hmemberEq : V₀ = V' := by
            obtain ⟨labels, hrecord⟩ := hdefs.recordType
            exact Dec.trm.inj
              (hrecord.has_unique hmember₀ hmember rfl) |>.2
          subst V₀
          obtain ⟨d, hdOpen, htyped⟩ := hdefs.recordHas hmember
          cases htyped with
          | all ht =>
              obtain ⟨raw, hdRaw, hopen⟩ :=
                Defs.hasTermOpenSource (ds := ds) hdOpen
              have hselect : LookupStep σ (.path (current.selectField a))
                  (raw.openPath current) := .selectVal hstep hdRaw
              obtain ⟨Sstatic, Tstatic, hV⟩ := hcMember.rightAll
              subst V
              rw [hopen] at hselect
              exact ⟨_, hselect, .lambda (.sub ht hcMember.subtypes.2)⟩
          | new base hbase htight hnested htag =>
              obtain ⟨raw, hdRaw, hopen⟩ :=
                Defs.hasTermOpenSource (ds := ds) hdOpen
              have hselect : LookupStep σ (.path (current.selectField a))
                  (raw.openPath current) := .selectVal hstep hdRaw
              subst base
              obtain ⟨Vstatic, hV, hcNested⟩ := hcMember.rightBnd
              obtain ⟨Vstatic₀, hV₀, hcNested₀⟩ := hcMember₀.rightBnd
              have hVstatic : Vstatic₀ = Vstatic :=
                Typ.bnd.inj (hV₀.symm.trans hV)
              subst Vstatic₀
              subst V
              rw [hopen] at hselect
              exact ⟨_, hselect, .object G₀ G₁ x pT (a :: fields)
                hG rfl
                (by simpa [current, Path.var, Path.selectField,
                    Path.selectFields] using hnested)
                (by simpa [current, Path.var, Path.selectField,
                    Path.selectFields] using htag)
                hcNested₀
                hcNested⟩
          | path hq =>
              obtain ⟨raw, hdRaw, hopen⟩ :=
                Defs.hasTermOpenSource (ds := ds) hdOpen
              have hselect : LookupStep σ (.path (current.selectField a))
                  (raw.openPath current) := .selectVal hstep hdRaw
              obtain ⟨r', hV⟩ := hcMember.rightSngl
              subst V
              rw [hopen] at hselect
              exact ⟨_, hselect, .path G₀ G₁ x pT (a :: fields)
                hG rfl hq hcMember₀ hcMember⟩
  | «open» h ih => exact ih
  | andLeft h ih => exact ih
  | andRight h ih => exact ih

theorem PreciseFlow.lookupSingletonSameReceiver {G : Ctx} {σ : Sta}
    {x : Var} {fields targetFields : Fields}
    (h : PreciseFlow G (.select (.free x) fields)
      (.sngl (.select (.free x) targetFields))
      (.sngl (.select (.free x) targetFields)))
    (hi : Inert G) (hwt : WellTyped G σ) :
    LookupStep σ (.path (.select (.free x) fields))
      (.path (.select (.free x) targetFields)) := by
  obtain ⟨rhs, hstep, hclass⟩ := h.lookupClass hi hwt
  cases hclass with
  | path G₀ G₁ y pT runtimeFields hG hp htyped hc₀ hc =>
      have hxy : x = y := by
        simp only [Path.var, Path.selectFields] at hp
        injection hp with hxy hfields
        injection hxy
      subst y
      have hiHead : Inert (G₀.push x pT) := by
        rw [hG] at hi
        exact hi.concatLeft
      have hxG₀ : Env.Fresh x G₀ := by
        cases hiHead with
        | push _ _ hx => exact hx
      have hruntime := hc₀.snglFreshPath_eq hxG₀
      subst hruntime
      exact hstep

theorem PreciseTyping2.lookupSingletonSameReceiver {G : Ctx} {σ : Sta}
    {x : Var} {fields targetFields : Fields}
    (h : PreciseTyping2 G (.select (.free x) fields)
      (.sngl (.select (.free x) targetFields)))
    (hi : Inert G) (hwt : WellTyped G σ) :
    LookupStep σ (.path (.select (.free x) fields))
      (.path (.select (.free x) targetFields)) := by
  have aux : ∀ {p : Path} {T : Typ}, PreciseTyping2 G p T →
      ∀ (q : Path) (y : Var) (sourceFields resultFields : Fields),
        T = .sngl q →
        p = .select (.free y) sourceFields →
        q = .select (.free y) resultFields →
        LookupStep σ (.path p) (.path q) := by
    intro p T hp
    induction hp with
    | flow hf =>
        intro q y sourceFields resultFields htEq hpEq hqEq
        rw [htEq] at hf
        rw [hpEq, hqEq] at hf
        have hsource := hf.snglSource_eq hi
        rw [hsource] at hf
        rw [hpEq, hqEq]
        exact hf.lookupSingletonSameReceiver hi hwt
    | snglTrans hp hq ihp ihq =>
        intro result y sourceFields resultFields htEq hpEq hqEq
        rename_i p q a U
        have hresult : result = q.selectField a :=
          (Typ.sngl.inj htEq).symm
        have hqEq' : q.selectField a = .select (.free y) resultFields :=
          hresult.symm.trans hqEq
        rw [hresult]
        cases p with
        | select pav pfields =>
            simp only [Path.selectField] at hpEq
            injection hpEq with hpAvar hpFields
            cases hpAvar
            cases sourceFields with
            | nil => cases hpFields
            | cons b sourceFields =>
                injection hpFields with hba hpRest
                cases hba
                cases q with
                | select qav qfields =>
                    simp only [Path.selectField] at hqEq'
                    injection hqEq' with hqAvar hqFields
                    cases hqAvar
                    cases resultFields with
                    | nil => cases hqFields
                    | cons c resultFields =>
                        injection hqFields with hca hqRest
                        cases hca
                        exact .selectPath
                          (ihp (.select (.free y) qfields) y
                            pfields qfields rfl rfl rfl)
  exact aux h _ x fields targetFields rfl rfl rfl

theorem PreciseTyping2.lookupSingletonCrossReceiver {G : Ctx} {σ : Sta}
    {x z : Var} {fields targetFields : Fields}
    (h : PreciseTyping2 G (.select (.free x) fields)
      (.sngl (.select (.free z) targetFields)))
    (hxz : x ≠ z) (hi : Inert G) (hwt : WellTyped G σ) :
    ∃ y runtimeFields,
      LookupStep σ (.path (.select (.free x) fields))
        (.path (.select (.free y) runtimeFields)) ∧ y ≠ x := by
  have aux : ∀ {p : Path} {T : Typ}, PreciseTyping2 G p T →
      ∀ (q : Path) (a b : Var) (pfields qfields : Fields),
        T = .sngl q →
        p = .select (.free a) pfields →
        q = .select (.free b) qfields → a ≠ b →
        ∃ y runtimeFields,
          LookupStep σ (.path p)
            (.path (.select (.free y) runtimeFields)) ∧ y ≠ a := by
    intro p T hp
    induction hp with
    | flow hf =>
        intro q a b pfields qfields ht hpEq hqEq hab
        rw [ht, hpEq, hqEq] at hf
        rw [hpEq]
        have hsource := hf.snglSource_eq hi
        rw [hsource] at hf
        obtain ⟨rhs, hstep, hclass⟩ := hf.lookupClass hi hwt
        cases hclass with
        | path G₀ G₁ root pT runtimePrefix hG hsourceEq
            htyped hc₀ hc =>
            rename_i runtime runtimeT
            have haroot : a = root := by
              simp only [Path.var, Path.selectFields] at hsourceEq
              injection hsourceEq with havar hfields
              injection havar
            subst root
            have hiHead : Inert (G₀.push a pT) := by
              rw [hG] at hi
              exact hi.concatLeft
            have haG₀ : Env.Fresh a G₀ := by
              cases hiHead with
              | push _ _ ha => exact ha
            have hruntimeNamed := htyped.pathNamed
            obtain ⟨rav, rfields⟩ := runtime
            simp only [Path.Named] at hruntimeNamed
            obtain ⟨y, rfl⟩ := hruntimeNamed
            have hya : y ≠ a := by
              intro hya
              subst y
              have heq := hc₀.symm.snglFreshPath_eq haG₀
              injection heq with havar hfields
              have hba : b = a := by injection havar
              exact hab hba.symm
            exact ⟨y, rfields, hstep, hya⟩
    | snglTrans hp hq ihp ihq =>
        intro result a b pfields qfields ht hpEq hqEq hab
        rename_i p q label U
        have hresult : result = q.selectField label :=
          (Typ.sngl.inj ht).symm
        have hqEq' : q.selectField label = .select (.free b) qfields :=
          hresult.symm.trans hqEq
        cases p with
        | select pav pbase =>
            simp only [Path.selectField] at hpEq
            injection hpEq with hpAvar hpFields
            cases hpAvar
            cases pfields with
            | nil => cases hpFields
            | cons l pfields =>
                injection hpFields with hlabel hpRest
                cases hlabel
                cases q with
                | select qav qbase =>
                    simp only [Path.selectField] at hqEq'
                    injection hqEq' with hqAvar hqFields
                    cases hqAvar
                    cases qfields with
                    | nil => cases hqFields
                    | cons l' qfields =>
                        injection hqFields with hlabel' hqRest
                        cases hlabel'
                        obtain ⟨y, runtimeFields, hstep, hya⟩ :=
                          ihp (.select (.free b) qbase) a b pbase qbase
                            rfl rfl rfl hab
                        exact ⟨y, label :: runtimeFields,
                          .selectPath hstep, hya⟩
  exact aux h _ x z fields targetFields rfl rfl rfl hxz

theorem PreciseTyping3.lookupSingletonSameReceiver {G : Ctx} {σ : Sta}
    {x : Var} {fields targetFields : Fields}
    (h : PreciseTyping3 G (.select (.free x) fields)
      (.sngl (.select (.free x) targetFields)))
    (hi : Inert G) (hwf : Wf G) (hwt : WellTyped G σ) :
    Lookup σ (.path (.select (.free x) fields))
      (.path (.select (.free x) targetFields)) := by
  have aux : ∀ {p : Path} {T : Typ}, PreciseTyping3 G p T →
      ∀ (q : Path) (y : Var) (sourceFields resultFields : Fields),
        T = .sngl q →
        p = .select (.free y) sourceFields →
        q = .select (.free y) resultFields →
        Lookup σ (.path p) (.path q) := by
    intro p T hp
    induction hp with
    | precise hp =>
        intro q y sourceFields resultFields htEq hpEq hqEq
        rw [htEq, hpEq, hqEq] at hp
        rw [hpEq, hqEq]
        exact .one (hp.lookupSingletonSameReceiver hi hwt)
    | snglTrans hp hrest ih =>
        intro result y sourceFields resultFields htEq hpEq hresultEq
        rename_i p q T
        rw [hpEq] at hp
        rw [hpEq]
        have hqNamed := hrest.toGeneral.pathNamed
        cases q with
        | select qav qfields =>
            simp only [Path.Named] at hqNamed
            obtain ⟨z, rfl⟩ := hqNamed
            by_cases hzy : z = y
            · subst z
              have hfirst := hp.lookupSingletonSameReceiver hi hwt
              have htail := ih result y qfields resultFields
                htEq rfl hresultEq
              exact .step hfirst htail
            · obtain ⟨S, hb⟩ := hp.receiverBinds
              obtain ⟨G₀, G₁, v, hG, hv, hvTyped⟩ :=
                hwt.bindsValueSplit hb
              rw [hG] at hi hwf hp hrest hwt
              have hiHead : Inert (G₀.push y S) := hi.concatLeft
              have hwfHead : Wf (G₀.push y S) := hwf.concatLeft
              have hpHead := hp.strengthenConcat
                (Env.Binds.here : Env.Binds y S (G₀.push y S)) hi hwf
              obtain ⟨U, hqHead⟩ :=
                hpHead.singletonTargetTyped hiHead hwfHead
              obtain ⟨Z, hbzHead⟩ := hqHead.receiverBinds
              have hrestHead := hrest.strengthenConcat hbzHead hi hwf
              have hrestBase := hrestHead.strengthenPush
                hiHead hwfHead.prefix hzy
              rw [htEq, hresultEq] at hrestBase
              obtain ⟨V, hresultBase⟩ :=
                hrestBase.singletonTargetTyped hiHead.prefix hwfHead.prefix
              obtain ⟨W, hresultBase₂⟩ := hresultBase.precise2Exists
              obtain ⟨R, hby⟩ := hresultBase₂.receiverBinds
              have hyG₀ : Env.Fresh y G₀ := by
                cases hiHead with
                | push _ _ hy => exact hy
              exact False.elim (hyG₀ hby.mem_dom)
  exact aux h _ x fields targetFields rfl rfl rfl

theorem PreciseTyping3.previousReceiver {G : Ctx} {p q : Path}
    {x y : Var} {sourceFields targetFields : Fields}
    (hi : Inert G) (hwf : Wf G)
    (hpEq : p = .select (.free x) sourceFields)
    (hqEq : q = .select (.free y) targetFields)
    (h : PreciseTyping3 G p (.sngl q)) (hxy : x ≠ y) :
    ∃ pFields qFields z,
      z ≠ x ∧
      (p = .select (.free x) pFields ∨
        PreciseTyping3 G p (.sngl (.select (.free x) pFields))) ∧
      PreciseTyping2 G (.select (.free x) pFields)
        (.sngl (.select (.free z) qFields)) ∧
      (.select (.free z) qFields = q ∨
        PreciseTyping3 G (.select (.free z) qFields) (.sngl q)) := by
  have aux : ∀ {p : Path} {T : Typ}, PreciseTyping3 G p T →
      ∀ (q : Path) (a b : Var) (pfields qfields : Fields),
        T = .sngl q →
        p = .select (.free a) pfields →
        q = .select (.free b) qfields → a ≠ b →
        ∃ prefixFields nextFields z,
          z ≠ a ∧
          (p = .select (.free a) prefixFields ∨
            PreciseTyping3 G p
              (.sngl (.select (.free a) prefixFields))) ∧
          PreciseTyping2 G (.select (.free a) prefixFields)
            (.sngl (.select (.free z) nextFields)) ∧
          (.select (.free z) nextFields = q ∨
            PreciseTyping3 G (.select (.free z) nextFields) (.sngl q)) := by
    intro path T hpath
    induction hpath with
    | precise hprecise =>
        intro target a b pfields qfields ht hpEq hqEq hab
        rw [ht, hpEq, hqEq] at hprecise
        exact ⟨pfields, qfields, b, Ne.symm hab, Or.inl hpEq,
          hprecise, Or.inl hqEq.symm⟩
    | snglTrans hfirst hrest ih =>
        intro target a b pfields qfields ht hpEq hqEq hab
        rename_i path middle T
        have hmiddleNamed := hrest.toGeneral.pathNamed
        cases middle with
        | select mav mfields =>
            simp only [Path.Named] at hmiddleNamed
            obtain ⟨z, rfl⟩ := hmiddleNamed
            rw [hpEq] at hfirst
            rw [hpEq]
            by_cases hzb : z = b
            · subst z
              rw [ht] at hrest
              exact ⟨pfields, mfields, b, Ne.symm hab, Or.inl rfl,
                hfirst, Or.inr hrest⟩
            · obtain ⟨prefixFields, nextFields, w, hwa,
                  hmiddlePrefix, hprefixNext, hnextTarget⟩ :=
                ih target z b mfields qfields ht rfl hqEq hzb
              by_cases haz : a = z
              · subst z
                have hpathPrefix :
                    Path.select (.free a) pfields =
                      Path.select (.free a) prefixFields ∨
                    PreciseTyping3 G (Path.select (.free a) pfields)
                      (.sngl (Path.select (.free a) prefixFields)) := by
                  rcases hmiddlePrefix with hmiddlePrefix | hmiddlePrefix
                  · rw [hmiddlePrefix] at hfirst
                    exact Or.inr (.precise hfirst)
                  · exact Or.inr
                      ((PreciseTyping3.precise hfirst).snglTrans3 hmiddlePrefix)
                exact ⟨prefixFields, nextFields, w, hwa,
                  hpathPrefix, hprefixNext, hnextTarget⟩
              · rw [ht] at hrest
                exact ⟨pfields, mfields, z, Ne.symm haz,
                  Or.inl rfl, hfirst, Or.inr hrest⟩
  exact aux h q x y sourceFields targetFields rfl hpEq hqEq hxy

theorem PreciseTyping2.lookupSingletonAliases {G : Ctx} {σ : Sta}
    {p q : Path} (h : PreciseTyping2 G p (.sngl q))
    (hi : Inert G) (hwf : Wf G) (hwt : WellTyped G σ) :
    ∃ r U, LookupStep σ (.path p) (.path r) ∧
      PreciseTyping3 G r U ∧ PreciseAliases G q r := by
  generalize heq : Typ.sngl q = T at h
  induction h generalizing q with
  | flow h =>
      cases heq
      have hsource := h.snglSource_eq hi
      rw [hsource] at h
      obtain ⟨rhs, hstep, hclass⟩ := h.lookupClass hi hwt
      cases hclass with
      | path G₀ G₁ x pT fields hG hp htyped hc₀ hc =>
          obtain ⟨U, hruntime⟩ := htyped.precise3Exists hi
          obtain ⟨V, hstatic⟩ := h.singletonTargetTyped hi hwf
          have halias := hc.snglAliases hi hwf
            (.precise hstatic) hruntime
          exact ⟨_, U, hstep, hruntime, halias⟩
  | snglTrans hp hq ihp ihq =>
      cases heq
      obtain ⟨r, U, hstep, hr, halias⟩ := ihp rfl
      obtain ⟨V, hrfield, haliasField⟩ :=
        halias.field hi (.precise hq)
      exact ⟨r.selectField _, V, .selectPath hstep, hrfield, haliasField⟩

theorem PreciseTyping3.lookupRecord {G : Ctx} {σ : Sta}
    {p : Path} {T : Typ} (h : PreciseTyping3 G p T)
    (hrecord : RecordType T) (hi : Inert G) (hwf : Wf G)
    (hwt : WellTyped G σ) :
    (∃ q, LookupStep σ (.path p) (.path q) ∧ PreciseTyping3 G q T) ∨
    (∃ r A U ds, LookupStep σ (.path p) (.val (.new r A U ds)) ∧
      Typed G (.path p) ((.path r A : Typ).openPath p)) := by
  cases h with
  | precise hp =>
      cases hp with
      | flow hf =>
          obtain ⟨rhs, hstep, hclass⟩ := hf.lookupClass hi hwt
          cases hclass with
          | lambda htyped =>
              have heq := hf.envAll_eq
              rw [heq] at hrecord
              obtain ⟨labels, hrecord⟩ := hrecord
              cases hrecord
          | object G₀ G₁ x pT fields hG heq hdefs htag hc₀ hc =>
              exact Or.inr ⟨_, _, _, _, hstep, htag⟩
          | path G₀ G₁ x pT fields hG heq htyped hc₀ hc =>
              have heq := hf.envSngl_eq
              rw [heq] at hrecord
              obtain ⟨labels, hrecord⟩ := hrecord
              cases hrecord
      | snglTrans hp hq =>
          obtain ⟨labels, hrecord⟩ := hrecord
          cases hrecord
  | snglTrans hp hq =>
      obtain ⟨r, U, hstep, hr, halias⟩ :=
        hp.lookupSingletonAliases hi hwf hwt
      exact Or.inl ⟨r, hstep, halias.transferRecord hi hrecord hq⟩

theorem PreciseTyping2.lookupRecordValue {G : Ctx} {σ : Sta}
    {p : Path} {T : Typ} (h : PreciseTyping2 G p T)
    (hrecord : RecordType T) (hi : Inert G) (hwt : WellTyped G σ) :
    ∃ r A U ds,
      LookupStep σ (.path p) (.val (.new r A U ds)) := by
  cases h with
  | flow hf =>
      obtain ⟨rhs, hstep, hclass⟩ := hf.lookupClass hi hwt
      cases hclass with
      | lambda htyped =>
          have heq := hf.envAll_eq
          rw [heq] at hrecord
          obtain ⟨labels, hrecord⟩ := hrecord
          cases hrecord
      | object G₀ G₁ x pT fields hG hp hdefs htag hc₀ hc =>
          exact ⟨_, _, _, _, hstep⟩
      | path G₀ G₁ x pT fields hG hp htyped hc₀ hc =>
          have heq := hf.envSngl_eq
          rw [heq] at hrecord
          obtain ⟨labels, hrecord⟩ := hrecord
          cases hrecord
  | snglTrans hp hq =>
      obtain ⟨labels, hrecord⟩ := hrecord
      cases hrecord

theorem PreciseTyping3.lookupRecordTerminates {G : Ctx} {σ : Sta}
    {p : Path} {T : Typ} (h : PreciseTyping3 G p T)
    (hrecord : RecordType T) (hi : Inert G) (hwf : Wf G)
    (hwt : WellTyped G σ) :
    ∃ v, Lookup σ (.path p) (.val v) := by
  induction hwt generalizing p T with
  | empty =>
      obtain ⟨U, hp⟩ := h.precise2Exists
      have hnamed := hp.toGeneral.pathNamed
      cases p with
      | select av fields =>
          simp only [Path.Named] at hnamed
          obtain ⟨x, rfl⟩ := hnamed
          obtain ⟨S, hb⟩ := hp.receiverBinds
          exact False.elim hb.empty_false
  | @push G σ x v X hwt hxG hxσ hv ih =>
      have hiBase : Inert G := hi.prefix
      have hwfBase : Wf G := hwf.prefix
      have hnamed := h.toGeneral.pathNamed
      cases p with
      | select av fields =>
          simp only [Path.Named] at hnamed
          obtain ⟨y, rfl⟩ := hnamed
          by_cases hyx : y = x
          · subst y
            rcases h.last with hdirect | ⟨target, halias, htarget⟩
            · obtain ⟨r, A, U, ds, hstep⟩ :=
                hdirect.lookupRecordValue hrecord hi (.push hwt hxG hxσ hv)
              exact ⟨_, .one hstep⟩
            · have htargetNamed := htarget.toGeneral.pathNamed
              cases target with
              | select targetVar targetFields =>
                  simp only [Path.Named] at htargetNamed
                  obtain ⟨z, rfl⟩ := htargetNamed
                  by_cases hzx : z = x
                  · subst z
                    have hprefix := halias.lookupSingletonSameReceiver hi hwf
                      (.push hwt hxG hxσ hv)
                    obtain ⟨r, A, U, ds, hstep⟩ :=
                      htarget.lookupRecordValue hrecord hi
                        (.push hwt hxG hxσ hv)
                    exact ⟨_, hprefix.trans (.one hstep)⟩
                  · obtain ⟨prefixFields, nextFields, z', hz'x,
                        hsourcePrefix, hedge, hnextTarget⟩ :=
                      halias.previousReceiver hi hwf rfl rfl (Ne.symm hzx)
                    have hprefix :
                        Lookup (σ.push x v)
                          (.path (.select (.free x) fields))
                          (.path (.select (.free x) prefixFields)) := by
                      rcases hsourcePrefix with hEq | hprefixAlias
                      · cases hEq
                        exact .refl _
                      · exact hprefixAlias.lookupSingletonSameReceiver hi hwf
                          (.push hwt hxG hxσ hv)
                    obtain ⟨runtime, runtimeT, hstep, hruntime, haliases⟩ :=
                      hedge.lookupSingletonAliases hi hwf
                        (.push hwt hxG hxσ hv)
                    obtain ⟨runtimeRoot, runtimeFields, hcross, hruntimeRoot⟩ :=
                      hedge.lookupSingletonCrossReceiver (Ne.symm hz'x) hi
                        (.push hwt hxG hxσ hv)
                    have hruntimeNamed := hruntime.toGeneral.pathNamed
                    cases runtime with
                    | select runtimeVar runtimeFields' =>
                        simp only [Path.Named] at hruntimeNamed
                        obtain ⟨runtimeRoot', rfl⟩ := hruntimeNamed
                        have hsame := lookup_step_functional hstep hcross
                        injection hsame with hpath
                        injection hpath with havar hfields
                        have hrootEq : runtimeRoot' = runtimeRoot := by
                          injection havar
                        have hruntimeNe : runtimeRoot' ≠ x := by
                          intro heq
                          apply hruntimeRoot
                          rw [← hrootEq, heq]
                        have hnextRecord : PreciseTyping3 (G.push x X)
                            (.select (.free z') nextFields) T := by
                          rcases hnextTarget with hEq | hsuffix
                          · rw [hEq]
                            exact .precise htarget
                          · exact hsuffix.snglTrans3 (.precise htarget)
                        have hruntimeRecord : PreciseTyping3 (G.push x X)
                            (.select (.free runtimeRoot') runtimeFields') T :=
                          haliases.transferRecord hi hrecord hnextRecord
                        have hruntimeBase := hruntimeRecord.strengthenPush
                          hi hwfBase hruntimeNe
                        obtain ⟨result, htail⟩ :=
                          ih hruntimeBase hrecord hiBase hwfBase
                        exact ⟨result, hprefix.trans
                          (.step hstep (htail.weakenPush hxσ))⟩
          · have hbase := h.strengthenPush hi hwfBase hyx
            obtain ⟨result, hlookup⟩ := ih hbase hrecord hiBase hwfBase
            exact ⟨result, hlookup.weakenPush hxσ⟩

theorem PreciseTyping2.all_sngl_false {G : Ctx} {p q : Path}
    {S T : Typ} (hi : Inert G)
    (hall : PreciseTyping2 G p (.all S T))
    (hsngl : PreciseTyping2 G p (.sngl q)) : False := by
  cases hall with
  | flow hall =>
      cases hsngl with
      | flow hsngl =>
          have hsource := hall.source_unique hi hsngl
          rw [hall.allSource_eq hi, hsngl.snglSource_eq hi] at hsource
          cases hsource
      | snglTrans hp hq =>
          obtain ⟨R, hrecord⟩ := hall.backtrackRecord
          exact hp.record_sngl_false hi hrecord

theorem PreciseTyping3.invertSngl2_all {G : Ctx} {p q : Path}
    {S T : Typ} (hi : Inert G)
    (hall : PreciseTyping3 G p (.all S T))
    (hsngl : PreciseTyping2 G p (.sngl q)) :
    PreciseTyping3 G q (.all S T) := by
  generalize heq : Typ.all S T = U at hall
  induction hall generalizing S T with
  | precise hall =>
      cases heq
      exact False.elim (hall.all_sngl_false hi hsngl)
  | snglTrans hs hall ih =>
      cases heq
      have hq := hs.snglTarget_unique hi hsngl
      subst q
      exact hall

theorem PreciseTyping3.invertSngl_all {G : Ctx} {p q : Path}
    {S T : Typ} (hi : Inert G)
    (hall : PreciseTyping3 G p (.all S T))
    (hsngl : PreciseTyping3 G p (.sngl q)) :
    PreciseTyping3 G q (.all S T) := by
  generalize heq : Typ.sngl q = U at hsngl
  induction hsngl generalizing q with
  | precise hsngl =>
      cases heq
      exact hall.invertSngl2_all hi hsngl
  | snglTrans hs hrest ih =>
      have hmiddle := hall.invertSngl2_all hi hs
      exact ih hmiddle heq

theorem PreciseAliases.transferAll {G : Ctx} {p q : Path} {S T : Typ}
    (hi : Inert G) (h : PreciseAliases G p q)
    (hp : PreciseTyping3 G p (.all S T)) :
    PreciseTyping3 G q (.all S T) := by
  obtain ⟨r, hpr, hqr⟩ := h
  have hr : PreciseTyping3 G r (.all S T) := by
    rcases hpr with rfl | hpr
    · exact hp
    · exact hp.invertSngl_all hi hpr
  rcases hqr with rfl | hqr
  · exact hr
  · exact hqr.snglTrans3 hr

theorem PreciseTyping2.lookupAllValue {G : Ctx} {σ : Sta}
    {p : Path} {S T : Typ} (h : PreciseTyping2 G p (.all S T))
    (hi : Inert G) (hwt : WellTyped G σ) :
    ∃ S' body, LookupStep σ (.path p) (.val (.lambda S' body)) ∧
      Typed G (.val (.lambda S' body)) (.all S T) := by
  cases h with
  | flow hf =>
      have hsource := hf.allSource_eq hi
      rw [hsource] at hf
      obtain ⟨rhs, hstep, hclass⟩ := hf.lookupClass hi hwt
      cases hclass with
      | lambda htyped => exact ⟨_, _, hstep, htyped⟩

theorem PreciseTyping3.lookupAllTerminates {G : Ctx} {σ : Sta}
    {p : Path} {S T : Typ} (h : PreciseTyping3 G p (.all S T))
    (hi : Inert G) (hwf : Wf G) (hwt : WellTyped G σ) :
    ∃ S' body, Lookup σ (.path p) (.val (.lambda S' body)) ∧
      Typed G (.val (.lambda S' body)) (.all S T) := by
  induction hwt generalizing p S T with
  | empty =>
      obtain ⟨U, hp⟩ := h.precise2Exists
      have hnamed := hp.toGeneral.pathNamed
      cases p with
      | select av fields =>
          simp only [Path.Named] at hnamed
          obtain ⟨x, rfl⟩ := hnamed
          obtain ⟨R, hb⟩ := hp.receiverBinds
          exact False.elim hb.empty_false
  | @push G σ x v X hwt hxG hxσ hv ih =>
      have hiBase : Inert G := hi.prefix
      have hwfBase : Wf G := hwf.prefix
      have hnamed := h.toGeneral.pathNamed
      cases p with
      | select av fields =>
          simp only [Path.Named] at hnamed
          obtain ⟨y, rfl⟩ := hnamed
          by_cases hyx : y = x
          · subst y
            rcases h.last with hdirect | ⟨target, halias, htarget⟩
            · obtain ⟨S', body, hstep, htyped⟩ :=
                hdirect.lookupAllValue hi (.push hwt hxG hxσ hv)
              exact ⟨S', body, .one hstep, htyped⟩
            · have htargetNamed := htarget.toGeneral.pathNamed
              cases target with
              | select targetVar targetFields =>
                  simp only [Path.Named] at htargetNamed
                  obtain ⟨z, rfl⟩ := htargetNamed
                  by_cases hzx : z = x
                  · subst z
                    have hprefix := halias.lookupSingletonSameReceiver hi hwf
                      (.push hwt hxG hxσ hv)
                    obtain ⟨S', body, hstep, htyped⟩ :=
                      htarget.lookupAllValue hi (.push hwt hxG hxσ hv)
                    exact ⟨S', body, hprefix.trans (.one hstep), htyped⟩
                  · obtain ⟨prefixFields, nextFields, z', hz'x,
                        hsourcePrefix, hedge, hnextTarget⟩ :=
                      halias.previousReceiver hi hwf rfl rfl (Ne.symm hzx)
                    have hprefix :
                        Lookup (σ.push x v)
                          (.path (.select (.free x) fields))
                          (.path (.select (.free x) prefixFields)) := by
                      rcases hsourcePrefix with hEq | hprefixAlias
                      · cases hEq
                        exact .refl _
                      · exact hprefixAlias.lookupSingletonSameReceiver hi hwf
                          (.push hwt hxG hxσ hv)
                    obtain ⟨runtime, runtimeT, hstep, hruntime, haliases⟩ :=
                      hedge.lookupSingletonAliases hi hwf
                        (.push hwt hxG hxσ hv)
                    obtain ⟨runtimeRoot, runtimeFields, hcross, hruntimeRoot⟩ :=
                      hedge.lookupSingletonCrossReceiver (Ne.symm hz'x) hi
                        (.push hwt hxG hxσ hv)
                    have hruntimeNamed := hruntime.toGeneral.pathNamed
                    cases runtime with
                    | select runtimeVar runtimeFields' =>
                        simp only [Path.Named] at hruntimeNamed
                        obtain ⟨runtimeRoot', rfl⟩ := hruntimeNamed
                        have hsame := lookup_step_functional hstep hcross
                        injection hsame with hpath
                        injection hpath with havar hfields
                        have hrootEq : runtimeRoot' = runtimeRoot := by
                          injection havar
                        have hruntimeNe : runtimeRoot' ≠ x := by
                          intro heq
                          apply hruntimeRoot
                          rw [← hrootEq, heq]
                        have hnextAll : PreciseTyping3 (G.push x X)
                            (.select (.free z') nextFields) (.all S T) := by
                          rcases hnextTarget with hEq | hsuffix
                          · rw [hEq]
                            exact .precise htarget
                          · exact hsuffix.snglTrans3 (.precise htarget)
                        have hruntimeAll : PreciseTyping3 (G.push x X)
                            (.select (.free runtimeRoot') runtimeFields')
                            (.all S T) := haliases.transferAll hi hnextAll
                        have hruntimeBase := hruntimeAll.strengthenPush
                          hi hwfBase hruntimeNe
                        obtain ⟨S', body, htail, htyped⟩ :=
                          ih hruntimeBase hiBase hwfBase
                        exact ⟨S', body, hprefix.trans
                          (.step hstep (htail.weakenPush hxσ)),
                          htyped.mono (.pushRight hxG X)⟩
          · have hbase := h.strengthenPush hi hwfBase hyx
            obtain ⟨S', body, hlookup, htyped⟩ :=
              ih hbase hiBase hwfBase
            exact ⟨S', body, hlookup.weakenPush hxσ,
              htyped.mono (.pushRight hxG X)⟩

theorem PreciseTyping2.lookupSingleton {G : Ctx} {σ : Sta}
    {p q : Path} (h : PreciseTyping2 G p (.sngl q))
    (hi : Inert G) (hwt : WellTyped G σ) :
    ∃ r, LookupStep σ (.path p) (.path r) := by
  generalize heq : Typ.sngl q = T at h
  induction h generalizing q with
  | flow h =>
      cases heq
      have hsource := h.snglSource_eq hi
      rw [hsource] at h
      obtain ⟨rhs, hstep, hclass⟩ := h.lookupClass hi hwt
      cases hclass with
      | path _ _ _ _ _ _ _ _ _ _ => exact ⟨_, hstep⟩
  | snglTrans hp hq ihp ihq =>
      cases heq
      obtain ⟨r, hstep⟩ := ihp rfl
      exact ⟨_, .selectPath hstep⟩

theorem PreciseTyping2.lookupExists {G : Ctx} {σ : Sta} {p : Path} {T : Typ}
    (h : PreciseTyping2 G p T) (hi : Inert G) (hwt : WellTyped G σ) :
    ∃ rhs, LookupStep σ (.path p) rhs := by
  cases h with
  | flow h =>
      obtain ⟨rhs, hstep, hclass⟩ := h.lookupClass hi hwt
      exact ⟨rhs, hstep⟩
  | snglTrans hp hq =>
      obtain ⟨r, hstep⟩ := hp.lookupSingleton hi hwt
      exact ⟨_, .selectPath hstep⟩

theorem PreciseTyping3.lookupExists {G : Ctx} {σ : Sta} {p : Path} {T : Typ}
    (h : PreciseTyping3 G p T) (hi : Inert G) (hwt : WellTyped G σ) :
    ∃ rhs, LookupStep σ (.path p) rhs := by
  cases h with
  | precise h =>
      exact h.lookupExists hi hwt
  | snglTrans hp hq =>
      obtain ⟨r, hstep⟩ := hp.lookupSingleton hi hwt
      exact ⟨_, hstep⟩

theorem PreciseTyping3.lookupAll {G : Ctx} {σ : Sta} {p : Path} {S T : Typ}
    (h : PreciseTyping3 G p (.all S T))
    (hi : Inert G) (hwt : WellTyped G σ) :
    (∃ q, LookupStep σ (.path p) (.path q)) ∨
    (∃ S' body, LookupStep σ (.path p) (.val (.lambda S' body)) ∧
      Typed G (.val (.lambda S' body)) (.all S T)) := by
  cases h with
  | precise hp =>
      cases hp with
      | flow hf =>
          have hsource := hf.allSource_eq hi
          rw [hsource] at hf
          obtain ⟨rhs, hstep, hclass⟩ := hf.lookupClass hi hwt
          cases hclass with
          | lambda hv => exact Or.inr ⟨_, _, hstep, hv⟩
  | snglTrans hp hq =>
      obtain ⟨r, hstep⟩ := hp.lookupSingleton hi hwt
      exact Or.inl ⟨r, hstep⟩

theorem PreciseTyping2.lookupObjectTag {G : Ctx} {σ : Sta} {p : Path}
    {T U : Typ} {r : Path} {A : Signature.TypLabel} {ds : Defs}
    (h : PreciseTyping2 G p T)
    (hstep : LookupStep σ (.path p) (.val (.new r A U ds)))
    (hi : Inert G) (hwt : WellTyped G σ) :
    Typed G (.path p) ((.path r A : Typ).openPath p) := by
  cases h with
  | flow hf =>
      obtain ⟨rhs, hcanonical, hclass⟩ := hf.lookupClass hi hwt
      have heq := lookup_step_functional hcanonical hstep
      subst rhs
      cases hclass with
      | object G₀ G₁ x pT fields hG hp hdefs htag hc₀ hc => exact htag
  | snglTrans hp hq =>
      obtain ⟨q', hpath⟩ := hp.lookupSingleton hi hwt
      have heq := lookup_step_functional (LookupStep.selectPath hpath) hstep
      cases heq

theorem PreciseTyping3.lookupObjectTag {G : Ctx} {σ : Sta} {p : Path}
    {T U : Typ} {r : Path} {A : Signature.TypLabel} {ds : Defs}
    (h : PreciseTyping3 G p T)
    (hstep : LookupStep σ (.path p) (.val (.new r A U ds)))
    (hi : Inert G) (hwt : WellTyped G σ) :
    Typed G (.path p) ((.path r A : Typ).openPath p) := by
  cases h with
  | precise hp => exact hp.lookupObjectTag hstep hi hwt
  | snglTrans hp hq =>
      obtain ⟨q', hpath⟩ := hp.lookupSingleton hi hwt
      have heq := lookup_step_functional hpath hstep
      cases heq

theorem Typed.pathLookupExists {G : Ctx} {σ : Sta} {p : Path} {T : Typ}
    (h : Typed G (.path p) T) (hi : Inert G) (hwt : WellTyped G σ) :
    ∃ rhs, LookupStep σ (.path p) rhs := by
  obtain ⟨U, hp⟩ := h.precise3Exists hi
  exact hp.lookupExists hi hwt

theorem Typed.pathProgress {G : Ctx} {σ : Sta} {p : Path} {T : Typ}
    (h : Typed G (.path p) T) (hi : Inert G) (hwt : WellTyped G σ) :
    NormalForm σ (.path p) ∨ ∃ state, Red (σ, .path p) state := by
  obtain ⟨rhs, hstep⟩ := h.pathLookupExists hi hwt
  cases rhs with
  | path q => exact Or.inr ⟨(σ, .path q), .resolve hstep⟩
  | val v => exact Or.inl (.path ⟨v, hstep⟩)

theorem Typed.pathSelectionRecord {G : Ctx} {p q : Path}
    {A : Signature.TypLabel}
    (h : Typed G (.path p) (.path q A)) (hi : Inert G) :
    ∃ T, PreciseTyping3 G q (.rcd (.typ A T T)) := by
  obtain ⟨T, hq, hp⟩ :=
    ((h.toTight hi).pathReplacement hi).pathSelExists hi
  exact ⟨T, hq⟩

theorem Typed.pathSelectionLookupTerminates {G : Ctx} {σ : Sta}
    {p q : Path} {A : Signature.TypLabel}
    (h : Typed G (.path p) (.path q A))
    (hi : Inert G) (hwf : Wf G) (hwt : WellTyped G σ) :
    ∃ v, Lookup σ (.path q) (.val v) := by
  obtain ⟨T, hq⟩ := h.pathSelectionRecord hi
  have hrecord : RecordType (.rcd (.typ A T T)) :=
    ⟨{Label.typ A}, .one .typ rfl⟩
  exact hq.lookupRecordTerminates hrecord hi hwf hwt

theorem Lookup.toFinalStep {σ : Sta} {p : Path} {v : Val}
    (h : Lookup σ (.path p) (.val v)) :
    ∃ q, Lookup σ (.path p) (.path q) ∧
      LookupStep σ (.path q) (.val v) := by
  generalize hsrc : DefRhs.path p = src at h
  generalize hdst : DefRhs.val v = dst at h
  induction h generalizing p v with
  | refl => cases hsrc.trans hdst.symm
  | @step _ middle _ hstep hrest ih =>
      cases middle with
      | path q =>
          obtain ⟨r, hprefix, hfinal⟩ := ih rfl hdst
          rw [← hsrc] at hstep
          rw [← hdst] at hfinal
          rw [← hsrc, ← hdst]
          exact ⟨r, (Star.one hstep).trans hprefix, hfinal⟩
      | val w =>
          have heq := lookup_val_inv hrest
          have hwv : w = v := by
            symm
            injection hdst.trans heq
          subst w
          rw [← hsrc] at hstep
          rw [← hsrc, ← hdst]
          exact ⟨p, .refl _, hstep⟩

theorem Typed.resolvePathSelection {G : Ctx} {σ : Sta}
    {p q : Path} {A : Signature.TypLabel}
    (h : Typed G (.path p) (.path q A))
    (hi : Inert G) (hwf : Wf G) (hwt : WellTyped G σ) :
    ∃ v r, Lookup σ (.path q) (.path r) ∧
      LookupStep σ (.path r) (.val v) := by
  obtain ⟨v, hlookup⟩ := h.pathSelectionLookupTerminates hi hwf hwt
  obtain ⟨r, hprefix, hfinal⟩ := hlookup.toFinalStep
  exact ⟨v, r, hprefix, hfinal⟩

theorem Typed.canonicalFunction {G : Ctx} {σ : Sta}
    {p : Path} {S T : Typ} (h : Typed G (.path p) (.all S T))
    (hi : Inert G) (hwf : Wf G) (hwt : WellTyped G σ) :
    ∃ L : Vars, ∃ S' body,
      Lookup σ (.path p) (.val (.lambda S' body)) ∧
      Subtyp G S S' ∧
      ∀ y, y ∉ L →
        Typed (G.push y S) (body.open y) (T.open y) := by
  obtain ⟨S₀, T₀, L₀, hp, hdom₀, hbody₀⟩ := h.pathAllToPrecise hi
  obtain ⟨S₁, body, hlookup, hlambda⟩ :=
    hp.lookupAllTerminates hi hwf hwt
  obtain ⟨L₁, S₂, body', heq, hdom₁, hbody₁⟩ :=
    hlambda.valAllToLambda hi
  cases heq
  let L : Vars := (L₀ ∪ L₁) ∪ G.dom
  refine ⟨L, S₁, body, hlookup, hdom₀.trans hdom₁, ?_⟩
  intro y hy
  simp only [L, Finset.mem_union, not_or] at hy
  have hyL₀ : y ∉ L₀ := hy.1.1
  have hyL₁ : y ∉ L₁ := hy.1.2
  have hyG : Env.Fresh y G := hy.2
  have hokS : Env.Ok (G.push y S) := Env.okPush hi.ok hyG
  have hokS₀ : Env.Ok (G.push y S₀) := Env.okPush hi.ok hyG
  have hnarrow := (hbody₁ y hyL₁).narrow
    (Subenv.last hdom₀ hokS hokS₀)
  exact .sub hnarrow (hbody₀ y hyL₀)

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
