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

theorem Subtyp.snglPQStar {G : Ctx} {p q : Path} {U S T : Typ}
    (hpq : Typed G (.path p) (.sngl q)) (hq : Typed G (.path q) U)
    (hr : Star (ReplTyp p q) S T) : Subtyp G S T := by
  induction hr with
  | refl => exact .refl
  | step hr hrest ih => exact .trans (.snglPQ hpq hq hr) ih

theorem PreciseAliases.symm {G : Ctx} {p q : Path}
    (h : PreciseAliases G p q) : PreciseAliases G q p := by
  obtain ⟨r, hp, hq⟩ := h
  exact ⟨r, hq, hp⟩

theorem PreciseAliases.typedForward {G : Ctx} {p q : Path}
    {P Q : Typ} (h : PreciseAliases G p q)
    (hp : PreciseTyping3 G p P) (hq : PreciseTyping3 G q Q)
    (hi : Inert G) (hwf : Wf G) : Typed G (.path p) (.sngl q) :=
  h.symm.typedReverse hq hp hi hwf

theorem Typed.lookupPreserves {G : Ctx} {σ : Sta}
    {p q : Path} {T : Typ} (h : Typed G (.path p) T)
    (hlookup : Lookup σ (.path p) (.path q))
    (hi : Inert G) (hwf : Wf G) (hwt : WellTyped G σ) :
    Typed G (.path q) T := by
  generalize hsrc : DefRhs.path p = src at hlookup
  generalize hdst : DefRhs.path q = dst at hlookup
  induction hlookup generalizing p q T with
  | refl =>
      have heq := hsrc.trans hdst.symm
      injection heq with hpq
      subst q
      exact h
  | @step _ middle _ hstep hrest ih =>
      cases middle with
      | path r =>
          rw [← hsrc] at hstep
          have hr := h.lookupPathPreserves hstep hi hwf hwt
          exact ih hr rfl hdst
      | val v =>
          have heq := lookup_val_inv hrest
          rw [← hdst] at heq
          cases heq

theorem Typed.lookupSingleton {G : Ctx} {σ : Sta}
    {p q : Path} {T : Typ} (h : Typed G (.path p) T)
    (hlookup : Lookup σ (.path p) (.path q))
    (hi : Inert G) (hwf : Wf G) (hwt : WellTyped G σ) :
    Typed G (.path p) (.sngl q) := by
  generalize hsrc : DefRhs.path p = src at hlookup
  generalize hdst : DefRhs.path q = dst at hlookup
  induction hlookup generalizing p q T with
  | refl =>
      have heq := hsrc.trans hdst.symm
      injection heq with hpq
      subst q
      exact .self h
  | @step _ middle _ hstep hrest ih =>
      cases middle with
      | path r =>
          rw [← hsrc] at hstep
          obtain ⟨P, hp⟩ := h.precise3Exists hi
          obtain ⟨R, hr, halias⟩ := hp.lookupPathAliases hstep hi hwf hwt
          have hfirst := halias.typedForward hp hr hi hwf
          have hrTyped := h.lookupPathPreserves hstep hi hwf hwt
          have htail := ih hrTyped rfl hdst
          exact .sngl hfirst htail
      | val v =>
          have heq := lookup_val_inv hrest
          rw [← hdst] at heq
          cases heq

theorem Subtyp.andExtendRight {G : Ctx} {S T U : Typ}
    (h : Subtyp G S T) : Subtyp G (.and S U) (.and T U) :=
  .andIntro (.trans .andLeft h) .andRight

theorem Subtyp.andExtendLeft {G : Ctx} {S T U : Typ}
    (h : Subtyp G T U) : Subtyp G (.and S T) (.and S U) :=
  .andIntro .andLeft (.trans .andRight h)

theorem Typed.instantiateNarrowed {G : Ctx} {L : Vars}
    {S T U : Typ} {body : Trm} {x : Var}
    (hi : Inert G) (hxG : Env.Fresh x G)
    (hsub : Subtyp G S T)
    (hbody : ∀ y, y ∉ L → Typed (G.push y T) (body.open y) U) :
    Typed (G.push x S) (body.open x) U := by
  let avoid : Vars := L ∪ G.dom ∪ G.fvTypes ∪ S.fv ∪ T.fv ∪
    U.fv ∪ body.fv ∪ {x}
  obtain ⟨y, hyRange⟩ := Finset.exists_nat_subset_range avoid
  have hy : y ∉ avoid := by
    intro hmem
    exact (Nat.lt_irrefl y) (Finset.mem_range.mp (hyRange hmem))
  have hyL : y ∉ L := by aesop
  have hyG : Env.Fresh y G := by aesop
  have hyCtx : y ∉ G.fvTypes := by aesop
  have hyS : y ∉ S.fv := by aesop
  have hyT : y ∉ T.fv := by aesop
  have hyU : y ∉ U.fv := by aesop
  have hyBody : y ∉ body.fv := by aesop
  have hyx : y ≠ x := by aesop
  have hokS : Env.Ok (G.push y S) := Env.okPush hi.ok hyG
  have hokT : Env.Ok (G.push y T) := Env.okPush hi.ok hyG
  have hnarrow := (hbody y hyL).narrow (Subenv.last hsub hokS hokT)
  have hrenamed := hnarrow.renameLast hyCtx hxG hyx
    (Env.okPush (Env.okPush hi.ok hxG) (by
      intro hmem
      simp only [Env.dom, Env.push, List.map_cons, List.mem_toFinset,
        List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · exact hyx heq
      · exact hyG (by simpa only [Env.dom, List.mem_toFinset] using hmem)))
  have hnamed : (Path.var x).Named := ⟨x, rfl⟩
  simpa only [Typ.subst_eq_self_of_not_mem S hyS,
    Typ.subst_eq_self_of_not_mem U hyU,
    Trm.subst_openRec (.var x) hnamed y y body 0,
    Trm.subst_eq_self_of_not_mem body hyBody,
    Var.substPath, if_true, ← Trm.openRec_eq_openRecPath_var] using hrenamed

theorem Typed.substFreshOpenPathDependent {G : Ctx} {L : Vars}
    {S T : Typ} {body : Trm} {p : Path}
    (hok : Env.Ok G)
    (hbody : ∀ x, x ∉ L →
      Typed (G.push x S) (body.open x) (T.open x))
    (hp : Typed G (.path p) S) :
    Typed G (body.openPath p) (T.openPath p) := by
  let avoid : Vars := L ∪ G.dom ∪ G.fvTypes ∪ S.fv ∪ T.fv ∪ body.fv
  obtain ⟨x, hxRange⟩ := Finset.exists_nat_subset_range avoid
  have hx : x ∉ avoid := by
    intro hmem
    exact (Nat.lt_irrefl x) (Finset.mem_range.mp (hxRange hmem))
  have hxL : x ∉ L := by aesop
  have hxG : Env.Fresh x G := by aesop
  have hxAll : x ∉ G.fvTypes ∪ S.fv ∪ T.fv ∪ body.fv := by aesop
  exact Typed.substOpenPath hok hxG hxAll (hbody x hxL) hp

/-! ## Progress -/

theorem progress {G : Ctx} {σ : Sta} {t : Trm} {T : Typ}
    (hi : Inert G) (hwf : Wf G) (hwt : WellTyped G σ)
    (h : Typed G t T) :
    NormalForm σ t ∨ ∃ state, Red (σ, t) state := by
  apply Typed.rec
    (motive_1 := fun G t T _ => ∀ (hi : Inert G) (hwf : Wf G)
      (σ : Sta), WellTyped G σ →
        NormalForm σ t ∨ ∃ state, Red (σ, t) state)
    (motive_2 := fun _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True)
  case var =>
      intro x T G hb hi hwf σ hwt
      exact (Typed.var hb).pathProgress hi hwt
  case allIntro => intros; exact Or.inl .val
  case newIntro => intros; exact Or.inl .val
  case allElim =>
      intro G p S T q hfun harg ihfun iharg hi hwf σ hwt
      rcases ihfun hi hwf σ hwt with hfunNormal | ⟨state, hfunRed⟩
      · cases hfunNormal with
        | path hfunResolved =>
            obtain ⟨vf, hfunStep⟩ := hfunResolved
            obtain ⟨L, S', body, hlookup, hdom, hbody⟩ :=
              hfun.canonicalFunction hi hwf hwt
            have hvf : vf = .lambda S' body :=
              lookup_functional (.one hfunStep) hlookup
            subst vf
            rcases iharg hi hwf σ hwt with hargNormal | ⟨state, hargRed⟩
            · cases hargNormal with
              | path hargResolved =>
                  exact Or.inr ⟨_, .app hfunStep hargResolved⟩
            · cases hargRed with
              | resolve hargStep =>
                  exact Or.inr ⟨_, .ctxAppArg ⟨_, hfunStep⟩ (.resolve hargStep)⟩
      · cases hfunRed with
        | resolve hfunStep =>
            exact Or.inr ⟨_, .ctxAppFun (.resolve hfunStep)⟩
  case newElim =>
      intro G p a T hpath ih hi hwf σ hwt
      exact hpath.newElim.pathProgress hi hwt
  case rcdIntro =>
      intro G T p a hpath ih hi hwf σ hwt
      exact hpath.rcdIntro.pathProgress hi hwt
  case letE =>
      intro G t₀ T U body L hbound hbody ihbound ihbody hi hwf σ hwt
      rcases ihbound hi hwf σ hwt with hnormal | ⟨state, hred⟩
      · cases hnormal with
        | val =>
            rename_i v
            obtain ⟨x, hx⟩ := Finset.exists_nat_subset_range σ.dom
            have hxfresh : Env.Fresh x σ := by
              intro hmem
              exact (Nat.lt_irrefl x) (Finset.mem_range.mp (hx hmem))
            exact Or.inr ⟨_, .letVal hxfresh⟩
        | path hresolved => exact Or.inr ⟨_, .letPath hresolved⟩
      · exact Or.inr ⟨_, .letTarget hred⟩
  case caseE =>
      intro G p S q U A T bodyElse bodyMatch L hp hq hbody helse
        ihp ihq ihbody ihelse hi hwf σ hwt
      rcases hp.pathProgress hi hwt with hpNormal | ⟨state, hpRed⟩
      · cases hpNormal with
        | path hpResolved =>
            rcases hq.pathProgress hi hwt with hqNormal | ⟨state, hqRed⟩
            · cases hqNormal with
              | path hqResolved =>
                  obtain ⟨vp, hpStep⟩ := hpResolved
                  cases vp with
                  | lambda S body =>
                      exact Or.inr ⟨_, .caseLambda hpStep⟩
                  | new tag A₁ U ds =>
                      obtain ⟨P, hprecise⟩ := hp.precise3Exists hi
                      have htag := hprecise.lookupObjectTag hpStep hi hwt
                      obtain ⟨vtag, resolvedTag, htagLookup, htagFinal⟩ :=
                        htag.resolvePathSelection hi hwf hwt
                      by_cases hpathEq : resolvedTag = q
                      · subst resolvedTag
                        by_cases hlabelEq : A₁ = A
                        · subst A₁
                          exact Or.inr ⟨_, .caseMatch hqResolved hpStep htagLookup⟩
                        · exact Or.inr ⟨_, .caseElse
                            ⟨vtag, htagFinal⟩ hqResolved hpStep htagLookup
                            (Or.inr hlabelEq)⟩
                      · exact Or.inr ⟨_, .caseElse
                          ⟨vtag, htagFinal⟩ hqResolved hpStep htagLookup
                          (Or.inl hpathEq)⟩
            · cases hqRed with
              | resolve hqStep =>
                  exact Or.inr ⟨_, .ctxCaseTag hpResolved (.resolve hqStep)⟩
      · cases hpRed with
        | resolve hpStep =>
            exact Or.inr ⟨_, .ctxCaseScrutinee (.resolve hpStep)⟩
  case sngl =>
      intro G p q T hp hq ihp ihq hi hwf σ hwt
      exact (Typed.sngl hp hq).pathProgress hi hwt
  case self =>
      intro G p T hp ih hi hwf σ hwt
      exact (Typed.self hp).pathProgress hi hwt
  case pathElim =>
      intro G p q a T hp hq ihp ihq hi hwf σ hwt
      exact (Typed.pathElim hp hq).pathProgress hi hwt
  case recIntro =>
      intro G p T hp ih hi hwf σ hwt
      exact (Typed.recIntro hp).pathProgress hi hwt
  case recElim =>
      intro G p T hp ih hi hwf σ hwt
      exact (Typed.recElim hp).pathProgress hi hwt
  case andIntro =>
      intro G p T U hp hq ihp ihq hi hwf σ hwt
      exact (Typed.andIntro hp hq).pathProgress hi hwt
  case sub =>
      intro G t S T ht hs ih iht hi hwf σ hwt
      exact ih hi hwf σ hwt
  all_goals intros <;> trivial

/-! ## Preservation -/

theorem Typed.matchedCaseType {G : Ctx} {σ : Sta}
    {p tag resolvedTag : Path} {A : Signature.TypLabel}
    {U T : Typ} {ds : Defs}
    (hp : Typed G (.path p) U)
    (hobject : LookupStep σ (.path p) (.val (.new tag A T ds)))
    (htag : Lookup σ (.path (tag.openPath p)) (.path resolvedTag))
    (hi : Inert G) (hwf : Wf G) (hwt : WellTyped G σ) :
    Typed G (.path p) (.path resolvedTag A) := by
  obtain ⟨P, hprecise⟩ := hp.precise3Exists hi
  have hselection := hprecise.lookupObjectTag hobject hi hwt
  obtain ⟨R, htagPrecise⟩ := hselection.pathSelectionRecord hi
  have hrecord : RecordType (.rcd (.typ A R R)) :=
    ⟨{Label.typ A}, .one .typ rfl⟩
  have htagTyped := htagPrecise.toGeneral
  have hresolvedTyped := htagTyped.lookupPreserves htag hi hwf hwt
  have hsingleton := htagTyped.lookupSingleton htag hi hwf hwt
  have hsub : Subtyp G (.path (tag.openPath p) A) (.path resolvedTag A) :=
    .snglPQStar hsingleton hresolvedTyped
      (Star.one (ReplTyp.path (fields := [])))
  exact .sub hselection hsub

theorem preservation {G : Ctx} {σ σ' : Sta} {t t' : Trm} {T : Typ}
    (hwt : WellTyped G σ) (hi : Inert G) (hwf : Wf G)
    (hred : Red (σ, t) (σ', t')) (h : Typed G t T) :
    ∃ H, Env.Extends G H ∧ Inert H ∧ Wf H ∧
      WellTyped H σ' ∧ Typed H t' T := by
  apply Typed.rec
    (motive_1 := fun G t T _ => ∀ (σ σ' : Sta) (t' : Trm),
      WellTyped G σ → Inert G → Wf G → Red (σ, t) (σ', t') →
      ∃ H, Env.Extends G H ∧ Inert H ∧ Wf H ∧
        WellTyped H σ' ∧ Typed H t' T)
    (motive_2 := fun _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True)
  case var =>
      intro x T G hb σ σ' t' hwt hi hwf hred
      cases hred with
      | resolve hstep =>
          exact ⟨G, .refl _, hi, hwf, hwt,
            (Typed.var hb).lookupPathPreserves hstep hi hwf hwt⟩
  case allIntro => intros; rename_i hred; cases hred
  case newIntro => intros; rename_i hred; cases hred
  case allElim =>
      intro G p S T q hfun harg ihfun iharg σ σ' target hwt hi hwf hred
      cases hred with
      | app hfunStep hargResolved =>
          obtain ⟨L, S', body, hlookup, hdom, hbody⟩ :=
            hfun.canonicalFunction hi hwf hwt
          have heq := lookup_functional (.one hfunStep) hlookup
          injection heq with hS hterm
          subst S'
          subst body
          have hresult := Typed.substFreshOpenPathDependent hi.ok hbody harg
          exact ⟨G, .refl _, hi, hwf, hwt, hresult⟩
      | ctxAppFun hfunRed =>
          obtain ⟨H, he, hiH, hwfH, hwtH, hfunH⟩ :=
            ihfun σ σ _ hwt hi hwf hfunRed
          exact ⟨H, he, hiH, hwfH, hwtH,
            .allElim hfunH (harg.mono he)⟩
      | ctxAppArg hfunResolved hargRed =>
          obtain ⟨H, he, hiH, hwfH, hwtH, hargH⟩ :=
            iharg σ σ _ hwt hi hwf hargRed
          cases hargRed with
          | resolve hargStep =>
              rename_i q'
              obtain ⟨P, hp⟩ := harg.precise3Exists hi
              obtain ⟨Q, hq', halias⟩ :=
                hp.lookupPathAliases hargStep hi hwf hwt
              have hreverse := halias.typedReverse hp hq' hi hwf
              have hsub : Subtyp G (T.openPath q') (T.openPath q) :=
                .snglPQStar hreverse harg (Typ.openPath_repl T q' q)
              exact ⟨H, he, hiH, hwfH, hwtH,
                .sub (.allElim (hfun.mono he) hargH) (hsub.mono he)⟩
  case newElim =>
      intro G p a T hp ih σ σ' target hwt hi hwf hred
      cases hred with
      | resolve hstep =>
          exact ⟨G, .refl _, hi, hwf, hwt,
            hp.newElim.lookupPathPreserves hstep hi hwf hwt⟩
  case rcdIntro =>
      intro G T p a hp ih σ σ' target hwt hi hwf hred
      cases hred with
      | resolve hstep =>
          exact ⟨G, .refl _, hi, hwf, hwt,
            hp.rcdIntro.lookupPathPreserves hstep hi hwf hwt⟩
  case letE =>
      intro G bound S T body L hbound hbody ihbound ihbody
        σ σ' target hwt hi hwf hred
      cases hred with
      | letVal hxStore =>
          rename_i x v
          have hxG := hwt.freshContext hxStore
          obtain ⟨V, hv, hVS, hVInert, hwfPush⟩ :=
            hbound.valTyping hi hwf hxG
          have hbody' := Typed.instantiateNarrowed hi hxG hVS hbody
          exact ⟨G.push x V, .pushRight hxG V, .push hi hVInert hxG,
            hwfPush, .push hwt hxG hxStore hv.toGeneral, hbody'⟩
      | letPath hresolved =>
          exact ⟨G, .refl _, hi, hwf, hwt,
            Typed.substFreshOpenPath hi.ok hbody hbound⟩
      | letTarget htarget =>
          obtain ⟨H, he, hiH, hwfH, hwtH, hboundH⟩ :=
            ihbound σ σ' _ hwt hi hwf htarget
          exact ⟨H, he, hiH, hwfH, hwtH,
            .letE L hboundH (fun x hx => (hbody x hx).mono (he.push x S))⟩
  case caseE =>
      intro G p S q U A T elseBranch matchBranch L hp hq hbody helse
        ihp ihq ihbody ihelse σ σ' target hwt hi hwf hred
      cases hred with
      | caseMatch hqResolved hpObject htag =>
          have hpTag := hp.matchedCaseType hpObject htag hi hwf hwt
          have hpAnd : Typed G (.path p) (.and (.sngl p) (.path q A)) :=
            .andIntro (.self hp) (by simpa using hpTag)
          exact ⟨G, .refl _, hi, hwf, hwt,
            Typed.substFreshOpenPath hi.ok hbody hpAnd⟩
      | caseElse htagResolved hqResolved hpObject htag hneq =>
          exact ⟨G, .refl _, hi, hwf, hwt, helse⟩
      | caseLambda hpLambda =>
          exact ⟨G, .refl _, hi, hwf, hwt, helse⟩
      | ctxCaseScrutinee hpRed =>
          cases hpRed with
          | resolve hpStep =>
              rename_i p'
              have hp' := hp.lookupPathPreserves hpStep hi hwf hwt
              obtain ⟨P, hpPrecise⟩ := hp.precise3Exists hi
              obtain ⟨P', hp'Precise, halias⟩ :=
                hpPrecise.lookupPathAliases hpStep hi hwf hwt
              have hreverse := halias.typedReverse hpPrecise hp'Precise hi hwf
              have hsngl : Subtyp G (.sngl p') (.sngl p) :=
                .snglPQ hreverse hp (ReplTyp.rootSngl p' p)
              let L' : Vars := L ∪ G.dom
              refine ⟨G, .refl _, hi, hwf, hwt,
                .caseE L' hp' hq ?_ helse⟩
              intro y hy
              simp only [L', Finset.mem_union, not_or] at hy
              have hyG : Env.Fresh y G := hy.2
              exact (hbody y hy.1).narrow
                (Subenv.last hsngl.andExtendRight
                  (Env.okPush hi.ok hyG) (Env.okPush hi.ok hyG))
      | ctxCaseTag hpResolved hqRed =>
          cases hqRed with
          | resolve hqStep =>
              rename_i q'
              have hq' := hq.lookupPathPreserves hqStep hi hwf hwt
              obtain ⟨Q, hqPrecise⟩ := hq.precise3Exists hi
              obtain ⟨Q', hq'Precise, halias⟩ :=
                hqPrecise.lookupPathAliases hqStep hi hwf hwt
              have hreverse := halias.typedReverse hqPrecise hq'Precise hi hwf
              have hpath : Subtyp G (.path q' A) (.path q A) :=
                .snglPQ hreverse hq (ReplTyp.path (fields := []))
              let L' : Vars := L ∪ G.dom
              refine ⟨G, .refl _, hi, hwf, hwt,
                .caseE L' hp hq' ?_ helse⟩
              intro y hy
              simp only [L', Finset.mem_union, not_or] at hy
              have hyG : Env.Fresh y G := hy.2
              exact (hbody y hy.1).narrow
                (Subenv.last hpath.andExtendLeft
                  (Env.okPush hi.ok hyG) (Env.okPush hi.ok hyG))
  case sngl =>
      intro G p q T hp hq ihp ihq σ σ' target hwt hi hwf hred
      cases hred with
      | resolve hstep =>
          exact ⟨G, .refl _, hi, hwf, hwt,
            (Typed.sngl hp hq).lookupPathPreserves hstep hi hwf hwt⟩
  case self =>
      intro G p T hp ih σ σ' target hwt hi hwf hred
      cases hred with
      | resolve hstep =>
          exact ⟨G, .refl _, hi, hwf, hwt,
            (Typed.self hp).lookupPathPreserves hstep hi hwf hwt⟩
  case pathElim =>
      intro G p q a T hp hq ihp ihq σ σ' target hwt hi hwf hred
      cases hred with
      | resolve hstep =>
          exact ⟨G, .refl _, hi, hwf, hwt,
            (Typed.pathElim hp hq).lookupPathPreserves hstep hi hwf hwt⟩
  case recIntro =>
      intro G p T hp ih σ σ' target hwt hi hwf hred
      cases hred with
      | resolve hstep =>
          exact ⟨G, .refl _, hi, hwf, hwt,
            (Typed.recIntro hp).lookupPathPreserves hstep hi hwf hwt⟩
  case recElim =>
      intro G p T hp ih σ σ' target hwt hi hwf hred
      cases hred with
      | resolve hstep =>
          exact ⟨G, .refl _, hi, hwf, hwt,
            (Typed.recElim hp).lookupPathPreserves hstep hi hwf hwt⟩
  case andIntro =>
      intro G p T U hp hq ihp ihq σ σ' target hwt hi hwf hred
      cases hred with
      | resolve hstep =>
          exact ⟨G, .refl _, hi, hwf, hwt,
            (Typed.andIntro hp hq).lookupPathPreserves hstep hi hwf hwt⟩
  case sub =>
      intro G term S T ht hs ih iht σ σ' target hwt hi hwf hred
      obtain ⟨H, he, hiH, hwfH, hwtH, htH⟩ :=
        ih σ σ' target hwt hi hwf hred
      exact ⟨H, he, hiH, hwfH, hwtH, .sub htH (hs.mono he)⟩
  all_goals intros <;> trivial

theorem preservationStar {G : Ctx} {σ σ' : Sta} {t t' : Trm} {T : Typ}
    (hwt : WellTyped G σ) (hi : Inert G) (hwf : Wf G)
    (hred : Reds (σ, t) (σ', t')) (h : Typed G t T) :
    ∃ H, Env.Extends G H ∧ Inert H ∧ Wf H ∧
      WellTyped H σ' ∧ Typed H t' T := by
  generalize hsrc : (σ, t) = source at hred
  generalize hdst : (σ', t') = target at hred
  induction hred generalizing G σ σ' t t' T with
  | refl =>
      have heq := hsrc.trans hdst.symm
      injection heq with hσ ht
      subst σ'
      subst t'
      exact ⟨G, .refl _, hi, hwf, hwt, h⟩
  | @step _ middle _ hstep hrest ih =>
      obtain ⟨σ₁, t₁⟩ := middle
      rw [← hsrc] at hstep
      obtain ⟨H, he, hiH, hwfH, hwtH, htH⟩ :=
        preservation hwt hi hwf hstep h
      obtain ⟨K, heHK, hiK, hwfK, hwtK, htK⟩ :=
        ih hwtH hiH hwfH htH rfl hdst
      exact ⟨K, he.trans heHK, hiK, hwfK, hwtK, htK⟩

def Diverges (state : State) : Prop := InfSeq Red state

def CyclicPath (σ : Sta) (p : Path) : Prop :=
  InfSeq (LookupStep σ) (.path p)

theorem safety {t : Trm} {T : Typ}
    (h : Typed Env.empty t T) :
    Diverges (Env.empty, t) ∨
      ∃ σ u G, Reds (Env.empty, t) (σ, u) ∧
        NormalForm σ u ∧ Typed G u T ∧
        WellTyped G σ ∧ Wf G ∧ Inert G := by
  rcases infSeqOrFinseq (R := Red) (Env.empty, t) with hinf | hfinite
  · exact Or.inl hinf
  · obtain ⟨⟨σ, u⟩, hsteps, hirred⟩ := hfinite
    obtain ⟨G, he, hi, hwf, hwt, hu⟩ :=
      preservationStar .empty .empty .empty hsteps h
    rcases progress hi hwf hwt hu with hnormal | ⟨state, hstep⟩
    · exact Or.inr ⟨σ, u, G, hsteps, hnormal, hu, hwt, hwf, hi⟩
    · exact False.elim (hirred state hstep)

theorem pathSafety {G : Ctx} {σ : Sta} {p : Path} {T : Typ}
    (hi : Inert G) (hwf : Wf G) (hwt : WellTyped G σ)
    (h : Typed G (.path p) T) :
    CyclicPath σ p ∨ ∃ v, Lookup σ (.path p) (.val v) := by
  rcases infSeqOrFinseq (R := LookupStep σ) (DefRhs.path p) with
    hinf | hfinite
  · exact Or.inl hinf
  · obtain ⟨rhs, hlookup, hirred⟩ := hfinite
    cases rhs with
    | val v => exact Or.inr ⟨v, hlookup⟩
    | path q =>
        have hq := h.lookupPreserves hlookup hi hwf hwt
        obtain ⟨next, hstep⟩ := hq.pathLookupExists hi hwt
        exact False.elim (hirred next hstep)

end CDot
