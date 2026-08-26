import CDot.Binding

/-!
# Records and inert types

Lean port of the structural metatheory in `cdot/RecordAndInertTypes.v`.
-/

namespace CDot

variable [Signature]

@[simp] theorem Dec.label_openRec (D : Dec) (x : Var) (n : Nat) :
    (D.openRec n x).label = D.label := by
  cases D <;> rfl

@[simp] theorem Dec.label_openRecPath (D : Dec) (p : Path) (n : Nat) :
    (D.openRecPath n p).label = D.label := by
  cases D <;> rfl

mutual
  theorem RecordDec.openRecPath {D : Dec} (h : RecordDec D)
      (p : Path) (n : Nat) : RecordDec (D.openRecPath n p) := by
    cases h with
    | typ => exact .typ
    | trm h => exact .trm (h.openRecPath p n)
    | trmSngl => exact .trmSngl

  theorem RecordTyp.openRecPath {T : Typ} {labels : Finset Label}
      (h : RecordTyp T labels) (p : Path) (n : Nat) :
      RecordTyp (T.openRecPath n p) labels := by
    cases h with
    | one hdec heq =>
      exact .one (hdec.openRecPath p n) (by simpa only [Dec.label_openRecPath] using heq)
    | cons htyp hdec heq hfresh =>
      exact .cons (htyp.openRecPath p n) (hdec.openRecPath p n)
        (by simpa only [Dec.label_openRecPath] using heq) hfresh

  theorem InertTyp.openRecPath {T : Typ} (h : InertTyp T)
      (p : Path) (n : Nat) : InertTyp (T.openRecPath n p) := by
    cases h with
    | all => exact .all
    | bnd htyp => exact .bnd (htyp.openRecPath p (n + 1))
end

theorem RecordTyp.openPath {T : Typ} {labels : Finset Label}
    (h : RecordTyp T labels) (p : Path) : RecordTyp (T.openPath p) labels :=
  h.openRecPath p 0

theorem RecordType.openPath {T : Typ} (h : RecordType T) (p : Path) :
    RecordType (T.openPath p) := by
  obtain ⟨labels, htyp⟩ := h
  exact ⟨labels, htyp.openPath p⟩

mutual
  theorem RecordDec.closeOpenRecPath {D : Dec} (h : RecordDec D)
      {D' : Dec} (p : Path) (n : Nat) (ht : D'.tightBounds)
      (heq : D = D'.openRecPath n p) : RecordDec D' := by
    cases h with
    | typ =>
        cases D' <;> simp_all [Dec.openRecPath, Dec.tightBounds]
        exact .typ
    | trm hT =>
        cases D' <;> simp_all [Dec.openRecPath, Dec.tightBounds]
        exact .trm (hT.closeOpenRecPath p n ht rfl)
    | trmSngl =>
        cases D' with
        | typ => simp_all [Dec.openRecPath]
        | trm a T =>
            cases T <;> simp_all [Dec.openRecPath, Typ.openRecPath]
            exact .trmSngl

  theorem RecordTyp.closeOpenRecPath {T : Typ} {labels : Finset Label}
      (h : RecordTyp T labels) {T' : Typ} (p : Path) (n : Nat)
      (ht : T'.tightBounds) (heq : T = T'.openRecPath n p) :
      RecordTyp T' labels := by
    cases h with
    | one hD hl =>
        cases T' <;> simp_all [Typ.openRecPath, Typ.tightBounds]
        exact .one (hD.closeOpenRecPath p n ht rfl) rfl
    | cons hT hD hl hf =>
        cases T' <;> simp_all [Typ.openRecPath, Typ.tightBounds]
        rename_i S R
        cases R <;> simp_all [Typ.openRecPath, Typ.tightBounds]
        exact .cons
          (hT.closeOpenRecPath p n ht.1 rfl)
          (hD.closeOpenRecPath p n ht.2 rfl)
          rfl hf

  theorem InertTyp.closeOpenRecPath {T : Typ} (h : InertTyp T)
      {T' : Typ} (p : Path) (n : Nat) (ht : T'.tightBounds)
      (heq : T = T'.openRecPath n p) : InertTyp T' := by
    cases h with
    | all =>
        cases T' <;> simp_all [Typ.openRecPath, Typ.tightBounds]
        exact .all
    | bnd hT =>
        cases T' <;> simp_all [Typ.openRecPath, Typ.tightBounds]
        exact .bnd (hT.closeOpenRecPath p (n + 1) ht rfl)
end

theorem RecordType.closeOpenPath {T T' : Typ} (h : RecordType T)
    (p : Path) (ht : T'.tightBounds) (heq : T = T'.openPath p) :
    RecordType T' := by
  obtain ⟨labels, hrecord⟩ := h
  exact ⟨labels, hrecord.closeOpenRecPath p 0 ht heq⟩

mutual
  theorem RecordDec.closeOpenRec {D : Dec} (h : RecordDec D)
      {D' : Dec} (x : Var) (n : Nat) (hf : x ∉ D'.fv)
      (heq : D = D'.openRec n x) : RecordDec D' := by
    cases h with
    | typ =>
        cases D' with
        | typ A S U =>
            simp only [Dec.openRec] at heq
            injection heq with hA hS hU
            simp only [Dec.fv, Finset.mem_union, not_or] at hf
            have heq' := Typ.openRec_injective_of_fresh hf.1 hf.2
              (hS.symm.trans hU)
            subst U
            exact .typ
        | trm => simp_all [Dec.openRec]
    | trm hT =>
        cases D' <;> simp_all [Dec.openRec]
        exact .trm (hT.closeOpenRec x n hf
          (Typ.openRec_eq_openRecPath_var x _ n).symm)
    | trmSngl =>
        cases D' with
        | typ => simp_all [Dec.openRec]
        | trm a T =>
            cases T <;> simp_all [Dec.openRec, Typ.openRec]
            exact .trmSngl

  theorem RecordTyp.closeOpenRec {T : Typ} {labels : Finset Label}
      (h : RecordTyp T labels) {T' : Typ} (x : Var) (n : Nat)
      (hf : x ∉ T'.fv) (heq : T = T'.openRec n x) :
      RecordTyp T' labels := by
    cases h with
    | one hD hl =>
        cases T' <;> simp_all [Typ.openRec]
        exact .one (hD.closeOpenRec x n hf
          (Dec.openRec_eq_openRecPath_var x _ n).symm) rfl
    | cons hT hD hl hlabel =>
        cases T' with
        | and S R =>
            simp only [Typ.openRec] at heq
            injection heq with hTS hR
            simp only [Typ.fv, Finset.mem_union, not_or] at hf
            cases R with
            | rcd E =>
                simp only [Typ.openRec] at hR
                injection hR with hDE
                have hlabelEq := congrArg Dec.label hDE
                simp only [Dec.label_openRec] at hlabelEq
                exact .cons
                  (hT.closeOpenRec x n hf.1 hTS)
                  (hD.closeOpenRec x n hf.2 hDE)
                  (hl.trans hlabelEq) (by simpa only [← hlabelEq] using hlabel)
            | _ => simp_all [Typ.openRec]
        | _ => simp_all [Typ.openRec]

  theorem InertTyp.closeOpenRec {T : Typ} (h : InertTyp T)
      {T' : Typ} (x : Var) (n : Nat) (hf : x ∉ T'.fv)
      (heq : T = T'.openRec n x) : InertTyp T' := by
    cases h with
    | all =>
        cases T' <;> simp_all [Typ.openRec]
        exact .all
    | bnd hT =>
        cases T' <;> simp_all [Typ.openRec]
        exact .bnd (hT.closeOpenRec x (n + 1) hf
          (Typ.openRec_eq_openRecPath_var x _ (n + 1)).symm)
end

theorem RecordType.closeOpen {T T' : Typ} (h : RecordType T)
    (x : Var) (hf : x ∉ T'.fv) (heq : T = T'.open x) :
    RecordType T' := by
  obtain ⟨labels, hrecord⟩ := h
  exact ⟨labels, hrecord.closeOpenRec x 0 hf heq⟩

theorem RecordTyp.has_label {T : Typ} {D : Dec} {labels : Finset Label}
    (htyp : RecordTyp T labels) (hhas : RecordHas T D) : D.label ∈ labels := by
  cases htyp with
  | one hdec heq =>
    cases hhas with
    | one => simpa only [heq] using Finset.mem_singleton_self D.label
  | cons hrest hdec heq hfresh =>
    cases hhas with
    | andLeft hhas =>
      exact Finset.mem_union_left _ (RecordTyp.has_label hrest hhas)
    | andRight hhas =>
      cases hhas with
      | one =>
        apply Finset.mem_union_right
        simpa only [heq] using Finset.mem_singleton_self D.label
termination_by sizeOf T
decreasing_by
  simp_all
  omega

theorem RecordTyp.has_recordDec {T : Typ} {D : Dec} {labels : Finset Label}
    (htyp : RecordTyp T labels) (hhas : RecordHas T D) : RecordDec D := by
  cases htyp with
  | one hdec heq =>
      cases hhas
      exact hdec
  | cons hrest hdec heq hfresh =>
      cases hhas with
      | andLeft hhas => exact hrest.has_recordDec hhas
      | andRight hhas =>
          cases hhas
          exact hdec
termination_by sizeOf T
decreasing_by
  simp_all
  omega

theorem RecordTyp.has_unique {T : Typ} {labels : Finset Label}
    {D₁ D₂ : Dec} (htyp : RecordTyp T labels)
    (h₁ : RecordHas T D₁) (h₂ : RecordHas T D₂)
    (hlab : D₁.label = D₂.label) : D₁ = D₂ := by
  cases htyp with
  | one hdec heq =>
      cases h₁
      cases h₂
      rfl
  | cons hrest hdec heq hfresh =>
      cases h₁ with
      | andLeft h₁ =>
          cases h₂ with
          | andLeft h₂ => exact hrest.has_unique h₁ h₂ hlab
          | andRight h₂ =>
              cases h₂
              have hmem := hrest.has_label h₁
              exfalso
              apply hfresh
              rw [heq, ← hlab]
              exact hmem
      | andRight h₁ =>
          cases h₁
          cases h₂ with
          | andLeft h₂ =>
              have hmem := hrest.has_label h₂
              exfalso
              apply hfresh
              rw [heq, hlab]
              exact hmem
          | andRight h₂ =>
              cases h₂
              rfl
termination_by sizeOf T
decreasing_by
  simp_all
  omega

theorem RecordTyp.typ_member_unique {T : Typ} {labels : Finset Label}
    {A : Signature.TypLabel} {S₁ S₂ : Typ}
    (htyp : RecordTyp T labels)
    (h₁ : RecordHas T (.typ A S₁ S₁))
    (h₂ : RecordHas T (.typ A S₂ S₂)) : S₁ = S₂ := by
  have heq := htyp.has_unique h₁ h₂ rfl
  exact Dec.typ.inj heq |>.2.1

def IsSngl (T : Typ) : Prop := ∃ p, T = .sngl p

def InertSngl (T : Typ) : Prop := InertTyp T ∨ IsSngl T

theorem RecordType.singleTrm {a : Signature.TrmLabel} {T : Typ}
    (h : RecordType (.rcd (.trm a T))) : InertSngl T := by
  obtain ⟨labels, h⟩ := h
  cases h with
  | one hdec heq =>
      cases hdec with
      | trm h => exact Or.inl h
      | trmSngl => exact Or.inr ⟨_, rfl⟩

theorem RecordType.singleTyp_eq {A : Signature.TypLabel} {S T : Typ}
    (h : RecordType (.rcd (.typ A S T))) : S = T := by
  obtain ⟨labels, h⟩ := h
  cases h with
  | one hdec heq => cases hdec; rfl

theorem RecordType.andLeft {T U : Typ} (h : RecordType (.and T U)) :
    RecordType T := by
  obtain ⟨labels, h⟩ := h
  cases h with
  | cons hT hD heq hfresh => exact ⟨_, hT⟩

theorem RecordType.andRight {T U : Typ} (h : RecordType (.and T U)) :
    RecordType U := by
  obtain ⟨labels, h⟩ := h
  cases h with
  | cons hT hD heq hfresh => exact ⟨_, .one hD heq⟩

theorem InertSngl.rcd_false {D : Dec} (h : InertSngl (.rcd D)) : False := by
  rcases h with h | ⟨p, h⟩
  · cases h
  · cases h

theorem InertSngl.and_false {T U : Typ} (h : InertSngl (.and T U)) : False := by
  rcases h with h | ⟨p, h⟩
  · cases h
  · cases h

theorem RecordType.bnd_false {T : Typ} (h : RecordType (.bnd T)) : False := by
  obtain ⟨labels, h⟩ := h
  cases h

theorem InertSngl.bnd_record {T : Typ} (h : InertSngl (.bnd T)) : RecordType T := by
  rcases h with h | ⟨p, h⟩
  · cases h with
    | bnd h => exact ⟨_, h⟩
  · cases h

theorem InertSngl.trmRecordType {T : Typ} (h : InertSngl T)
    (a : Signature.TrmLabel) : RecordType (.rcd (.trm a T)) := by
  rcases h with hinert | ⟨p, rfl⟩
  · exact ⟨_, .one (.trm hinert) rfl⟩
  · exact ⟨_, .one .trmSngl rfl⟩

theorem TypedDef.label_eq {x : Var} {fields : Fields} {G : Ctx}
    {d : Def} {D : Dec} (h : TypedDef x fields G d D) :
    d.label = D.label := by
  cases h <;> rfl

theorem TypedDefs.recordTyping {x : Var} {fields : Fields} {G : Ctx}
    {ds : Defs} {T : Typ} (h : TypedDefs x fields G ds T) :
    ∃ labels, RecordTyp T labels ∧
      ∀ l, l ∈ labels → ∃ d, ds.Has d ∧ d.label = l := by
  apply TypedDefs.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ D _ => RecordDec D)
    (motive_3 := fun _ _ _ ds T _ =>
      ∃ labels, RecordTyp T labels ∧
        ∀ l, l ∈ labels → ∃ d, ds.Has d ∧ d.label = l)
    (motive_4 := fun _ _ _ _ => True)
  case typ => exact .typ
  case all =>
    intros
    exact .trm .all
  case new =>
    intro x fields T b G q A ds p hp ht hdefs htag ihdefs ihtag
    obtain ⟨labels, hrecord, _⟩ := ihdefs
    change T.tightBounds at ht
    exact .trm (.bnd
      (hrecord.closeOpenRecPath (p.selectField b) 0 ht rfl))
  case path =>
    intros
    exact .trmSngl
  case one =>
    intro x fields G d D hdef ihdef
    refine ⟨{D.label}, .one ihdef rfl, ?_⟩
    intro l hl
    simp only [Finset.mem_singleton] at hl
    subst l
    exact ⟨d, by simp [Defs.Has, Defs.get], hdef.label_eq⟩
  case cons =>
    intro x fields G ds T d D hdefs hdef hno ihdefs ihdef
    obtain ⟨labels, hrecord, hlabels⟩ := ihdefs
    have hfresh : D.label ∉ labels := by
      intro hmem
      obtain ⟨d', hd', heq⟩ := hlabels _ hmem
      exact hd'.label_ne_of_hasnt hno (heq.trans hdef.label_eq.symm)
    refine ⟨labels ∪ {D.label}, .cons hrecord ihdef rfl hfresh, ?_⟩
    intro l hl
    simp only [Finset.mem_union, Finset.mem_singleton] at hl
    rcases hl with hl | rfl
    · obtain ⟨d', hd', heq⟩ := hlabels _ hl
      have hne := hd'.label_ne_of_hasnt hno
      refine ⟨d', ?_, heq⟩
      unfold Defs.Has at hd' ⊢
      simp only [Defs.get]
      rw [if_neg (Ne.symm hne)]
      exact hd'
    · exact ⟨d, by simp [Defs.Has, Defs.get, hdef.label_eq], hdef.label_eq⟩
  all_goals intros <;> trivial

theorem TypedDefs.recordType {x : Var} {fields : Fields} {G : Ctx}
    {ds : Defs} {T : Typ} (h : TypedDefs x fields G ds T) : RecordType T := by
  obtain ⟨labels, hrecord, _⟩ := h.recordTyping
  exact ⟨labels, hrecord⟩

theorem Inert.prefix {G : Ctx} {x : Var} {T : Typ}
    (h : Inert (G.push x T)) : Inert G := by
  cases h with
  | push h _ _ => exact h

theorem Inert.ok {G : Ctx} (h : Inert G) : Env.Ok G := by
  induction h with
  | empty => exact .nil
  | @push G x T _ _ hfresh ih =>
    exact List.nodup_cons.mpr ⟨by
      simpa only [Env.Fresh, Env.dom, List.mem_toFinset] using hfresh, ih⟩

theorem WellTyped.context_inert_domain_ok {G : Ctx} {σ : Sta}
    (h : WellTyped G σ) :
    List.Nodup (G.map Prod.fst) ∧ List.Nodup (σ.map Prod.fst) := by
  induction h with
  | empty => exact ⟨.nil, .nil⟩
  | @push G σ x T v _ hfg hfs _ ih =>
    constructor
    · exact List.nodup_cons.mpr ⟨by
        simpa only [Env.Fresh, Env.dom, List.mem_toFinset] using hfg, ih.1⟩
    · exact List.nodup_cons.mpr ⟨by
        simpa only [Env.Fresh, Env.dom, List.mem_toFinset] using hfs, ih.2⟩

end CDot
