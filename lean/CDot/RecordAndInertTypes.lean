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
