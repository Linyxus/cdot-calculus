import CDot.Weakening

/-!
# Precise flow

The value-precise and first-level path-precise judgments from
`cdot/PreciseFlow.v`.
-/

namespace CDot

variable [Signature]

inductive PreciseVal : Ctx → Val → Typ → Prop where
  | allIntro (L : Vars) :
      (∀ x, x ∉ L → Typed (G.push x T) (t.open x) (U.open x)) →
      PreciseVal G (.lambda T t) (.all T U)
  | newIntro (L : Vars) :
      (∀ x, x ∉ L →
        TypedDefs x [] (G.push x (T.open x)) (ds.open x) (T.open x)) →
      (∀ x, x ∉ L →
        Typed (G.push x (T.open x)) (.path (.var x)) ((.path p A : Typ).open x)) →
      PreciseVal G (.new p A T ds) (.bnd T)

inductive PreciseFlow : Ctx → Path → Typ → Typ → Prop where
  | bind : Env.Ok G → Env.Binds x T G → PreciseFlow G (.var x) T T
  | fld : PreciseFlow G p T (.rcd (.trm a U)) →
      PreciseFlow G (p.selectField a) U U
  | open : PreciseFlow G p T (.bnd U) → PreciseFlow G p T (U.openPath p)
  | andLeft : PreciseFlow G p T (.and U₁ U₂) → PreciseFlow G p T U₁
  | andRight : PreciseFlow G p T (.and U₁ U₂) → PreciseFlow G p T U₂

theorem PreciseFlow.toGeneralBoth {G : Ctx} {p : Path} {T U : Typ}
    (h : PreciseFlow G p T U) : Typed G (.path p) T ∧ Typed G (.path p) U := by
  induction h with
  | bind _ hb =>
    have ht : Typed _ (.path _) _ := .var hb
    exact ⟨ht, ht⟩
  | fld _ ih =>
    have ht := Typed.newElim ih.2
    exact ⟨ht, ht⟩
  | «open» _ ih => exact ⟨ih.1, Typed.recElim ih.2⟩
  | andLeft _ ih => exact ⟨ih.1, (Typed.sub ih.2 Subtyp.andLeft)⟩
  | andRight _ ih => exact ⟨ih.1, (Typed.sub ih.2 Subtyp.andRight)⟩

theorem PreciseFlow.toGeneral {G : Ctx} {p : Path} {T U : Typ}
    (h : PreciseFlow G p T U) : Typed G (.path p) U := h.toGeneralBoth.2

theorem PreciseVal.toGeneral {G : Ctx} {v : Val} {T : Typ}
    (h : PreciseVal G v T) : Typed G (.val v) T := by
  cases h with
  | allIntro L hbody => exact .allIntro L hbody
  | newIntro L hdefs hself => exact .newIntro L hdefs hself

theorem Inert.bindsTyp {G : Ctx} {x : Var} {T : Typ}
    (hi : Inert G) (hb : Env.Binds x T G) : InertTyp T := by
  induction hi with
  | empty => exact False.elim hb.empty_false
  | @push G y U hi hU hf ih =>
      cases hb with
      | here => exact hU
      | there hne hb => exact ih hb

theorem PreciseFlow.sourceNamed {G : Ctx} {p : Path} {T U : Typ}
    (h : PreciseFlow G p T U) : p.Named :=
  h.toGeneral.pathNamed

theorem PreciseFlow.reset {G : Ctx} {p : Path} {T U : Typ}
    (h : PreciseFlow G p T U) : PreciseFlow G p T T := by
  induction h with
  | bind hok hb => exact .bind hok hb
  | fld h ih => exact .fld h
  | «open» h ih => exact ih
  | andLeft h ih => exact ih
  | andRight h ih => exact ih

theorem PreciseFlow.mono {G G' : Ctx} {p : Path} {T U : Typ}
    (h : PreciseFlow G p T U) (he : Env.Extends G G') (hok : Env.Ok G') :
    PreciseFlow G' p T U := by
  induction h with
  | bind _ hb => exact .bind hok (he hb)
  | fld _ ih => exact .fld ih
  | «open» _ ih => exact .open ih
  | andLeft _ ih => exact .andLeft ih
  | andRight _ ih => exact .andRight ih

theorem PreciseFlow.envAll_eq {G : Ctx} {p : Path} {S T U : Typ}
    (h : PreciseFlow G p (.all S T) U) : U = .all S T := by
  generalize heq : Typ.all S T = E at h
  induction h with
  | bind _ _ => rfl
  | fld _ _ => rfl
  | «open» _ ih =>
      have := ih heq
      rw [← heq] at this
      contradiction
  | andLeft _ ih =>
      have := ih heq
      rw [← heq] at this
      contradiction
  | andRight _ ih =>
      have := ih heq
      rw [← heq] at this
      contradiction

theorem PreciseFlow.envSngl_eq {G : Ctx} {p q : Path} {U : Typ}
    (h : PreciseFlow G p (.sngl q) U) : U = .sngl q := by
  generalize heq : Typ.sngl q = E at h
  induction h with
  | bind _ _ => rfl
  | fld _ _ => rfl
  | «open» _ ih =>
      have := ih heq
      rw [← heq] at this
      contradiction
  | andLeft _ ih =>
      have := ih heq
      rw [← heq] at this
      contradiction
  | andRight _ ih =>
      have := ih heq
      rw [← heq] at this
      contradiction

theorem PreciseFlow.backtrackRecord {G : Ctx} {p : Path}
    {a : Signature.TrmLabel} {T U : Typ}
    (h : PreciseFlow G (p.selectField a) T U) :
    ∃ S, PreciseFlow G p S (.rcd (.trm a T)) := by
  generalize heq : p.selectField a = r at h
  induction h with
  | bind hok hb =>
      cases p with
      | select x fields =>
          simp only [Path.selectField, Path.var] at heq
          cases heq
  | fld h ih =>
      rename_i p' S b V
      obtain ⟨rfl, rfl⟩ := Path.selectField_injective heq
      exact ⟨S, h⟩
  | «open» h ih => exact ih heq
  | andLeft h ih => exact ih heq
  | andRight h ih => exact ih heq

theorem PreciseVal.new_type_eq {G : Ctx} {r : Path} {A : Signature.TypLabel}
    {T U : Typ} {ds : Defs} (h : PreciseVal G (.new r A T ds) U) : U = .bnd T := by
  cases h
  rfl

end CDot
