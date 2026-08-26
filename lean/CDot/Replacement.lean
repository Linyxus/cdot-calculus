import CDot.Binding
import CDot.Sequences

/-!
# Path replacement metatheory

Lean port of `cdot/Replacement.v`.
-/

namespace CDot

variable [Signature]

mutual
  theorem ReplTyp.swap {p q T U} (h : ReplTyp p q T U) :
      ReplTyp q p U T := by
    cases h with
    | rcd h => exact .rcd h.swap
    | andLeft h => exact .andLeft h.swap
    | andRight h => exact .andRight h.swap
    | path => exact .path
    | bnd h => exact .bnd h.swap
    | allDom h => exact .allDom h.swap
    | allCod h => exact .allCod h.swap
    | sngl => exact .sngl

  theorem ReplDec.swap {p q D E} (h : ReplDec p q D E) :
      ReplDec q p E D := by
    cases h with
    | typLo h => exact .typLo h.swap
    | typHi h => exact .typHi h.swap
    | trm h => exact .trm h.swap
end

mutual
  theorem ReplTyp.eq_of_paths_eq {p q T U} (h : ReplTyp p q T U)
      (hpq : p = q) : T = U := by
    cases hpq
    cases h with
    | rcd h => exact congrArg Typ.rcd (h.eq_of_paths_eq rfl)
    | andLeft h => exact congrArg (fun T => Typ.and T _) (h.eq_of_paths_eq rfl)
    | andRight h => exact congrArg (fun T => Typ.and _ T) (h.eq_of_paths_eq rfl)
    | path => rfl
    | bnd h => exact congrArg Typ.bnd (h.eq_of_paths_eq rfl)
    | allDom h => exact congrArg (fun T => Typ.all T _) (h.eq_of_paths_eq rfl)
    | allCod h => exact congrArg (fun T => Typ.all _ T) (h.eq_of_paths_eq rfl)
    | sngl => rfl

  theorem ReplDec.eq_of_paths_eq {p q D E} (h : ReplDec p q D E)
      (hpq : p = q) : D = E := by
    cases hpq
    cases h with
    | typLo h => exact congrArg (fun T => Dec.typ _ T _) (h.eq_of_paths_eq rfl)
    | typHi h => exact congrArg (fun T => Dec.typ _ _ T) (h.eq_of_paths_eq rfl)
    | trm h => exact congrArg (fun T => Dec.trm _ T) (h.eq_of_paths_eq rfl)
end

theorem ReplTyp.rootSngl (p q : Path) : ReplTyp p q (.sngl p) (.sngl q) := by
  simpa only [Path.selectFields_nil] using
    (ReplTyp.sngl (p := p) (q := q) (fields := []))

theorem ReplTyp.pathRoot (p q : Path) (A : Signature.TypLabel) :
    ReplTyp p q (.path p A) (.path q A) := by
  simpa only [Path.selectFields_nil] using
    (ReplTyp.path (p := p) (q := q) (fields := []) (A := A))

mutual
  theorem ReplTyp.openRecPath {p q T U} (h : ReplTyp p q T U)
      (hp : p.Named) (hq : q.Named) (r : Path) (n : Nat) :
      ReplTyp p q (T.openRecPath n r) (U.openRecPath n r) := by
    cases h with
    | rcd h => exact .rcd (h.openRecPath hp hq r n)
    | andLeft h => exact .andLeft (h.openRecPath hp hq r n)
    | andRight h => exact .andRight (h.openRecPath hp hq r n)
    | path =>
      simp only [Typ.openRecPath]
      rw [Path.openRecPath_eq_of_named (hp.selectFields _)]
      rw [Path.openRecPath_eq_of_named (hq.selectFields _)]
      exact .path
    | bnd h => exact .bnd (h.openRecPath hp hq r (n + 1))
    | allDom h => exact .allDom (h.openRecPath hp hq r n)
    | allCod h => exact .allCod (h.openRecPath hp hq r (n + 1))
    | sngl =>
      simp only [Typ.openRecPath]
      rw [Path.openRecPath_eq_of_named (hp.selectFields _)]
      rw [Path.openRecPath_eq_of_named (hq.selectFields _)]
      exact .sngl

  theorem ReplDec.openRecPath {p q D E} (h : ReplDec p q D E)
      (hp : p.Named) (hq : q.Named) (r : Path) (n : Nat) :
      ReplDec p q (D.openRecPath n r) (E.openRecPath n r) := by
    cases h with
    | typLo h => exact .typLo (h.openRecPath hp hq r n)
    | typHi h => exact .typHi (h.openRecPath hp hq r n)
    | trm h => exact .trm (h.openRecPath hp hq r n)
end

theorem ReplTyp.openPath {p q T U} (h : ReplTyp p q T U)
    (hp : p.Named) (hq : q.Named) (r : Path) :
    ReplTyp p q (T.openPath r) (U.openPath r) :=
  h.openRecPath hp hq r 0

theorem ReplTyp.openVar {p q T U} (h : ReplTyp p q T U)
    (hp : p.Named) (hq : q.Named) (x : Var) :
    ReplTyp p q (T.open x) (U.open x) := by
  change ReplTyp p q (T.openRec 0 x) (U.openRec 0 x)
  rw [Typ.openRec_eq_openRecPath_var, Typ.openRec_eq_openRecPath_var]
  exact h.openRecPath hp hq (.var x) 0

namespace Star

omit [Signature] in
theorem map {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (preserve : ∀ {a b}, R a b → S (f a) (f b))
    {a b} (h : Star R a b) : Star S (f a) (f b) := by
  induction h with
  | refl a => exact .refl (f a)
  | step hab _ ih => exact .step (preserve hab) ih

end Star

theorem Star.replRcd {p q D E} (h : Star (ReplDec p q) D E) :
    Star (ReplTyp p q) (.rcd D) (.rcd E) :=
  h.map Typ.rcd (fun h => .rcd h)

theorem Star.replAndLeft {p q T U V} (h : Star (ReplTyp p q) T U) :
    Star (ReplTyp p q) (.and T V) (.and U V) :=
  h.map (fun T : Typ => Typ.and T V) (fun h => ReplTyp.andLeft h)

theorem Star.replAndRight {p q T U V} (h : Star (ReplTyp p q) T U) :
    Star (ReplTyp p q) (.and V T) (.and V U) :=
  h.map (fun T : Typ => Typ.and V T) (fun h => ReplTyp.andRight h)

theorem Star.replBnd {p q T U} (h : Star (ReplTyp p q) T U) :
    Star (ReplTyp p q) (.bnd T) (.bnd U) :=
  h.map Typ.bnd (fun h => .bnd h)

theorem Star.replAllDom {p q T U V} (h : Star (ReplTyp p q) T U) :
    Star (ReplTyp p q) (.all T V) (.all U V) :=
  h.map (fun T : Typ => Typ.all T V) (fun h => ReplTyp.allDom h)

theorem Star.replAllCod {p q T U V} (h : Star (ReplTyp p q) T U) :
    Star (ReplTyp p q) (.all V T) (.all V U) :=
  h.map (fun T : Typ => Typ.all V T) (fun h => ReplTyp.allCod h)

theorem Star.replTypLo {p q T U V A} (h : Star (ReplTyp p q) T U) :
    Star (ReplDec p q) (.typ A T V) (.typ A U V) :=
  h.map (fun T : Typ => Dec.typ A T V) (fun h => ReplDec.typLo h)

theorem Star.replTypHi {p q T U V A} (h : Star (ReplTyp p q) T U) :
    Star (ReplDec p q) (.typ A V T) (.typ A V U) :=
  h.map (fun T : Typ => Dec.typ A V T) (fun h => ReplDec.typHi h)

theorem Star.replTrm {p q T U a} (h : Star (ReplTyp p q) T U) :
    Star (ReplDec p q) (.trm a T) (.trm a U) :=
  h.map (fun T : Typ => Dec.trm a T) (fun h => ReplDec.trm h)

mutual
  theorem ReplTyp.insert {p q T U} (h : ReplTyp p q T U) (r : Path) :
      ∃ V, ReplTyp p r T V ∧ ReplTyp r q V U := by
    cases h with
    | rcd h =>
      obtain ⟨E, h₁, h₂⟩ := h.insert r
      exact ⟨.rcd E, .rcd h₁, .rcd h₂⟩
    | andLeft h =>
      obtain ⟨V, h₁, h₂⟩ := h.insert r
      exact ⟨.and V _, .andLeft h₁, .andLeft h₂⟩
    | andRight h =>
      obtain ⟨V, h₁, h₂⟩ := h.insert r
      exact ⟨.and _ V, .andRight h₁, .andRight h₂⟩
    | path => exact ⟨.path (r.selectFields _) _, .path, .path⟩
    | bnd h =>
      obtain ⟨V, h₁, h₂⟩ := h.insert r
      exact ⟨.bnd V, .bnd h₁, .bnd h₂⟩
    | allDom h =>
      obtain ⟨V, h₁, h₂⟩ := h.insert r
      exact ⟨.all V _, .allDom h₁, .allDom h₂⟩
    | allCod h =>
      obtain ⟨V, h₁, h₂⟩ := h.insert r
      exact ⟨.all _ V, .allCod h₁, .allCod h₂⟩
    | sngl => exact ⟨.sngl (r.selectFields _), .sngl, .sngl⟩

  theorem ReplDec.insert {p q D E} (h : ReplDec p q D E) (r : Path) :
      ∃ F, ReplDec p r D F ∧ ReplDec r q F E := by
    cases h with
    | typLo h =>
      obtain ⟨V, h₁, h₂⟩ := h.insert r
      exact ⟨.typ _ V _, .typLo h₁, .typLo h₂⟩
    | typHi h =>
      obtain ⟨V, h₁, h₂⟩ := h.insert r
      exact ⟨.typ _ _ V, .typHi h₁, .typHi h₂⟩
    | trm h =>
      obtain ⟨V, h₁, h₂⟩ := h.insert r
      exact ⟨.trm _ V, .trm h₁, .trm h₂⟩
end

theorem ReplTyp.sngl_prefixes {p q p' q'}
    (h : ReplTyp p q (.sngl p') (.sngl q')) :
    ∃ fields, p' = p.selectFields fields ∧ q' = q.selectFields fields := by
  cases h with
  | sngl => exact ⟨_, rfl, rfl⟩

theorem ReplTyp.path_prefixes {p q p' q' A}
    (h : ReplTyp p q (.path p' A) (.path q' A)) :
    ∃ fields, p' = p.selectFields fields ∧ q' = q.selectFields fields := by
  cases h with
  | path => exact ⟨_, rfl, rfl⟩

mutual
  theorem ReplTyp.subst {p q T U} (h : ReplTyp p q T U) (x : Var) (r : Path) :
      ReplTyp (p.subst x r) (q.subst x r) (T.subst x r) (U.subst x r) := by
    cases h with
    | rcd h => exact .rcd (h.subst x r)
    | andLeft h => exact .andLeft (h.subst x r)
    | andRight h => exact .andRight (h.subst x r)
    | path =>
      simp only [Typ.subst, Path.subst_selectFields]
      exact .path
    | bnd h => exact .bnd (h.subst x r)
    | allDom h => exact .allDom (h.subst x r)
    | allCod h => exact .allCod (h.subst x r)
    | sngl =>
      simp only [Typ.subst, Path.subst_selectFields]
      exact .sngl

  theorem ReplDec.subst {p q D E} (h : ReplDec p q D E) (x : Var) (r : Path) :
      ReplDec (p.subst x r) (q.subst x r) (D.subst x r) (E.subst x r) := by
    cases h with
    | typLo h => exact .typLo (h.subst x r)
    | typHi h => exact .typHi (h.subst x r)
    | trm h => exact .trm (h.subst x r)
end

end CDot
