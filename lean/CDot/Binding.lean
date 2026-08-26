import CDot.Definitions

/-!
# Binding infrastructure

Lean port of the environment-facing infrastructure in `cdot/Binding.v`.
-/

namespace CDot

section Syntax

variable [Signature]

/-! ## Substitution of a free variable by a path -/

def Var.subst (z : Var) (y : Var) (x : Var) : Var := if x = z then y else x

def Var.substPath (z : Var) (p : Path) (x : Var) : Path :=
  if x = z then p else .var x

def AVar.subst (z : Var) (p : Path) : AVar → Path
  | .bound i => .select (.bound i) []
  | .free x => Var.substPath z p x

def Path.subst : Path → Var → Path → Path
  | .select x fields, z, q => (x.subst z q).selectFields fields

mutual
  def Typ.subst (z : Var) (p : Path) : Typ → Typ
    | .top => .top
    | .bot => .bot
    | .rcd D => .rcd (D.subst z p)
    | .and T U => .and (T.subst z p) (U.subst z p)
    | .path q A => .path (q.subst z p) A
    | .bnd T => .bnd (T.subst z p)
    | .all T U => .all (T.subst z p) (U.subst z p)
    | .sngl q => .sngl (q.subst z p)

  def Dec.subst (z : Var) (p : Path) : Dec → Dec
    | .typ A T U => .typ A (T.subst z p) (U.subst z p)
    | .trm a T => .trm a (T.subst z p)
end

mutual
  def Trm.subst (z : Var) (p : Path) : Trm → Trm
    | .val v => .val (v.subst z p)
    | .path q => .path (q.subst z p)
    | .app q r => .app (q.subst z p) (r.subst z p)
    | .letE t u => .letE (t.subst z p) (u.subst z p)
    | .caseE q r A t u =>
        .caseE (q.subst z p) (r.subst z p) A (t.subst z p) (u.subst z p)

  def Val.subst (z : Var) (p : Path) : Val → Val
    | .new q A T ds => .new (q.subst z p) A (T.subst z p) (ds.subst z p)
    | .lambda T t => .lambda (T.subst z p) (t.subst z p)

  def Def.subst (z : Var) (p : Path) : Def → Def
    | .typ A T => .typ A (T.subst z p)
    | .trm a rhs => .trm a (rhs.subst z p)

  def Defs.subst (z : Var) (p : Path) : Defs → Defs
    | .nil => .nil
    | .cons ds d => .cons (ds.subst z p) (d.subst z p)

  def DefRhs.subst (z : Var) (p : Path) : DefRhs → DefRhs
    | .path q => .path (q.subst z p)
    | .val v => .val (v.subst z p)
end

def Ctx.subst (z : Var) (p : Path) (G : Ctx) : Ctx :=
  G.map fun binding => (binding.1, binding.2.subst z p)

end Syntax

def Env.get [DecidableEq Var] (x : Var) : Env α → Option α
  | [] => none
  | (y, a) :: G => if x = y then some a else Env.get x G

namespace Env.Binds

theorem empty_false {α : Type} {x : Var} {a : α}
    (h : Env.Binds x a (Env.empty : Env α)) : False := by
  cases h

theorem functional {α : Type} {x : Var} {a b : α} {G : Env α}
    (h₁ : Env.Binds x a G) (h₂ : Env.Binds x b G) : a = b := by
  induction h₁ generalizing b
  case here =>
    cases h₂ with
    | here => rfl
    | there hne _ => exact False.elim (hne rfl)
  case there hne _ ih =>
    cases h₂ with
    | here => exact False.elim (hne rfl)
    | there _ h₂ => exact ih h₂

theorem push_eq {α : Type} {x : Var} {a b : α} {G : Env α}
    (h : Env.Binds x a (Env.push G x b)) : a = b :=
  functional h .here

theorem push_ne {α : Type} {x y : Var} {a b : α} {G : Env α}
    (hne : x ≠ y) (h : Env.Binds x a G) :
    Env.Binds x a (Env.push G y b) := .there hne h

theorem push_ne_inv {α : Type} {x y : Var} {a b : α} {G : Env α}
    (hne : x ≠ y) (h : Env.Binds x a (Env.push G y b)) :
    Env.Binds x a G := by
  cases h with
  | here => exact False.elim (hne rfl)
  | there _ h => exact h

theorem get_eq_some {α : Type} {x : Var} {a : α} {G : Env α}
    (h : Env.Binds x a G) : Env.get x G = some a := by
  induction h
  case here => simp [Env.get]
  case there hne _ ih => simp [Env.get, hne, ih]

theorem mem_dom {α : Type} {x : Var} {a : α} {G : Env α}
    (h : Env.Binds x a G) : x ∈ G.dom := by
  induction h with
  | here => simp [Env.dom]
  | there hne h ih => simp only [Env.dom, List.map_cons, List.mem_toFinset,
      List.mem_cons]; exact Or.inr (by simpa only [Env.dom, List.mem_toFinset] using ih)

theorem ne_of_fresh {α : Type} {x y : Var} {a : α} {G : Env α}
    (h : Env.Binds y a G) (hf : Env.Fresh x G) : y ≠ x := by
  intro heq
  subst x
  exact hf h.mem_dom

end Env.Binds

variable [Signature]

/-! ## Path selection and opening -/

@[simp] theorem Path.selectFields_openRecPath
    (n : Nat) (q p : Path) (fields : Fields) :
    (p.openRecPath n q).selectFields fields =
      (p.selectFields fields).openRecPath n q := by
  cases p with
  | select x suffix =>
    cases x with
    | bound i =>
      cases q with
      | select y suffix' =>
        simp only [Path.openRecPath, Path.selectFields]
        split
        · simp only [List.append_assoc]
        · rfl
    | free x => rfl

theorem Path.last_field {p : Path} {a : Signature.TrmLabel}
    {x : AVar} {fields : Fields}
    (h : p.selectField a = .select x fields) :
    ∃ rest, fields = a :: rest := by
  cases p with
  | select y rest =>
    simp only [Path.selectField] at h
    cases h
    exact ⟨rest, rfl⟩

def Path.Named : Path → Prop
  | .select x _ => ∃ y, x = .free y

theorem Path.openRecPath_eq_of_named {p : Path} (h : p.Named)
    (q : Path) (n : Nat) : p.openRecPath n q = p := by
  cases p with
  | select x fields =>
    simp only [Path.Named] at h
    obtain ⟨y, rfl⟩ := h
    rfl

theorem Path.Named.selectFields {p : Path} (h : p.Named) (fields : Fields) :
    (p.selectFields fields).Named := by
  cases p with
  | select x suffix =>
    simp only [Path.Named] at h ⊢
    exact h

theorem Path.Named.of_selectField {p : Path} {a : Signature.TrmLabel}
    (h : (p.selectField a).Named) : p.Named := by
  cases p with
  | select x fields =>
      simpa only [Path.selectField, Path.Named] using h

@[simp] theorem Path.openRec_eq_openRecPath_var
    (x : Var) (p : Path) (n : Nat) :
    p.openRec n x = p.openRecPath n (.var x) := by
  cases p with
  | select a fields =>
    cases a with
    | bound i =>
      simp only [Path.openRec, AVar.openRec, Path.openRecPath, Path.var]
      split
      · simp only [List.append_nil]
      · rfl
    | free y => rfl

mutual
  @[simp] theorem Typ.openRec_eq_openRecPath_var
      (x : Var) (T : Typ) (n : Nat) :
      T.openRec n x = T.openRecPath n (.var x) := by
    cases T with
    | top => rfl
    | bot => rfl
    | rcd D => simp only [Typ.openRec, Typ.openRecPath, Dec.openRec_eq_openRecPath_var]
    | and T U => simp only [Typ.openRec, Typ.openRecPath, Typ.openRec_eq_openRecPath_var]
    | path p A =>
      simp only [Typ.openRec, Typ.openRecPath, Path.openRec_eq_openRecPath_var]
    | bnd T => simp only [Typ.openRec, Typ.openRecPath, Typ.openRec_eq_openRecPath_var]
    | all T U => simp only [Typ.openRec, Typ.openRecPath, Typ.openRec_eq_openRecPath_var]
    | sngl p =>
      simp only [Typ.openRec, Typ.openRecPath, Path.openRec_eq_openRecPath_var]

  @[simp] theorem Dec.openRec_eq_openRecPath_var
      (x : Var) (D : Dec) (n : Nat) :
      D.openRec n x = D.openRecPath n (.var x) := by
    cases D with
    | typ A T U => simp only [Dec.openRec, Dec.openRecPath, Typ.openRec_eq_openRecPath_var]
    | trm a T => simp only [Dec.openRec, Dec.openRecPath, Typ.openRec_eq_openRecPath_var]
end

/-! ## Substitution of fresh variables -/

@[simp] theorem Path.subst_eq_self_of_not_mem
    {x : Var} {q p : Path} (h : x ∉ p.fv) : p.subst x q = p := by
  cases p with
  | select a fields =>
    cases a with
    | bound i => simp [Path.subst, AVar.subst, Path.selectFields]
    | free y =>
      simp only [Path.fv, AVar.fv, Finset.mem_singleton] at h
      have hne : y ≠ x := Ne.symm h
      simp [Path.subst, AVar.subst, Var.substPath, Path.selectFields, Path.var, hne]

mutual
  @[simp] theorem Typ.subst_eq_self_of_not_mem
      {x : Var} {q : Path} (T : Typ) (h : x ∉ T.fv) : T.subst x q = T := by
    cases T with
    | top => rfl
    | bot => rfl
    | rcd D =>
      simp only [Typ.fv] at h
      simp only [Typ.subst, Dec.subst_eq_self_of_not_mem D h]
    | and T U =>
      simp only [Typ.fv, Finset.mem_union, not_or] at h
      simp only [Typ.subst, Typ.subst_eq_self_of_not_mem T h.1,
        Typ.subst_eq_self_of_not_mem U h.2]
    | path p A =>
      simp only [Typ.fv] at h
      simp only [Typ.subst, Path.subst_eq_self_of_not_mem h]
    | bnd T =>
      simp only [Typ.fv] at h
      simp only [Typ.subst, Typ.subst_eq_self_of_not_mem T h]
    | all T U =>
      simp only [Typ.fv, Finset.mem_union, not_or] at h
      simp only [Typ.subst, Typ.subst_eq_self_of_not_mem T h.1,
        Typ.subst_eq_self_of_not_mem U h.2]
    | sngl p =>
      simp only [Typ.fv] at h
      simp only [Typ.subst, Path.subst_eq_self_of_not_mem h]

  @[simp] theorem Dec.subst_eq_self_of_not_mem
      {x : Var} {q : Path} (D : Dec) (h : x ∉ D.fv) : D.subst x q = D := by
    cases D with
    | typ A T U =>
      simp only [Dec.fv, Finset.mem_union, not_or] at h
      simp only [Dec.subst, Typ.subst_eq_self_of_not_mem T h.1,
        Typ.subst_eq_self_of_not_mem U h.2]
    | trm a T =>
      simp only [Dec.fv] at h
      simp only [Dec.subst, Typ.subst_eq_self_of_not_mem T h]
end

mutual
  @[simp] theorem Trm.subst_eq_self_of_not_mem
      {x : Var} {q : Path} (t : Trm) (h : x ∉ t.fv) : t.subst x q = t := by
    cases t with
    | val v =>
      simp only [Trm.fv] at h
      simp only [Trm.subst, Val.subst_eq_self_of_not_mem v h]
    | path p =>
      simp only [Trm.fv] at h
      simp only [Trm.subst, Path.subst_eq_self_of_not_mem h]
    | app p r =>
      simp only [Trm.fv, Finset.mem_union, not_or] at h
      simp only [Trm.subst, Path.subst_eq_self_of_not_mem h.1,
        Path.subst_eq_self_of_not_mem h.2]
    | letE t u =>
      simp only [Trm.fv, Finset.mem_union, not_or] at h
      simp only [Trm.subst, Trm.subst_eq_self_of_not_mem t h.1,
        Trm.subst_eq_self_of_not_mem u h.2]
    | caseE p r A t u =>
      simp only [Trm.fv, Finset.mem_union, not_or] at h
      simp only [Trm.subst, Path.subst_eq_self_of_not_mem h.1.1.1,
        Path.subst_eq_self_of_not_mem h.1.1.2,
        Trm.subst_eq_self_of_not_mem t h.1.2,
        Trm.subst_eq_self_of_not_mem u h.2]

  @[simp] theorem Val.subst_eq_self_of_not_mem
      {x : Var} {q : Path} (v : Val) (h : x ∉ v.fv) : v.subst x q = v := by
    cases v with
    | new p A T ds =>
      simp only [Val.fv, Finset.mem_union, not_or] at h
      simp only [Val.subst, Path.subst_eq_self_of_not_mem h.1.1,
        Typ.subst_eq_self_of_not_mem T h.1.2, Defs.subst_eq_self_of_not_mem ds h.2]
    | lambda T t =>
      simp only [Val.fv, Finset.mem_union, not_or] at h
      simp only [Val.subst, Typ.subst_eq_self_of_not_mem T h.1,
        Trm.subst_eq_self_of_not_mem t h.2]

  @[simp] theorem Def.subst_eq_self_of_not_mem
      {x : Var} {q : Path} (d : Def) (h : x ∉ d.fv) : d.subst x q = d := by
    cases d with
    | typ A T =>
      simp only [Def.fv] at h
      simp only [Def.subst, Typ.subst_eq_self_of_not_mem T h]
    | trm a rhs =>
      simp only [Def.fv] at h
      simp only [Def.subst, DefRhs.subst_eq_self_of_not_mem rhs h]

  @[simp] theorem Defs.subst_eq_self_of_not_mem
      {x : Var} {q : Path} (ds : Defs) (h : x ∉ ds.fv) : ds.subst x q = ds := by
    cases ds with
    | nil => rfl
    | cons ds d =>
      simp only [Defs.fv, Finset.mem_union, not_or] at h
      simp only [Defs.subst, Defs.subst_eq_self_of_not_mem ds h.1,
        Def.subst_eq_self_of_not_mem d h.2]

  @[simp] theorem DefRhs.subst_eq_self_of_not_mem
      {x : Var} {q : Path} (rhs : DefRhs) (h : x ∉ rhs.fv) : rhs.subst x q = rhs := by
    cases rhs with
    | path p =>
      simp only [DefRhs.fv] at h
      simp only [DefRhs.subst, Path.subst_eq_self_of_not_mem h]
    | val v =>
      simp only [DefRhs.fv] at h
      simp only [DefRhs.subst, Val.subst_eq_self_of_not_mem v h]
end

mutual
  @[simp] theorem Trm.openRec_eq_openRecPath_var
      (x : Var) (t : Trm) (n : Nat) :
      t.openRec n x = t.openRecPath n (.var x) := by
    cases t with
    | val v => simp only [Trm.openRec, Trm.openRecPath, Val.openRec_eq_openRecPath_var]
    | path p =>
      simp only [Trm.openRec, Trm.openRecPath, Path.openRec_eq_openRecPath_var]
    | app p q =>
      simp only [Trm.openRec, Trm.openRecPath, Path.openRec_eq_openRecPath_var]
    | letE t u => simp only [Trm.openRec, Trm.openRecPath, Trm.openRec_eq_openRecPath_var]
    | caseE p q A t u =>
      simp only [Trm.openRec, Trm.openRecPath, Path.openRec_eq_openRecPath_var,
        Trm.openRec_eq_openRecPath_var]

  @[simp] theorem Val.openRec_eq_openRecPath_var
      (x : Var) (v : Val) (n : Nat) :
      v.openRec n x = v.openRecPath n (.var x) := by
    cases v with
    | new p A T ds =>
      simp only [Val.openRec, Val.openRecPath, Path.openRec_eq_openRecPath_var,
        Typ.openRec_eq_openRecPath_var, Defs.openRec_eq_openRecPath_var]
    | lambda T t =>
      simp only [Val.openRec, Val.openRecPath, Typ.openRec_eq_openRecPath_var,
        Trm.openRec_eq_openRecPath_var]

  @[simp] theorem Def.openRec_eq_openRecPath_var
      (x : Var) (d : Def) (n : Nat) :
      d.openRec n x = d.openRecPath n (.var x) := by
    cases d with
    | typ A T => simp only [Def.openRec, Def.openRecPath, Typ.openRec_eq_openRecPath_var]
    | trm a rhs =>
      simp only [Def.openRec, Def.openRecPath, DefRhs.openRec_eq_openRecPath_var]

  @[simp] theorem Defs.openRec_eq_openRecPath_var
      (x : Var) (ds : Defs) (n : Nat) :
      ds.openRec n x = ds.openRecPath n (.var x) := by
    cases ds with
    | nil => rfl
    | cons ds d =>
      simp only [Defs.openRec, Defs.openRecPath, Defs.openRec_eq_openRecPath_var,
        Def.openRec_eq_openRecPath_var]

  @[simp] theorem DefRhs.openRec_eq_openRecPath_var
      (x : Var) (rhs : DefRhs) (n : Nat) :
      rhs.openRec n x = rhs.openRecPath n (.var x) := by
    cases rhs with
    | path p =>
      simp only [DefRhs.openRec, DefRhs.openRecPath, Path.openRec_eq_openRecPath_var]
    | val v =>
      simp only [DefRhs.openRec, DefRhs.openRecPath, Val.openRec_eq_openRecPath_var]
end

/-! ## Substitution commutes with opening by a variable -/

theorem Path.subst_openRec (p : Path) (n : Nat) (x : Var)
    (q : Path) (z : Var) (hp : p.Named) :
    (q.openRec n z).subst x p =
      (q.subst x p).openRecPath n (Var.substPath x p z) := by
  cases p with
  | select pa pfields =>
    simp only [Path.Named] at hp
    obtain ⟨y, rfl⟩ := hp
    cases q with
    | select qa qfields =>
      cases qa with
      | bound i =>
        by_cases hni : n = i
        · by_cases hzx : z = x
          · simp [Path.openRec, AVar.openRec, Path.subst, AVar.subst,
              Path.selectFields, Path.openRecPath, Var.substPath,
              hni, hzx]
          · simp [Path.openRec, AVar.openRec, Path.subst, AVar.subst,
              Path.selectFields, Path.openRecPath, Var.substPath, Path.var,
              hni, hzx]
        · simp [Path.openRec, AVar.openRec, Path.subst, AVar.subst,
            Path.selectFields, Path.openRecPath, Var.substPath, Path.var, hni]
      | free w =>
        simp only [Path.openRec, AVar.openRec, Path.subst, AVar.subst,
          Path.selectFields, Path.openRecPath, Var.substPath, Path.var]
        split <;> split <;> simp_all [List.append_assoc]

mutual
  theorem Typ.subst_openRec (p : Path) (hp : p.Named) (x z : Var)
      (T : Typ) (n : Nat) :
      (T.openRec n z).subst x p =
        (T.subst x p).openRecPath n (Var.substPath x p z) := by
    cases T with
    | top => rfl
    | bot => rfl
    | rcd D =>
      simp only [Typ.openRec, Typ.subst, Typ.openRecPath,
        Dec.subst_openRec p hp x z D n]
    | and T U =>
      simp only [Typ.openRec, Typ.subst, Typ.openRecPath,
        Typ.subst_openRec p hp x z T n, Typ.subst_openRec p hp x z U n]
    | path q A =>
      simp only [Typ.openRec, Typ.subst, Typ.openRecPath, Path.subst_openRec p n x q z hp]
    | bnd T =>
      simp only [Typ.openRec, Typ.subst, Typ.openRecPath,
        Typ.subst_openRec p hp x z T (n + 1)]
    | all T U =>
      simp only [Typ.openRec, Typ.subst, Typ.openRecPath,
        Typ.subst_openRec p hp x z T n, Typ.subst_openRec p hp x z U (n + 1)]
    | sngl q =>
      simp only [Typ.openRec, Typ.subst, Typ.openRecPath, Path.subst_openRec p n x q z hp]

  theorem Dec.subst_openRec (p : Path) (hp : p.Named) (x z : Var)
      (D : Dec) (n : Nat) :
      (D.openRec n z).subst x p =
        (D.subst x p).openRecPath n (Var.substPath x p z) := by
    cases D with
    | typ A T U =>
      simp only [Dec.openRec, Dec.subst, Dec.openRecPath,
        Typ.subst_openRec p hp x z T n, Typ.subst_openRec p hp x z U n]
    | trm a T =>
      simp only [Dec.openRec, Dec.subst, Dec.openRecPath,
        Typ.subst_openRec p hp x z T n]
end

mutual
  theorem Trm.subst_openRec (p : Path) (hp : p.Named) (x z : Var)
      (t : Trm) (n : Nat) :
      (t.openRec n z).subst x p =
        (t.subst x p).openRecPath n (Var.substPath x p z) := by
    cases t with
    | val v =>
      simp only [Trm.openRec, Trm.subst, Trm.openRecPath,
        Val.subst_openRec p hp x z v n]
    | path q =>
      simp only [Trm.openRec, Trm.subst, Trm.openRecPath, Path.subst_openRec p n x q z hp]
    | app q r =>
      simp only [Trm.openRec, Trm.subst, Trm.openRecPath,
        Path.subst_openRec p n x q z hp, Path.subst_openRec p n x r z hp]
    | letE t u =>
      simp only [Trm.openRec, Trm.subst, Trm.openRecPath,
        Trm.subst_openRec p hp x z t n, Trm.subst_openRec p hp x z u (n + 1)]
    | caseE q r A t u =>
      simp only [Trm.openRec, Trm.subst, Trm.openRecPath,
        Path.subst_openRec p n x q z hp, Path.subst_openRec p n x r z hp,
        Trm.subst_openRec p hp x z t (n + 1), Trm.subst_openRec p hp x z u n]

  theorem Val.subst_openRec (p : Path) (hp : p.Named) (x z : Var)
      (v : Val) (n : Nat) :
      (v.openRec n z).subst x p =
        (v.subst x p).openRecPath n (Var.substPath x p z) := by
    cases v with
    | new q A T ds =>
      simp only [Val.openRec, Val.subst, Val.openRecPath,
        Path.subst_openRec p (n + 1) x q z hp,
        Typ.subst_openRec p hp x z T (n + 1),
        Defs.subst_openRec p hp x z ds (n + 1)]
    | lambda T t =>
      simp only [Val.openRec, Val.subst, Val.openRecPath,
        Typ.subst_openRec p hp x z T n, Trm.subst_openRec p hp x z t (n + 1)]

  theorem Def.subst_openRec (p : Path) (hp : p.Named) (x z : Var)
      (d : Def) (n : Nat) :
      (d.openRec n z).subst x p =
        (d.subst x p).openRecPath n (Var.substPath x p z) := by
    cases d with
    | typ A T =>
      simp only [Def.openRec, Def.subst, Def.openRecPath,
        Typ.subst_openRec p hp x z T n]
    | trm a rhs =>
      simp only [Def.openRec, Def.subst, Def.openRecPath,
        DefRhs.subst_openRec p hp x z rhs n]

  theorem Defs.subst_openRec (p : Path) (hp : p.Named) (x z : Var)
      (ds : Defs) (n : Nat) :
      (ds.openRec n z).subst x p =
        (ds.subst x p).openRecPath n (Var.substPath x p z) := by
    cases ds with
    | nil => rfl
    | cons ds d =>
      simp only [Defs.openRec, Defs.subst, Defs.openRecPath,
        Defs.subst_openRec p hp x z ds n, Def.subst_openRec p hp x z d n]

  theorem DefRhs.subst_openRec (p : Path) (hp : p.Named) (x z : Var)
      (rhs : DefRhs) (n : Nat) :
      (rhs.openRec n z).subst x p =
        (rhs.subst x p).openRecPath n (Var.substPath x p z) := by
    cases rhs with
    | path q =>
      simp only [DefRhs.openRec, DefRhs.subst, DefRhs.openRecPath,
        Path.subst_openRec p n x q z hp]
    | val v =>
      simp only [DefRhs.openRec, DefRhs.subst, DefRhs.openRecPath,
        Val.subst_openRec p hp x z v n]
end

/-! ## Substitution commutes with opening by a path -/

theorem Path.subst_openRecPath (p : Path) (n : Nat) (x : Var) (q r : Path)
    (hq : q.Named) :
    (p.openRecPath n r).subst x q =
      (p.subst x q).openRecPath n (r.subst x q) := by
  cases q with
  | select qa qfields =>
    simp only [Path.Named] at hq
    obtain ⟨y, rfl⟩ := hq
    cases p with
    | select pa pfields =>
      cases r with
      | select ra rfields =>
        cases pa with
        | bound i =>
          by_cases hni : n = i
          · simp [Path.openRecPath, Path.subst, AVar.subst, Path.selectFields,
              Var.substPath, Path.var, hni, List.append_assoc]
          · simp [Path.openRecPath, Path.subst, AVar.subst, Path.selectFields,
              Var.substPath, Path.var, hni]
        | free z =>
          have hnamed :
              ((Path.select (.free z) pfields).subst x
                (Path.select (.free y) qfields)).Named := by
            by_cases hzx : z = x
            · subst z
              simp [Path.subst, AVar.subst, Var.substPath, Path.selectFields,
                Path.Named]
            · simp [Path.subst, AVar.subst, Var.substPath, Path.selectFields,
                Path.var, Path.Named, hzx]
          rw [Path.openRecPath_eq_of_named hnamed]
          rfl

mutual
  theorem Typ.subst_openRecPath (q : Path) (hq : q.Named) (x : Var)
      (r : Path) (T : Typ) (n : Nat) :
      (T.openRecPath n r).subst x q =
        (T.subst x q).openRecPath n (r.subst x q) := by
    cases T with
    | top => rfl
    | bot => rfl
    | rcd D =>
      simp only [Typ.openRecPath, Typ.subst, Dec.subst_openRecPath q hq x r D n]
    | and T U =>
      simp only [Typ.openRecPath, Typ.subst, Typ.subst_openRecPath q hq x r T n,
        Typ.subst_openRecPath q hq x r U n]
    | path p A =>
      simp only [Typ.openRecPath, Typ.subst, Path.subst_openRecPath p n x q r hq]
    | bnd T =>
      simp only [Typ.openRecPath, Typ.subst,
        Typ.subst_openRecPath q hq x r T (n + 1)]
    | all T U =>
      simp only [Typ.openRecPath, Typ.subst, Typ.subst_openRecPath q hq x r T n,
        Typ.subst_openRecPath q hq x r U (n + 1)]
    | sngl p =>
      simp only [Typ.openRecPath, Typ.subst, Path.subst_openRecPath p n x q r hq]

  theorem Dec.subst_openRecPath (q : Path) (hq : q.Named) (x : Var)
      (r : Path) (D : Dec) (n : Nat) :
      (D.openRecPath n r).subst x q =
        (D.subst x q).openRecPath n (r.subst x q) := by
    cases D with
    | typ A T U =>
      simp only [Dec.openRecPath, Dec.subst, Typ.subst_openRecPath q hq x r T n,
        Typ.subst_openRecPath q hq x r U n]
    | trm a T =>
      simp only [Dec.openRecPath, Dec.subst, Typ.subst_openRecPath q hq x r T n]
end

mutual
  theorem Trm.subst_openRecPath (q : Path) (hq : q.Named) (x : Var)
      (r : Path) (t : Trm) (n : Nat) :
      (t.openRecPath n r).subst x q =
        (t.subst x q).openRecPath n (r.subst x q) := by
    cases t with
    | val v =>
      simp only [Trm.openRecPath, Trm.subst, Val.subst_openRecPath q hq x r v n]
    | path p =>
      simp only [Trm.openRecPath, Trm.subst, Path.subst_openRecPath p n x q r hq]
    | app p s =>
      simp only [Trm.openRecPath, Trm.subst, Path.subst_openRecPath p n x q r hq,
        Path.subst_openRecPath s n x q r hq]
    | letE t u =>
      simp only [Trm.openRecPath, Trm.subst, Trm.subst_openRecPath q hq x r t n,
        Trm.subst_openRecPath q hq x r u (n + 1)]
    | caseE p s A t u =>
      simp only [Trm.openRecPath, Trm.subst, Path.subst_openRecPath p n x q r hq,
        Path.subst_openRecPath s n x q r hq,
        Trm.subst_openRecPath q hq x r t (n + 1),
        Trm.subst_openRecPath q hq x r u n]

  theorem Val.subst_openRecPath (q : Path) (hq : q.Named) (x : Var)
      (r : Path) (v : Val) (n : Nat) :
      (v.openRecPath n r).subst x q =
        (v.subst x q).openRecPath n (r.subst x q) := by
    cases v with
    | new p A T ds =>
      simp only [Val.openRecPath, Val.subst,
        Path.subst_openRecPath p (n + 1) x q r hq,
        Typ.subst_openRecPath q hq x r T (n + 1),
        Defs.subst_openRecPath q hq x r ds (n + 1)]
    | lambda T t =>
      simp only [Val.openRecPath, Val.subst, Typ.subst_openRecPath q hq x r T n,
        Trm.subst_openRecPath q hq x r t (n + 1)]

  theorem Def.subst_openRecPath (q : Path) (hq : q.Named) (x : Var)
      (r : Path) (d : Def) (n : Nat) :
      (d.openRecPath n r).subst x q =
        (d.subst x q).openRecPath n (r.subst x q) := by
    cases d with
    | typ A T =>
      simp only [Def.openRecPath, Def.subst, Typ.subst_openRecPath q hq x r T n]
    | trm a rhs =>
      simp only [Def.openRecPath, Def.subst, DefRhs.subst_openRecPath q hq x r rhs n]

  theorem Defs.subst_openRecPath (q : Path) (hq : q.Named) (x : Var)
      (r : Path) (ds : Defs) (n : Nat) :
      (ds.openRecPath n r).subst x q =
        (ds.subst x q).openRecPath n (r.subst x q) := by
    cases ds with
    | nil => rfl
    | cons ds d =>
      simp only [Defs.openRecPath, Defs.subst, Defs.subst_openRecPath q hq x r ds n,
        Def.subst_openRecPath q hq x r d n]

  theorem DefRhs.subst_openRecPath (q : Path) (hq : q.Named) (x : Var)
      (r : Path) (rhs : DefRhs) (n : Nat) :
      (rhs.openRecPath n r).subst x q =
        (rhs.subst x q).openRecPath n (r.subst x q) := by
    cases rhs with
    | path p =>
      simp only [DefRhs.openRecPath, DefRhs.subst, Path.subst_openRecPath p n x q r hq]
    | val v =>
      simp only [DefRhs.openRecPath, DefRhs.subst, Val.subst_openRecPath q hq x r v n]
end

theorem Typ.openPath_eq_subst_open_of_fresh
    {x : Var} {p : Path} (T : Typ) (hx : x ∉ T.fv) (hp : p.Named) :
    T.openPath p = (T.open x).subst x p := by
  change T.openRecPath 0 p = (T.openRec 0 x).subst x p
  rw [Typ.subst_openRec p hp x x T 0]
  rw [Typ.subst_eq_self_of_not_mem T hx]
  simp [Var.substPath]

theorem Trm.openPath_eq_subst_open_of_fresh
    {x : Var} {p : Path} (t : Trm) (hx : x ∉ t.fv) (hp : p.Named) :
    t.openPath p = (t.open x).subst x p := by
  change t.openRecPath 0 p = (t.openRec 0 x).subst x p
  rw [Trm.subst_openRec p hp x x t 0]
  rw [Trm.subst_eq_self_of_not_mem t hx]
  simp [Var.substPath]

theorem Defs.openPath_eq_subst_open_of_fresh
    {x : Var} {p : Path} (ds : Defs) (hx : x ∉ ds.fv) (hp : p.Named) :
    ds.openPath p = (ds.open x).subst x p := by
  change ds.openRecPath 0 p = (ds.openRec 0 x).subst x p
  rw [Defs.subst_openRec p hp x x ds 0]
  rw [Defs.subst_eq_self_of_not_mem ds hx]
  simp [Var.substPath]

theorem Defs.has_injective {ds : Defs} {d₁ d₂ : Def}
    (h₁ : ds.Has d₁) (h₂ : ds.Has d₂) (labels : d₁.label = d₂.label) :
    d₁ = d₂ := by
  unfold Defs.Has at h₁ h₂
  rw [labels] at h₁
  rw [h₂] at h₁
  exact Option.some.inj h₁.symm

@[simp] theorem Def.label_subst (d : Def) (x : Var) (q : Path) :
    (d.subst x q).label = d.label := by
  cases d <;> rfl

theorem Defs.hasnt_subst {ds : Defs} {l : Label} {x : Var} {q : Path}
    (h : ds.Hasnt l) : (ds.subst x q).Hasnt l := by
  cases ds with
  | nil => exact h
  | cons ds d =>
    simp only [Defs.Hasnt, Defs.get, Defs.subst, Def.label_subst] at h ⊢
    by_cases heq : d.label = l
    · simp [heq] at h
    · simp only [heq, ↓reduceIte] at h ⊢
      exact Defs.hasnt_subst h

theorem Defs.hasnt_subst_label {ds : Defs} {d : Def} {x : Var} {q : Path}
    (h : ds.Hasnt d.label) :
    (ds.subst x q).Hasnt (d.subst x q).label := by
  rw [Def.label_subst]
  exact Defs.hasnt_subst h

theorem Defs.Has.label_ne_of_hasnt {ds : Defs} {d₁ d₂ : Def}
    (hhas : ds.Has d₁) (hno : ds.Hasnt d₂.label) : d₁.label ≠ d₂.label := by
  intro heq
  unfold Defs.Has at hhas
  unfold Defs.Hasnt at hno
  rw [heq, hno] at hhas
  contradiction

theorem TypedDefs.recordHas {x : Var} {fields : Fields} {G : Ctx}
    {ds : Defs} {T : Typ} {D : Dec}
    (hdefs : TypedDefs x fields G ds T) (hhas : RecordHas T D) :
    ∃ d, ds.Has d ∧ TypedDef x fields G d D := by
  cases hdefs with
  | one hdef =>
    cases hhas with
    | one => exact ⟨_, by simp [Defs.Has, Defs.get], hdef⟩
  | cons hrest hdef hno =>
    cases hhas with
    | andLeft hhas =>
      obtain ⟨d', hd', htyped⟩ :=
        TypedDefs.recordHas (x := x) (fields := fields) hrest hhas
      have hne : d'.label ≠ _ := hd'.label_ne_of_hasnt hno
      refine ⟨d', ?_, htyped⟩
      unfold Defs.Has at hd' ⊢
      simp only [Defs.get]
      rw [if_neg (Ne.symm hne)]
      exact hd'
    | andRight hhas =>
      cases hhas with
      | one => exact ⟨_, by simp [Defs.Has, Defs.get], hdef⟩
termination_by sizeOf ds
decreasing_by
  simp_all
  omega

@[simp] theorem Path.selectFields_nil (p : Path) : p.selectFields [] = p := by
  cases p
  rfl

@[simp] theorem Path.selectFields_selectField
    (p : Path) (a : Signature.TrmLabel) (fields : Fields) :
    (p.selectField a).selectFields fields =
      p.selectFields (fields ++ [a]) := by
  cases p
  simp only [Path.selectField, Path.selectFields, List.append_assoc,
    List.singleton_append]

@[simp] theorem Path.selectFields_append (p : Path) (xs ys : Fields) :
    (p.selectFields xs).selectFields ys = p.selectFields (ys ++ xs) := by
  cases p
  simp only [Path.selectFields, List.append_assoc]

@[simp] theorem Path.subst_selectFields
    (p : Path) (fields : Fields) (x : Var) (r : Path) :
    (p.selectFields fields).subst x r = (p.subst x r).selectFields fields := by
  cases p with
  | select a suffix =>
    simp only [Path.selectFields, Path.subst, List.append_assoc]

theorem Path.selectFields_right_injective (p : Path) {xs ys : Fields}
    (h : p.selectFields xs = p.selectFields ys) : xs = ys := by
  cases p with
  | select x fields =>
    simp only [Path.selectFields] at h
    injection h with _ hfields
    exact List.append_cancel_right hfields

omit [Signature] in
theorem List.append_comparable_of_append_eq
    {α : Type} {m n x y : List α} (h : m ++ x = n ++ y) :
    ∃ rest, x = rest ++ y ∨ y = rest ++ x := by
  induction m generalizing n x y with
  | nil =>
    exact ⟨n, Or.inl h⟩
  | cons a m ih =>
    cases n with
    | nil => exact ⟨a :: m, Or.inr h.symm⟩
    | cons b n =>
      simp only [List.cons_append, List.cons.injEq] at h
      exact ih h.2

theorem Path.selectFields_comparable {p q : Path} {xs ys : Fields}
    (h : p.selectFields xs = q.selectFields ys) :
    ∃ rest, p = q.selectFields rest ∨ q = p.selectFields rest := by
  cases p with
  | select px pfields =>
    cases q with
    | select qx qfields =>
      simp only [Path.selectFields] at h
      injection h with havar hfields
      obtain ⟨rest, hleft | hright⟩ :=
        List.append_comparable_of_append_eq hfields
      · exact ⟨rest, Or.inl (by simp only [Path.selectFields, havar, hleft])⟩
      · exact ⟨rest, Or.inr (by simp only [Path.selectFields, havar, hright])⟩

end CDot
