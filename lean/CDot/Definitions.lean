import Mathlib.Data.Finset.Basic

/-!
# cDOT abstract syntax and type system

Lean port of `cdot/Definitions.v`.
-/

namespace CDot

/-- The two disjoint classes of cDOT member labels. -/
class Signature where
  TypLabel : Type
  TrmLabel : Type
  typLabelDecidableEq : DecidableEq TypLabel
  trmLabelDecidableEq : DecidableEq TrmLabel

@[reducible] instance Signature.instDecidableEqTypLabel [s : Signature] :
    DecidableEq s.TypLabel := s.typLabelDecidableEq

@[reducible] instance Signature.instDecidableEqTrmLabel [s : Signature] :
    DecidableEq s.TrmLabel := s.trmLabelDecidableEq

abbrev Var := Nat
abbrev Vars := Finset Var

/-- Locally nameless variables: bound variables use de Bruijn indices. -/
inductive AVar where
  | bound : Nat → AVar
  | free : Var → AVar
  deriving DecidableEq

variable [Signature]

inductive Label where
  | typ : Signature.TypLabel → Label
  | trm : Signature.TrmLabel → Label
  deriving DecidableEq

abbrev Fields := List Signature.TrmLabel

inductive Path where
  | select : AVar → Fields → Path
  deriving DecidableEq

mutual
  inductive Typ where
    | top : Typ
    | bot : Typ
    | rcd : Dec → Typ
    | and : Typ → Typ → Typ
    | path : Path → Signature.TypLabel → Typ
    | bnd : Typ → Typ
    | all : Typ → Typ → Typ
    | sngl : Path → Typ
    deriving DecidableEq

  inductive Dec where
    | typ : Signature.TypLabel → Typ → Typ → Dec
    | trm : Signature.TrmLabel → Typ → Dec
    deriving DecidableEq
end

mutual
  inductive Trm where
    | val : Val → Trm
    | app : Path → Path → Trm
    | letE : Trm → Trm → Trm
    | path : Path → Trm
    | caseE : Path → Path → Signature.TypLabel → Trm → Trm → Trm
    deriving DecidableEq

  inductive Val where
    | new : Path → Signature.TypLabel → Typ → Defs → Val
    | lambda : Typ → Trm → Val
    deriving DecidableEq

  inductive Def where
    | typ : Signature.TypLabel → Typ → Def
    | trm : Signature.TrmLabel → DefRhs → Def
    deriving DecidableEq

  inductive Defs where
    | nil : Defs
    | cons : Defs → Def → Defs
    deriving DecidableEq

  inductive DefRhs where
    | path : Path → DefRhs
    | val : Val → DefRhs
    deriving DecidableEq
end

/-! ## Paths, labels, and definition lookup -/

def Path.var (x : Var) : Path := .select (.free x) []

def Trm.var (x : Var) : Trm := .path (.var x)

def Path.selectField (p : Path) (a : Signature.TrmLabel) : Path :=
  match p with
  | .select x fields => .select x (a :: fields)

def Path.selectFields (p : Path) (fields : Fields) : Path :=
  match p with
  | .select x fields' => .select x (fields ++ fields')

def Def.label : Def → Label
  | .typ A _ => .typ A
  | .trm a _ => .trm a

def Dec.label : Dec → Label
  | .typ A _ _ => .typ A
  | .trm a _ => .trm a

def Defs.get (l : Label) : Defs → Option Def
  | .nil => none
  | .cons ds d => if d.label = l then some d else ds.get l

def Defs.Has (ds : Defs) (d : Def) : Prop := ds.get d.label = some d

def Defs.Hasnt (ds : Defs) (l : Label) : Prop := ds.get l = none

/-! ## Opening with a free variable -/

def AVar.openRec (k : Nat) (u : Var) : AVar → AVar
  | .bound i => if k = i then .free u else .bound i
  | .free x => .free x

def Path.openRec (k : Nat) (u : Var) : Path → Path
  | .select x fields => .select (x.openRec k u) fields

mutual
  def Typ.openRec (k : Nat) (u : Var) : Typ → Typ
    | .top => .top
    | .bot => .bot
    | .rcd D => .rcd (D.openRec k u)
    | .and T U => .and (T.openRec k u) (U.openRec k u)
    | .path p A => .path (p.openRec k u) A
    | .bnd T => .bnd (T.openRec (k + 1) u)
    | .all T U => .all (T.openRec k u) (U.openRec (k + 1) u)
    | .sngl p => .sngl (p.openRec k u)

  def Dec.openRec (k : Nat) (u : Var) : Dec → Dec
    | .typ A T U => .typ A (T.openRec k u) (U.openRec k u)
    | .trm a T => .trm a (T.openRec k u)
end

mutual
  def Trm.openRec (k : Nat) (u : Var) : Trm → Trm
    | .val v => .val (v.openRec k u)
    | .path p => .path (p.openRec k u)
    | .app p q => .app (p.openRec k u) (q.openRec k u)
    | .letE t₁ t₂ => .letE (t₁.openRec k u) (t₂.openRec (k + 1) u)
    | .caseE p q A t₁ t₂ =>
        .caseE (p.openRec k u) (q.openRec k u) A
          (t₁.openRec (k + 1) u) (t₂.openRec k u)

  def Val.openRec (k : Nat) (u : Var) : Val → Val
    | .new p A T ds =>
        .new (p.openRec (k + 1) u) A (T.openRec (k + 1) u)
          (ds.openRec (k + 1) u)
    | .lambda T t => .lambda (T.openRec k u) (t.openRec (k + 1) u)

  def Def.openRec (k : Nat) (u : Var) : Def → Def
    | .typ A T => .typ A (T.openRec k u)
    | .trm a rhs => .trm a (rhs.openRec k u)

  def Defs.openRec (k : Nat) (u : Var) : Defs → Defs
    | .nil => .nil
    | .cons ds d => .cons (ds.openRec k u) (d.openRec k u)

  def DefRhs.openRec (k : Nat) (u : Var) : DefRhs → DefRhs
    | .path p => .path (p.openRec k u)
    | .val v => .val (v.openRec k u)
end

abbrev AVar.open (u : Var) (a : AVar) := a.openRec 0 u
abbrev Path.open (u : Var) (p : Path) := p.openRec 0 u
abbrev Typ.open (u : Var) (T : Typ) := T.openRec 0 u
abbrev Dec.open (u : Var) (D : Dec) := D.openRec 0 u
abbrev Trm.open (u : Var) (t : Trm) := t.openRec 0 u
abbrev Val.open (u : Var) (v : Val) := v.openRec 0 u
abbrev Def.open (u : Var) (d : Def) := d.openRec 0 u
abbrev Defs.open (u : Var) (ds : Defs) := ds.openRec 0 u
abbrev DefRhs.open (u : Var) (rhs : DefRhs) := rhs.openRec 0 u

/-! ## Opening with a path -/

def AVar.openRecPath (k : Nat) (u : Path) : AVar → Path
  | .bound i => if k = i then u else .select (.bound i) []
  | .free x => .var x

def Path.openRecPath : Path → Nat → Path → Path
  | p@(.select x fields), k, u =>
      match x, u with
      | .bound i, .select y suffix =>
          if k = i then .select y (fields ++ suffix) else p
      | .free _, _ => p

mutual
  def Typ.openRecPath (k : Nat) (u : Path) : Typ → Typ
    | .top => .top
    | .bot => .bot
    | .rcd D => .rcd (D.openRecPath k u)
    | .and T U => .and (T.openRecPath k u) (U.openRecPath k u)
    | .path p A => .path (p.openRecPath k u) A
    | .bnd T => .bnd (T.openRecPath (k + 1) u)
    | .all T U => .all (T.openRecPath k u) (U.openRecPath (k + 1) u)
    | .sngl p => .sngl (p.openRecPath k u)

  def Dec.openRecPath (k : Nat) (u : Path) : Dec → Dec
    | .typ A T U => .typ A (T.openRecPath k u) (U.openRecPath k u)
    | .trm a T => .trm a (T.openRecPath k u)
end

mutual
  def Trm.openRecPath (k : Nat) (u : Path) : Trm → Trm
    | .val v => .val (v.openRecPath k u)
    | .path p => .path (p.openRecPath k u)
    | .app p q => .app (p.openRecPath k u) (q.openRecPath k u)
    | .letE t₁ t₂ => .letE (t₁.openRecPath k u) (t₂.openRecPath (k + 1) u)
    | .caseE p q A t₁ t₂ =>
        .caseE (p.openRecPath k u) (q.openRecPath k u) A
          (t₁.openRecPath (k + 1) u) (t₂.openRecPath k u)

  def Val.openRecPath (k : Nat) (u : Path) : Val → Val
    | .new p A T ds =>
        .new (p.openRecPath (k + 1) u) A (T.openRecPath (k + 1) u)
          (ds.openRecPath (k + 1) u)
    | .lambda T t => .lambda (T.openRecPath k u) (t.openRecPath (k + 1) u)

  def Def.openRecPath (k : Nat) (u : Path) : Def → Def
    | .typ A T => .typ A (T.openRecPath k u)
    | .trm a rhs => .trm a (rhs.openRecPath k u)

  def Defs.openRecPath (k : Nat) (u : Path) : Defs → Defs
    | .nil => .nil
    | .cons ds d => .cons (ds.openRecPath k u) (d.openRecPath k u)

  def DefRhs.openRecPath (k : Nat) (u : Path) : DefRhs → DefRhs
    | .path p => .path (p.openRecPath k u)
    | .val v => .val (v.openRecPath k u)
end

abbrev AVar.openPath (u : Path) (a : AVar) := a.openRecPath 0 u
abbrev Path.openPath (p : Path) (u : Path) := p.openRecPath 0 u
abbrev Typ.openPath (u : Path) (T : Typ) := T.openRecPath 0 u
abbrev Dec.openPath (u : Path) (D : Dec) := D.openRecPath 0 u
abbrev Trm.openPath (u : Path) (t : Trm) := t.openRecPath 0 u
abbrev Val.openPath (u : Path) (v : Val) := v.openRecPath 0 u
abbrev Def.openPath (u : Path) (d : Def) := d.openRecPath 0 u
abbrev Defs.openPath (u : Path) (ds : Defs) := ds.openRecPath 0 u
abbrev DefRhs.openPath (u : Path) (rhs : DefRhs) := rhs.openRecPath 0 u

/-! ## Path replacement -/

mutual
  inductive ReplTyp : Path → Path → Typ → Typ → Prop where
    | rcd : ReplDec p q D₁ D₂ → ReplTyp p q (.rcd D₁) (.rcd D₂)
    | andLeft : ReplTyp p q T₁ T₂ → ReplTyp p q (.and T₁ U) (.and T₂ U)
    | andRight : ReplTyp p q T₁ T₂ → ReplTyp p q (.and U T₁) (.and U T₂)
    | path : ReplTyp p q (.path (p.selectFields fields) A)
        (.path (q.selectFields fields) A)
    | bnd : ReplTyp p q T₁ T₂ → ReplTyp p q (.bnd T₁) (.bnd T₂)
    | allDom : ReplTyp p q T₁ T₂ → ReplTyp p q (.all T₁ U) (.all T₂ U)
    | allCod : ReplTyp p q T₁ T₂ → ReplTyp p q (.all U T₁) (.all U T₂)
    | sngl : ReplTyp p q (.sngl (p.selectFields fields))
        (.sngl (q.selectFields fields))

  inductive ReplDec : Path → Path → Dec → Dec → Prop where
    | typLo : ReplTyp p q T₁ T₂ →
        ReplDec p q (.typ A T₁ U) (.typ A T₂ U)
    | typHi : ReplTyp p q T₁ T₂ →
        ReplDec p q (.typ A U T₁) (.typ A U T₂)
    | trm : ReplTyp p q T₁ T₂ →
        ReplDec p q (.trm a T₁) (.trm a T₂)
end

/-! ## Free variables -/

def AVar.fv : AVar → Vars
  | .bound _ => ∅
  | .free x => {x}

def Path.fv : Path → Vars
  | .select x _ => x.fv

mutual
  def Typ.fv : Typ → Vars
    | .top | .bot => ∅
    | .rcd D => D.fv
    | .and T U | .all T U => T.fv ∪ U.fv
    | .path p _ | .sngl p => p.fv
    | .bnd T => T.fv

  def Dec.fv : Dec → Vars
    | .typ _ T U => T.fv ∪ U.fv
    | .trm _ T => T.fv
end

mutual
  def Trm.fv : Trm → Vars
    | .val v => v.fv
    | .path p => p.fv
    | .app p q => p.fv ∪ q.fv
    | .letE t₁ t₂ => t₁.fv ∪ t₂.fv
    | .caseE p q _ t₁ t₂ => p.fv ∪ q.fv ∪ t₁.fv ∪ t₂.fv

  def Val.fv : Val → Vars
    | .new p _ T ds => p.fv ∪ T.fv ∪ ds.fv
    | .lambda T t => T.fv ∪ t.fv

  def Def.fv : Def → Vars
    | .typ _ T => T.fv
    | .trm _ rhs => rhs.fv

  def Defs.fv : Defs → Vars
    | .nil => ∅
    | .cons ds d => ds.fv ∪ d.fv

  def DefRhs.fv : DefRhs → Vars
    | .path p => p.fv
    | .val v => v.fv
end

/-! ## Environments -/

abbrev Env (α : Type) := List (Var × α)
abbrev Ctx := Env Typ
abbrev Sta := Env Val

namespace Env

def empty : Env α := []

/-- Add the newest binding at the front of an environment. -/
def push (G : Env α) (x : Var) (a : α) : Env α := (x, a) :: G

/-- Concatenate environments in the same order as TLC's `G & H`. -/
def concat (G H : Env α) : Env α := H ++ G

def dom (G : Env α) : Vars := (G.map Prod.fst).toFinset

def Fresh (x : Var) (G : Env α) : Prop := x ∉ G.dom

def Ok (G : Env α) : Prop := List.Nodup (G.map Prod.fst)

inductive Binds (x : Var) (a : α) : Env α → Prop where
  | here : Binds x a ((x, a) :: G)
  | there : x ≠ y → Binds x a G → Binds x a ((y, b) :: G)

def fvValues (fv : α → Vars) (G : Env α) : Vars :=
  G.foldl (fun xs binding => xs ∪ fv binding.2) ∅

end Env

def Ctx.fvTypes (G : Ctx) : Vars := Env.fvValues Typ.fv G
def Sta.fvVals (σ : Sta) : Vars := Env.fvValues Val.fv σ

/-! ## Record and inert types -/

mutual
  inductive RecordDec : Dec → Prop where
    | typ : RecordDec (.typ A T T)
    | trm : InertTyp T → RecordDec (.trm a T)
    | trmSngl : RecordDec (.trm a (.sngl p))

  inductive RecordTyp : Typ → Finset Label → Prop where
    | one : RecordDec D → l = D.label → RecordTyp (.rcd D) {l}
    | cons : RecordTyp T labels → RecordDec D → l = D.label → l ∉ labels →
        RecordTyp (.and T (.rcd D)) (labels ∪ {l})

  inductive InertTyp : Typ → Prop where
    | all : InertTyp (.all S T)
    | bnd : RecordTyp T labels → InertTyp (.bnd T)
end

inductive RecordHas : Typ → Dec → Prop where
  | one : RecordHas (.rcd D) D
  | andLeft : RecordHas T D → RecordHas (.and T U) D
  | andRight : RecordHas U D → RecordHas (.and T U) D

def RecordType (T : Typ) : Prop := ∃ labels, RecordTyp T labels

inductive Inert : Ctx → Prop where
  | empty : Inert Env.empty
  | push : Inert G → InertTyp T → Env.Fresh x G → Inert (G.push x T)

/-! ## Unique flow -/

inductive UniqueMembership : Typ → Finset Label → Typ → Prop where
  | typ : UniqueMembership (.rcd (.typ A S T)) {Label.typ A}
      (.rcd (.typ A S T))
  | trm : UniqueMembership (.rcd (.trm a T)) {Label.trm a}
      (.rcd (.trm a T))
  | bnd : UniqueMembership (.bnd T) ∅ (.bnd T)
  | andLeft : UniqueMembership U₁ labels₁ T₁ →
      UniqueMembership U₂ labels₂ T₂ → Disjoint labels₁ labels₂ →
      UniqueMembership (.and U₁ U₂) (labels₁ ∪ labels₂) T₁
  | andRight : UniqueMembership U₁ labels₁ T₁ →
      UniqueMembership U₂ labels₂ T₂ → Disjoint labels₁ labels₂ →
      UniqueMembership (.and U₁ U₂) (labels₁ ∪ labels₂) T₂

def Unique (U T : Typ) : Prop :=
  ∃ labels : Finset Label, UniqueMembership U labels T

/-! ## Tight bounds -/

mutual
  def Typ.tightBounds : Typ → Prop
    | .rcd D => D.tightBounds
    | .and U V => U.tightBounds ∧ V.tightBounds
    | .bnd U => U.tightBounds
    | _ => True

  def Dec.tightBounds : Dec → Prop
    | .trm _ T => T.tightBounds
    | .typ _ T U => T = U
end

/-! ## Typing and subtyping -/

set_option autoImplicit true in
mutual
  inductive Typed : Ctx → Trm → Typ → Prop where
    | var : Env.Binds x T G → Typed G (.var x) T
    | allIntro (L : Vars) :
        (∀ z, z ∉ L → Typed (G.push z T) (t.open z) (U.open z)) →
        Typed G (.val (.lambda T t)) (.all T U)
    | allElim : Typed G (.path p) (.all S T) → Typed G (.path q) S →
        Typed G (.app p q) (T.openPath q)
    | newIntro (L : Vars) :
        (∀ z, z ∉ L →
          TypedDefs z [] (G.push z (T.open z)) (ds.open z) (T.open z)) →
        (∀ z, z ∉ L →
          Typed (G.push z (T.open z)) (.path (.var z))
            ((.path p A : Typ).open z)) →
        Typed G (.val (.new p A T ds)) (.bnd T)
    | newElim : Typed G (.path p) (.rcd (.trm a T)) →
        Typed G (.path (p.selectField a)) T
    | rcdIntro : Typed G (.path (p.selectField a)) T →
        Typed G (.path p) (.rcd (.trm a T))
    | letE (L : Vars) : Typed G t T →
        (∀ x, x ∉ L → Typed (G.push x T) (u.open x) U) →
        Typed G (.letE t u) U
    | caseE (L : Vars) : Typed G (.path p) S → Typed G (.path q) U →
        (∀ y, y ∉ L →
          Typed (G.push y (.and (.sngl p) (.path q A))) (t₁.open y) T) →
        Typed G t₂ T → Typed G (.caseE p q A t₁ t₂) T
    | sngl : Typed G (.path p) (.sngl q) → Typed G (.path q) T →
        Typed G (.path p) T
    | self : Typed G (.path p) T → Typed G (.path p) (.sngl p)
    | pathElim : Typed G (.path p) (.sngl q) →
        Typed G (.path (q.selectField a)) T →
        Typed G (.path (p.selectField a)) (.sngl (q.selectField a))
    | recIntro : Typed G (.path p) (T.openPath p) →
        Typed G (.path p) (.bnd T)
    | recElim : Typed G (.path p) (.bnd T) →
        Typed G (.path p) (T.openPath p)
    | andIntro : Typed G (.path p) T → Typed G (.path p) U →
        Typed G (.path p) (.and T U)
    | sub : Typed G t T → Subtyp G T U → Typed G t U

  inductive TypedDef : Var → Fields → Ctx → Def → Dec → Prop where
    | typ : TypedDef x fields G (.typ A T) (.typ A T T)
    | all : Typed G (.val (.lambda T t)) (.all U V) →
        TypedDef x fields G (.trm b (.val (.lambda T t)))
          (.trm b (.all U V))
    | new (p : Path) : p = .select (.free x) fields → Typ.tightBounds (.bnd T) →
        TypedDefs x (b :: fields) G (ds.openPath (p.selectField b))
          (T.openPath (p.selectField b)) →
        Typed G (.path (p.selectField b)) ((.path q A : Typ).openPath (p.selectField b)) →
        TypedDef x fields G (.trm b (.val (.new q A T ds))) (.trm b (.bnd T))
    | path : Typed G (.path q) T →
        TypedDef x fields G (.trm b (.path q)) (.trm b (.sngl q))

  inductive TypedDefs : Var → Fields → Ctx → Defs → Typ → Prop where
    | one : TypedDef x fields G d D →
        TypedDefs x fields G (.cons .nil d) (.rcd D)
    | cons : TypedDefs x fields G ds T → TypedDef x fields G d D →
        ds.Hasnt d.label →
        TypedDefs x fields G (.cons ds d) (.and T (.rcd D))

  inductive Subtyp : Ctx → Typ → Typ → Prop where
    | top : Subtyp G T .top
    | bot : Subtyp G .bot T
    | refl : Subtyp G T T
    | trans : Subtyp G S T → Subtyp G T U → Subtyp G S U
    | andLeft : Subtyp G (.and T U) T
    | andRight : Subtyp G (.and T U) U
    | andIntro : Subtyp G S T → Subtyp G S U → Subtyp G S (.and T U)
    | fld : Subtyp G T U → Subtyp G (.rcd (.trm a T)) (.rcd (.trm a U))
    | fldInv : Subtyp G U₁ (.rcd (.trm a T₂)) →
        Unique U₁ (.rcd (.trm a T₁)) → Subtyp G T₁ T₂
    | typ : Subtyp G S₂ S₁ → Subtyp G T₁ T₂ →
        Subtyp G (.rcd (.typ A S₁ T₁)) (.rcd (.typ A S₂ T₂))
    | typInvLo : Subtyp G U₁ (.rcd (.typ A S₂ T₂)) →
        Unique U₁ (.rcd (.typ A S₁ T₁)) → Subtyp G S₂ S₁
    | typInvHi : Subtyp G U₁ (.rcd (.typ A S₂ T₂)) →
        Unique U₁ (.rcd (.typ A S₁ T₁)) → Subtyp G T₁ T₂
    | allInv : Subtyp G (.all S₁ T₁) (.all S₂ T₂) → Subtyp G S₂ S₁
    | snglPQ : Typed G (.path p) (.sngl q) → Typed G (.path q) U →
        ReplTyp p q T T' → Subtyp G T T'
    | snglQP : Typed G (.path p) (.sngl q) → Typed G (.path q) U →
        ReplTyp q p T T' → Subtyp G T T'
    | selLo : Typed G (.path p) (.rcd (.typ A S T)) →
        Subtyp G S (.path p A)
    | selHi : Typed G (.path p) (.rcd (.typ A S T)) →
        Subtyp G (.path p A) T
    | all (L : Vars) : Subtyp G S₂ S₁ →
        (∀ x, x ∉ L → Subtyp (G.push x S₂) (T₁.open x) (T₂.open x)) →
        Subtyp G (.all S₁ T₁) (.all S₂ T₂)
end

/-! ## Well-typed stores -/

inductive WellTyped : Ctx → Sta → Prop where
  | empty : WellTyped Env.empty Env.empty
  | push : WellTyped G σ → Env.Fresh x G → Env.Fresh x σ →
      Typed G (.val v) T → WellTyped (G.push x T) (σ.push x v)

end CDot
