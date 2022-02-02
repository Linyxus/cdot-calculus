(** remove printing ~ *)

(** * pDOT Abstract Syntax and Type System *)

Set Implicit Arguments.

(** This proof uses the
    #<a href="http://www.chargueraud.org/softs/tlc/">TLC</a>#
    meta-theory library by Arthur Chargueraud. *)
Require Export TLC.LibLN.
Require Import TLC.LibOption.
Require Import List String.

Parameter typ_label: Set.
Parameter trm_label: Set.

(** ** Abstract Syntax *)

(** *** Variables ([x], [y], [z])
    The proof represents variables using the
    #<a href="http://www.chargueraud.org/softs/ln/">locally nameless representation</a>#:
    - [avar_b n] represents a variable using the de Bruijn index [n];
    - [avar_f x] represents a free variable with name [x].
    de Bruijn-indexed variables represent bound variables, whereas named variables represent free variables
    that are in the evaluation context/type environment.  *)
Inductive avar : Set :=
  | avar_b : nat -> avar
  | avar_f : var -> avar.

(** *** Term and type members
        Type member labels ([A], [B], [C]) and term (field) member labels ([a], [b], [c]).  *)
Inductive label: Set :=
| label_typ: typ_label -> label
| label_trm: trm_label -> label.

(** The fields of a path in reverse order.
    E.g. for a path [x. a1. a2... aₙ], a list [aₙ, ..., a2, a1]. *)
Definition fields := list trm_label.

(** A path, [x.a1.a2...aₙ], represented through its receiver [x] and reversed list of fields
 [aₙ, ..., a_2, a_1] *)
Inductive path :=
  | p_sel : avar -> fields ->  path.

(** *** Types
    Types ([typ], [S], [T], [U]) and type declarations ([dec], [D]):
    - [typ_top] represents [top];
    - [typ_bot] represents [bottom];
    - [typ_rcd d] represents a record type [d], where [d] is either a type or field declaration;
    - [typ_and T U] represents an intersection type [T /\ U];
    - [typ_sel p A] represents type selection [p.A];
    - [typ_bnd T] represents a recursive type [mu(x: T)]; however, since [x] is bound in the recursive type,
      it is referred to in [T] using the de Bruijn index 0, and is therefore omitted from the type representation;
      we will denote recursive types as [mu(T)];
    - [typ_all T U] represents the dependent function type [forall(x: T)U]; as in the previous case,
      [x] represents a variable bound in [U], and is therefore omitted from the representation;
      we will denote function types as [forall(T)U];
    - [typ_sngl p] denotes a singleton type [p.type]. *)
Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_rcd  : dec -> typ
  | typ_and  : typ -> typ -> typ
  | typ_path : path -> typ_label -> typ
  | typ_bnd  : typ -> typ
  | typ_all  : typ -> typ -> typ
  | typ_sngl : path -> typ
(**
  - [dec_typ A S T] represents a type declaraion [{A: S..T}];
  - [dec_trm a T] represents a field declaration [{a: T}] . *)
with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec
  | dec_trm  : trm_label -> typ -> dec.

(** *** Terms
  Terms ([t], [u]), values ([v]),
   member definitions ([d] and [defs], [ds]):
  - [trm_val v] represents a value [v];
  - [trm_app p q] represents a function application [p q];
  - [trm_let t u] represents a let binding [let x = t in u]; since x is bound in [u],
    it is referred to in [u] using the de Bruijn index 0, and is therefore omitted from
    the let-term representation; we will denote let terms as [let t in u];
  - [trm_path p] represents a path [p]. *)
Inductive trm : Set :=
  | trm_val  : val -> trm
  | trm_app  : path -> path -> trm
  | trm_let  : trm -> trm -> trm
  | trm_path : path -> trm
(**
  - [val_new T ds] represents the object [nu(x: T)ds]; the variable [x] is bound in [T]
    and [ds] and is omitted from the representation;
    we will denote new object definitions as [nu(T)ds];
  - [val_lambda T t] represents a function [lambda(x: T)t]; again, [x] is bound in [t]
    and is omitted;
    we will denote lambda terms as [lambda(T)t. *)
with val : Set :=
  | val_new  : typ -> defs -> val
  | val_lambda : typ -> trm -> val
(**
  - [def_typ A T] represents a type-member definition [{A = T}];
  - [def_trm a t] represents a field definition [{a = t}]; *)
with def : Set :=
  | def_typ  : typ_label -> typ -> def
  | def_trm  : trm_label -> def_rhs -> def
(**
  [defs] represents a list of definitions that are part of an intersection
  - [defs_nil] represents the empty list;
  - [defs_cons d ds] represents a concatenation of the definition [d] to the definitions [ds]. *)
with defs : Set :=
  | defs_nil : defs
  | defs_cons : defs -> def -> defs

with def_rhs : Set :=
  | defp : path -> def_rhs
  | defv : val -> def_rhs.

(** *** Useful definitions and notations *)

(** - field declarations [{a: T}] *)
Notation "'{' a '⦂' T '}'" := (dec_trm a T) (T at level 50).

(** - type declarations [{A: S..T}] *)
Notation "'{' A '>:' S '<:' T '}'" := (dec_typ A S T) (S at level 58).

(** - type intersection *)
Notation "T '∧' U" := (typ_and T U) (at level 30).

(** - dependent function types [∀(x: T)U] *)
Notation "'∀' '(' T ')' U" := (typ_all T U) (at level 30).

(** - path-dependent types [p.A] *)
Notation "p '↓' A" := (typ_path p A) (at level 30).

(** - recursive types [μ(x: T)] *)
Notation "'μ' T" := (typ_bnd T) (at level 30, T at level 50).

(** - top type *)
Notation "⊤" := typ_top.

(** - bottom type *)
Notation "⊥" := typ_bot.

(** singleton types [p.type] *)
Notation "'{{' p '}}'" := (typ_sngl p).

(** - object [ν(x: T)ds] *)
Notation "'ν' '(' T ')' ds" := (val_new T ds) (at level 40, T at level 40, ds at level 40).

(** - function [λ(x: T).t] *)
Notation "'λ' '(' T ')' t" := (val_lambda T t) (at level 50).

(** - field definition [{a = t}] (we do not restrict terms to stable terms syntactically but the type system
    can only typecheck stable field definitions) *)
Notation "'{' a ':=' t '}'" := (def_trm a t) (t at level 50).

(** - field definition with a path on the right-handside [{a = p}] *)
Notation "'{' a ':=p' p '}'" := (def_trm a (defp p)).

(** - field definition with a value on the right-handside [{a = v}] *)
Notation "'{' a ':=v' v '}'" := (def_trm a (defv v)).

(** - type member definition *)
Notation "'{' A '⦂=' T '}'" := (def_typ A T).

(** Shorthand definitions for variables and field selections *)

(** - a named variable *)
Notation pvar x := (p_sel (avar_f x) nil).

(** - a variable as a term *)
Notation  tvar x := (trm_path (pvar x)).

(** - field selection [p.b] on a path [p] *)
Definition sel_field (p : path) (b : trm_label) :=
  match p with
  | p_sel x bs => p_sel x (b :: bs)
  end.

(** - selection of multiple fields [p. b1. b2... b_n] where [b_n, ..., b2, b1 = bs] *)
Definition sel_fields (p : path) (bs : list trm_label) :=
  match p with
  | p_sel x bs' => p_sel x (bs ++ bs')
  end.

(** - field selection [p.a] *)
Notation "p '•' a" := (sel_field p a) (at level 5).

(** - selection of multiple fields [p.bs] *)
Notation "p '••' bs" := (sel_fields p bs) (at level 5).

(** - helper functions to retrieve labels of declarations and definitions *)

Definition label_of_def(d: def): label := match d with
| def_typ A _ => label_typ A
| { a := t }  => label_trm a
end.

Definition label_of_dec(D: dec): label := match D with
| { A >: _ <: _ } => label_typ A
| { a ⦂ _ }  => label_trm a
end.

Fixpoint get_def(l: label)(ds: defs): option def :=
match ds with
| defs_nil => None
| defs_cons ds' d => If label_of_def d = l then Some d else get_def l ds'
end.

Definition defs_has(ds: defs)(d: def) := get_def (label_of_def d) ds = Some d.

Definition defs_hasnt(ds: defs)(l: label) := get_def l ds = None.

(** ** Opening *)
(** Opening takes a bound variable that is represented with a de Bruijn index [k]
    and replaces it by a named variable or path [u].
    The following functions define opening on paths, types, declarations, terms,
    values, and definitions.

    We will denote an identifier [X] opened with a variable [y] as [X^y]. *)

Definition open_rec_avar (k: nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
end.

Definition open_rec_path (k: nat) (u: var) (p: path): path :=
  match p with
  | p_sel x bs => p_sel (open_rec_avar k u x) bs
  end.

Fixpoint open_rec_typ (k: nat) (u: var) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (open_rec_dec k u D)
  | T1 ∧ T2        => open_rec_typ k u T1 ∧ open_rec_typ k u T2
  | p ↓ L          => open_rec_path k u p ↓ L
  | μ T            => μ (open_rec_typ (S k) u T)
  | ∀(T1) T2      => ∀(open_rec_typ k u T1) open_rec_typ (S k) u T2
  | {{ p }}        => {{ open_rec_path k u p }}
  end
with open_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | { A >: T <: U } => { A >: open_rec_typ k u T <: open_rec_typ k u U }
  | { a ⦂ T } => { a ⦂ open_rec_typ k u T }
  end.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_val v      => trm_val (open_rec_val k u v)
  | trm_path p     => trm_path (open_rec_path k u p)
  | trm_app p q    => trm_app (open_rec_path k u p) (open_rec_path k u q)
  | trm_let t1 t2  => trm_let (open_rec_trm k u t1) (open_rec_trm (S k) u t2)
  end
with open_rec_val (k: nat) (u: var) (v: val): val :=
  match v with
  | ν(T)ds   => ν (open_rec_typ (S k) u T) open_rec_defs (S k) u ds
  | λ(T) e  => λ(open_rec_typ k u T) open_rec_trm (S k) u e
  end
with open_rec_def (k: nat) (u: var) (d: def): def :=
  match d with
  | def_typ A T => def_typ A (open_rec_typ k u T)
  | { a := t } => { a := open_rec_defrhs k u t }
  end
with open_rec_defs (k: nat) (u: var) (ds: defs): defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons tl d => defs_cons (open_rec_defs k u tl) (open_rec_def k u d)
  end
with open_rec_defrhs (k: nat) (u: var) (drhs: def_rhs) : def_rhs :=
  match drhs with
  | defp p => defp (open_rec_path k u p)
  | defv v => defv (open_rec_val k u v)
  end.

Definition open_avar u a := open_rec_avar  0 u a.
Definition open_typ  u t := open_rec_typ   0 u t.
Definition open_dec  u D := open_rec_dec   0 u D.
Definition open_trm  u e := open_rec_trm   0 u e.
Definition open_val  u v := open_rec_val   0 u v.
Definition open_def  u d := open_rec_def   0 u d.
Definition open_defs u l := open_rec_defs  0 u l.
Definition open_defrhsdd u t := open_rec_defrhs 0 u t.
Definition open_path u p := open_rec_path  0 u p.

Definition open_paths u ps := map (open_path u) ps.

(** Path opening replaces in some syntax a bound variable with dangling index (k)
    by a path p. *)

(** Opening of variables *)
Definition open_rec_avar_p (k: nat) (u: path) (a: avar) : path :=
  match a with
  | avar_b i => If k = i then u else p_sel (avar_b i) nil
  | avar_f x => pvar x
  end.

(** Opening of paths

   Example:

   [0.a.b    ^ y.c.d    == y.c.d.a.b]

   our representation:

   [0 [b, a] ^ y [d, c] == y [b, a, d, c]] *)
Definition open_rec_path_p (k: nat) (u: path) (p: path): path :=
  match p, u with
  | p_sel x bs, p_sel y cs=>
    match x with
    | avar_b i => If k = i then p_sel y (bs ++ cs) else p (* maintaining reverse order of fields *)
    | avar_f x => p
    end
  end.

Fixpoint open_rec_typ_p (k: nat) (u: path) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (open_rec_dec_p k u D)
  | T1 ∧ T2        => open_rec_typ_p k u T1 ∧ open_rec_typ_p k u T2
  | p ↓ L          => open_rec_path_p k u p ↓ L
  | μ       T      => μ (open_rec_typ_p (S k) u T)
  | ∀(T1) T2       => ∀(open_rec_typ_p k u T1) open_rec_typ_p (S k) u T2
  | {{ p }}        => {{ open_rec_path_p k u p }}
  end
with open_rec_dec_p (k: nat) (u: path) (D: dec): dec :=
  match D with
  | { A >: T <: U } => { A >: open_rec_typ_p k u T <: open_rec_typ_p k u U }
  | { a ⦂ T } => { a ⦂ open_rec_typ_p k u T }
  end.

Fixpoint open_rec_trm_p (k: nat) (u: path) (t: trm): trm :=
  match t with
  | trm_val v      => trm_val (open_rec_val_p k u v)
  | trm_path p     => trm_path (open_rec_path_p k u p)
  | trm_app p q    => trm_app (open_rec_path_p k u p) (open_rec_path_p k u q)
  | trm_let t1 t2  => trm_let (open_rec_trm_p k u t1) (open_rec_trm_p (S k) u t2)
  end
with open_rec_val_p (k: nat) (u: path) (v: val): val :=
  match v with
  | ν(T) ds => ν(open_rec_typ_p (S k) u T) open_rec_defs_p (S k) u ds
  | λ(T) e  => λ(open_rec_typ_p k u T) open_rec_trm_p (S k) u e
  end
with open_rec_def_p (k: nat) (u: path) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (open_rec_typ_p k u T)
  | { a := t } => { a := open_rec_defrhs_p k u t }
  end
with open_rec_defs_p (k: nat) (u: path) (ds: defs): defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons tl d => defs_cons (open_rec_defs_p k u tl) (open_rec_def_p k u d)
  end
with open_rec_defrhs_p (k: nat) (u: path) (drhs: def_rhs) : def_rhs :=
  match drhs with
  | defp p => defp (open_rec_path_p k u p)
  | defv v => defv (open_rec_val_p k u v)
  end.

Definition open_avar_p u a := open_rec_avar_p  0 u a.
Definition open_typ_p  u t := open_rec_typ_p   0 u t.
Definition open_dec_p  u D := open_rec_dec_p   0 u D.
Definition open_path_p u p := open_rec_path_p  0 u p.
Definition open_trm_p  u t := open_rec_trm_p   0 u t.
Definition open_val_p  u v := open_rec_val_p   0 u v.
Definition open_def_p  u d := open_rec_def_p   0 u d.
Definition open_defs_p u l := open_rec_defs_p 0 u l.
Definition open_defrhs_p u t := open_rec_defrhs_p 0 u t.

(** ** Path Replacement *)

(** [repl_typ p q T U] represents the fact that [T[q/p] = U];
    more precisely,
    - [T] has a path [p.bs] that starts with [p]
    - replacing that occurrence of [p] with [q] yields the type [U] *)

Inductive repl_typ : path -> path -> typ -> typ -> Prop :=
| rrcd: forall p q D1 D2,
    repl_dec p q D1 D2 ->
    repl_typ p q (typ_rcd D1) (typ_rcd D2)
| rand1: forall p q T1 T2 U,
    repl_typ p q T1 T2 ->
    repl_typ p q (T1 ∧ U) (T2 ∧ U)
| rand2: forall p q T1 T2 U,
    repl_typ p q T1 T2 ->
    repl_typ p q (U ∧ T1) (U ∧ T2)
| rpath: forall p q bs A,
    repl_typ p q (p••bs ↓ A) (q••bs ↓ A)
| rbnd: forall p q T1 T2,
    repl_typ p q T1 T2 ->
    repl_typ p q (μ T1) (μ T2)
| rall1: forall p q T1 T2 U,
    repl_typ p q T1 T2 ->
    repl_typ p q (∀(T1) U) (∀(T2) U)
| rall2: forall p q T1 T2 U,
    repl_typ p q T1 T2 ->
    repl_typ p q (∀(U) T1) (∀(U) T2)
| rsngl: forall p q bs,
    repl_typ p q {{ p••bs }} {{ q••bs }}
with repl_dec : path -> path -> dec -> dec -> Prop :=
| rdtyp1: forall p q T1 T2 A U,
    repl_typ p q T1 T2 ->
    repl_dec p q {A >: T1 <: U} {A >: T2 <: U}
| rdtyp2: forall p q T1 T2 A U,
    repl_typ p q T1 T2 ->
    repl_dec p q {A >: U <: T1} {A >: U <: T2}
| rdtrm: forall p q T1 T2 a,
    repl_typ p q T1 T2 ->
    repl_dec p q {a ⦂ T1} {a ⦂ T2}.

Hint Constructors repl_typ repl_dec.

(** ** Free variables
      Functions that retrieve the free variables of a symbol. *)

(** Free variable in a variable. *)
Definition fv_avar (a: avar) : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

(** Free variables in a path. *)
Fixpoint fv_path (p: path) : vars :=
  match p with
  | p_sel x bs => fv_avar x
  end.

(** Free variables in a type or declaration. *)
Fixpoint fv_typ (T: typ) : vars :=
  match T with
  | typ_top        => \{}
  | typ_bot        => \{}
  | typ_rcd D      => fv_dec D
  | T ∧ U          => (fv_typ T) \u (fv_typ U)
  | p ↓ L          => fv_path p
  | μ T            => fv_typ T
  | ∀(T1) T2       => (fv_typ T1) \u (fv_typ T2)
  | {{ p }}        => fv_path p
  end
with fv_dec (D: dec) : vars :=
  match D with
  | { A >: T <: U } => (fv_typ T) \u (fv_typ U)
  | { a ⦂ T } => fv_typ T
  end.

(** Free variables in a term, value, or definition. *)
Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_val v        => (fv_val v)
  | trm_path p       => (fv_path p)
  | trm_app p q      => (fv_path p) \u (fv_path q)
  | trm_let t1 t2    => (fv_trm t1) \u (fv_trm t2)
  end
with fv_val (v: val) : vars :=
  match v with
  | ν(T) ds    => (fv_typ T) \u (fv_defs ds)
  | λ(T)t      => (fv_typ T) \u (fv_trm t)
  end
with fv_def (d: def) : vars :=
  match d with
  | def_typ _ T => (fv_typ T)
  | { _ := t }  => (fv_defrhs t)
  end
with fv_defs(ds: defs) : vars :=
  match ds with
  | defs_nil         => \{}
  | defs_cons tl d   => (fv_defs tl) \u (fv_def d)
  end
with fv_defrhs(drhs: def_rhs) : vars :=
  match drhs with
  | defp p => fv_path p
  | defv v => fv_val v
  end.

(** Typing environment ([G]) *)
Definition ctx := env typ.

(** The sequence of variable-to-value let bindings, [(let x = v in)*],
     is represented as a value environment that maps variables to values: *)
Definition sta := env val.

(** Free variables in the range (types) of a context *)
Definition fv_ctx_types(G: ctx): vars :=
  (fv_in_values (fun T => fv_typ T) G).
Definition fv_sta_vals(s: sta): vars := (fv_in_values (fun v => fv_val v) s).

(** ** Record and Inert Types *)

(** A record declaration is either a type declaration with equal bounds,
    or a field declaration.*)
Inductive record_dec : dec -> Prop :=
| rd_typ : forall A T, record_dec { A >: T <: T }
| rd_trm : forall a T, inert_typ T -> record_dec { a ⦂ T }
| rd_trm_sngl : forall a p, record_dec { a ⦂ {{ p }} }

(** Given a record declaration, a [record_typ] keeps track of the declaration's
    field member labels (i.e. names of fields) and type member labels
    (i.e. names of abstract type members). [record_typ] also requires that the
    labels are distinct.  *)
with record_typ : typ -> fset label -> Prop :=
| rt_one : forall D l,
  record_dec D ->
  l = label_of_dec D ->
  record_typ (typ_rcd D) \{l}
| rt_cons: forall T ls D l,
  record_typ T ls ->
  record_dec D ->
  l = label_of_dec D ->
  l \notin ls ->
  record_typ (T ∧ typ_rcd D) (union ls \{l})

(** A type is inert if it is either a dependent function type, or a recursive type [μ(x: T)]
    where [T] is a record type.
    For example, the following types are inert:
    - [lambda(x: S)T]
    - [mu(x: {a: T} ∧ {B: U..U})]
    - [mu(x: {C: {A: T..U}..{A: T..U}})]
    - [mu(x: {a: μ(y: {A: T..T})})]
    And the following types are not inert:
    - [{a: T}]
    - [{B: U..U}]
    - [top]
    - [x.A]
    - [mu(x: {B: S..T})], where [S ≠ T]
    - [mu(x: {a: μ(y: {A: S..T})})], where [S ≠ T]*)
with inert_typ : typ -> Prop :=
  | inert_typ_all : forall S T, inert_typ (∀(S) T)
  | inert_typ_bnd : forall T ls,
      record_typ T ls ->
      inert_typ (μ T).

(** Given a type [T = D1 /\ D2 /\ ... /\ Dn] and member declaration [D], [record_has T D] tells whether
    [D] is contained in the intersection of [Di]'s. *)
Inductive record_has: typ -> dec -> Prop :=
| rh_one : forall D,
    record_has (typ_rcd D) D
| rh_andl : forall T U D,
    record_has T D ->
    record_has (T ∧ U) D
| rh_andr : forall T U D,
    record_has U D ->
    record_has (T ∧ U) D.

(** A [record_type] is a [record_typ] with an unspecified set of labels. The meaning
    of [record_type] is an intersection of type/field declarations with distinct labels. *)
Definition record_type T := exists ls, record_typ T ls.

(** An inert context is a typing context whose range consists only of inert types. *)
Inductive inert : ctx -> Prop :=
  | inert_empty : inert empty
  | inert_push : forall G x T,
      inert G ->
      inert_typ T ->
      x # G ->
      inert (G & x ~ T).


(** ** Unique Flow *)

Inductive rcd_with_unique_typ : typ -> fset typ_label -> typ -> Prop :=

| rcd_typ : forall A S T,
    rcd_with_unique_typ (typ_rcd (dec_typ A S T)) \{A} (typ_rcd (dec_typ A S T))

| rcd_fld : forall a T,
    rcd_with_unique_typ (typ_rcd (dec_trm a T)) \{} (typ_rcd (dec_trm a T))

| rcd_rec : forall T,
    rcd_with_unique_typ (μ T) \{} (μ T)

| rcd_andl : forall U1 U2 L1 L2 T1 T2,
    rcd_with_unique_typ U1 L1 T1 ->
    rcd_with_unique_typ U2 L2 T2 ->
    disjoint L1 L2 ->
    rcd_with_unique_typ (typ_and U1 U2) (L1 \u L2) T1

| rcd_andr : forall U1 U2 L1 L2 T1 T2,
    rcd_with_unique_typ U1 L1 T1 ->
    rcd_with_unique_typ U2 L2 T2 ->
    disjoint L1 L2 ->
    rcd_with_unique_typ (typ_and U1 U2) (L1 \u L2) T2
.

Hint Constructors rcd_with_unique_typ.

Notation "U '↘' S" :=
  (exists ls, rcd_with_unique_typ U ls S) (at level 60).


(** * Trivial types *)

Inductive trivial_dec : dec -> Prop :=
| td_typ_refl : forall A T, trivial_dec { A >: T <: T }
| td_typ_bot : forall A T, trivial_dec { A >: ⊥ <: T }
| td_typ_top : forall A T, trivial_dec { A >: T <: ⊤ }
| td_trm : forall a T, trivial_typ T -> trivial_dec { a ⦂ T }
| td_trm_sngl : forall a p, trivial_dec { a ⦂ {{ p }} }

with trivial_record_typ : typ -> fset label -> Prop :=
| trt_one : forall D l,
  trivial_dec D ->
  l = label_of_dec D ->
  trivial_record_typ (typ_rcd D) \{l}
| trt_cons: forall T ls D l,
  trivial_record_typ T ls ->
  trivial_dec D ->
  l = label_of_dec D ->
  l \notin ls ->
  trivial_record_typ (T ∧ typ_rcd D) (union ls \{l})

with trivial_typ : typ -> Prop :=
  | trivial_typ_all : forall S T, trivial_typ (∀(S) T)
  | trivial_typ_bnd : forall T ls,
      trivial_record_typ T ls ->
      trivial_typ (μ T).


(** ** Typing Rules *)

(** The [tight_bounds] function ensures that all type declarations nested inside a
 type have equal bounds (except the ones that are inside of function types) *)
Fixpoint tight_bounds T :=
  match T with
  | typ_rcd D => tight_bounds_dec D
  | U ∧ V     => tight_bounds U /\ tight_bounds V
  | typ_bnd U => tight_bounds U
  | _         => True
  end
with tight_bounds_dec D :=
  match D with
  | { a ⦂ T }       => tight_bounds T
  | { A >: T <: U } => T = U
  end.

Reserved Notation "G '⊢' t ':' T" (at level 40, t at level 59).
Reserved Notation "G '⊢' T '<:' U" (at level 40, T at level 59).
Reserved Notation "x ';' bs ';' G '⊢' d ':' D"
         (at level 40, bs at level 39, G at level 39, d at level 59).
Reserved Notation "x ';' bs ';' G '⊢' ds '::' D"
         (at level 40, bs at level 39, G at level 39, ds at level 59).

(** *** Term typing [G ⊢ t: T] *)
Inductive ty_trm : ctx -> trm -> typ -> Prop :=

(** [[
G(x) = T
________
G ⊢ x: T
]]
*)
| ty_var : forall x T G,
    binds x T G ->
    G ⊢ tvar x : T

(** [[
G, z: T ⊢ t^z: U^z
z fresh
__________________
G ⊢ lambda(T)t: forall(T)U
]]
*)
| ty_all_intro : forall L G T t U,
    (forall z, z \notin L ->
      G & z ~ T ⊢ open_trm z t : open_typ z U) ->
    G ⊢ trm_val (λ(T) t) : ∀(T) U

(** [[
G ⊢ p: forall(S)T
G ⊢ q: S
_________________
G ⊢ p q: T^q
]]
*)
| ty_all_elim : forall G p q S T,
    G ⊢ trm_path p : ∀(S) T ->
    G ⊢ trm_path q : S ->
    G ⊢ trm_app p q : open_typ_p q T

(** [[
z; G, z: T^z ⊢ ds^z :: T^z
z fresh
_________________
G ⊢ nu(T)ds :: mu(T)
]]
*)
| ty_new_intro : forall L G T ds,
    (forall z, z \notin L ->
      z; nil; G & (z ~ open_typ z T) ⊢ open_defs z ds :: open_typ z T) ->
    G ⊢ trm_val (ν(T) ds) : μ T

(** [[
G ⊢ p: {a: T}
_________________
G ⊢ p.a: T
]]
*)
| ty_new_elim : forall G p a T,
    G ⊢ trm_path p : typ_rcd { a ⦂ T } ->
    G ⊢ trm_path p•a : T

(** [[
G ⊢ p.a: T
_________________
G ⊢ p: {a: T}
]]
*)
| ty_rcd_intro : forall G p a T,
    G ⊢ trm_path p•a : T ->
    G ⊢ trm_path p : typ_rcd { a ⦂ T }

(** [[
G ⊢ t: T
G, x: T ⊢ u^x: U
x fresh
_________________
G ⊢ let t in u: U
]]
*)
| ty_let : forall L G t u T U,
    G ⊢ t : T ->
    (forall x, x \notin L ->
      G & x ~ T ⊢ open_trm x u : U) ->
    G ⊢ trm_let t u : U

(** [[
G ⊢ p: q.type
G ⊢ q: T
_________________
G ⊢ p: T
]]
*)
| ty_sngl : forall G p q T,
    G ⊢ trm_path p : {{ q }} ->
    G ⊢ trm_path q : T ->
    G ⊢ trm_path p : T

(** [[
G ⊢ p: q.type
G ⊢ q.a
_________________
G ⊢ p.a: q.a.type
]]
*)
| ty_path_elim : forall G p q a T,
    G ⊢ trm_path p : {{ q }} ->
    G ⊢ trm_path q•a : T ->
    G ⊢ trm_path p•a : {{ q•a }}

(** [[
G ⊢ p: T^p
_________________
G ⊢ p: mu(T)
]]
*)
| ty_rec_intro : forall G p T,
    G ⊢ trm_path p : open_typ_p p T ->
    G ⊢ trm_path p : μ T

(** [[
G ⊢ p: mu(T)
_________________
G ⊢ p: T^p
]]
*)
| ty_rec_elim : forall G p T,
    G ⊢ trm_path p : μ T ->
    G ⊢ trm_path p : open_typ_p p T

(** [[
G ⊢ p: T
G ⊢ p: U
_________________
G ⊢ p: T /\ U
]]
*)
| ty_and_intro : forall G p T U,
    G ⊢ trm_path p : T ->
    G ⊢ trm_path p : U ->
    G ⊢ trm_path p : T ∧ U

(** [[
G ⊢ t: T
G ⊢ T <: U
_________________
G ⊢ t: U
]]
*)
| ty_sub : forall G t T U,
    G ⊢ t : T ->
    G ⊢ T <: U ->
    G ⊢ t : U
where "G '⊢' t ':' T" := (ty_trm G t T)

(** *** Single-definition typing [x; bs; G ⊢ d: D]
    The notation [x; bs; G ⊢ d : D] denotes the typing
    of a definition [d] with record-type [D] under the path [x.bs]
    (i.e. a path with receiver [x] and fields [bs]) *)
with ty_def : var -> fields -> ctx -> def -> dec -> Prop :=
(** [x.bs; G ⊢ {A = T}: {A: T..T}]   *)
| ty_def_typ : forall x bs G A T,
    x; bs; G ⊢ def_typ A T : { A >: T <: T }

(** [[
G ⊢ lambda(T)t: ∀(U)V
_________________
x.bs; G ⊢ {b = lambda(T)t}: {b: ∀(U)V}
]]
*)
 | ty_def_all : forall x bs G T t b U V,
    G ⊢ trm_val (λ(T) t) : ∀(U) V ->
    x; bs; G ⊢ { b :=v λ(T) t } : { b ⦂ ∀(U) V }

(** [[
x.bs.b; G ⊢ ds^x.bs.b: T^x.bs.b
_________________
x.bs; G ⊢ {b = nu(T)ds}: {b: T}
]]
*)
 | ty_def_new : forall x bs b G ds T p,
     p = p_sel (avar_f x) bs ->
     tight_bounds (μ T) ->
     x; (b :: bs); G ⊢ open_defs_p p•b ds :: open_typ_p p•b T ->
     x; bs; G ⊢ { b :=v ν(T) ds } : { b ⦂ μ T }

(** [[
G ⊢ q
_____________________________
x.bs; G ⊢ {b = q}: {b: q.type}
]]
*)
 | ty_def_path : forall x bs G q b T,
    G ⊢ trm_path q: T ->
    x; bs; G ⊢ { b :=p q } : { b ⦂ {{ q }} }

where "x ';' bs ';' G '⊢' d ':' D" := (ty_def x bs G d D)

(** *** Multiple-definition typing [x; bs; G ⊢ ds :: T]
    The notation [x; bs; G ⊢ ds :: T] denotes the typing
    of definitions [ds] with type [T] under the path [x.bs]
    (i.e. a path with receiver [x] and fields [bs]) *)
with ty_defs : var -> fields -> ctx -> defs -> typ -> Prop :=
(** [[
x.bs; G ⊢ d: D
___________________________
x.bs; G ⊢ d ++ defs_nil : D
]]
*)
| ty_defs_one : forall x bs G d D,
    x; bs; G ⊢ d : D ->
    x; bs; G ⊢ defs_cons defs_nil d :: typ_rcd D

(** [[
x.bs; G ⊢ ds :: T
x.bs; G ⊢ d: D
d ∉ ds
__________________________
x.bs; G ⊢ ds ++ d : T /\ D
]]
*)
| ty_defs_cons : forall x bs G d ds D T,
    x; bs; G ⊢ ds :: T ->
    x; bs; G ⊢ d : D ->
    defs_hasnt ds (label_of_def d) ->
    x; bs; G ⊢ defs_cons ds d :: T ∧ typ_rcd D
where "x ';' bs ';' G '⊢' ds '::' T" := (ty_defs x bs G ds T)

(** *** Subtyping [ G ⊢ T <: U] *)
with subtyp : ctx -> typ -> typ -> Prop :=

(** [[
G ⊢ T <: top
]]
*)
| subtyp_top: forall G T,
    G ⊢ T <: typ_top

(** [[
G ⊢ bot <: T
]]
*)
| subtyp_bot: forall G T,
    G ⊢ typ_bot <: T

(** [[
G ⊢ T <: T
]]
*)
| subtyp_refl: forall G T,
    G ⊢ T <: T

(** [[
G ⊢ S <: T
G ⊢ T <: U
_________________
G ⊢ S <: U
]]
*)
| subtyp_trans: forall G S T U,
    G ⊢ S <: T ->
    G ⊢ T <: U ->
    G ⊢ S <: U

(** [[
G ⊢ T /\ U <: T
]]
*)
| subtyp_and11: forall G T U,
    G ⊢ T ∧ U <: T

(** [G ⊢ T /\ U <: U] *)
| subtyp_and12: forall G T U,
    G ⊢ T ∧ U <: U

(** [[
G ⊢ S <: T
G ⊢ S <: U
_________________
G ⊢ S <: T /\ U
]]
*)
| subtyp_and2: forall G S T U,
    G ⊢ S <: T ->
    G ⊢ S <: U ->
    G ⊢ S <: T ∧ U

(** [[
G ⊢ T <: U
_________________
G ⊢ {a: T} <: {a: U}
]]
*)
| subtyp_fld: forall G T U a,
    G ⊢ T <: U ->
    G ⊢ typ_rcd { a ⦂ T } <: typ_rcd { a ⦂ U }

(** [[
G ⊢ S2 <: S1
G ⊢ T1 <: T2
_________________
G ⊢ {A: S1..T1} <: {A: S2..T2}
]]
*)
| subtyp_typ: forall G S1 S2 T1 T2 A,
    G ⊢ S2 <: S1 ->
    G ⊢ T1 <: T2 ->
    G ⊢ typ_rcd { A >: S1 <: T1 } <: typ_rcd { A >: S2 <: T2 }

(** [[
G ⊢ U1 <: U2
U1 ↘ {A: S1..T1}
U2 ↘ {A: S2..T2}
_________________
G ⊢ S2 <: S1
]]
*)
| subtyp_rcd_inv1: forall G U1 U2 S1 S2 T1 T2 A,
    G ⊢ U1 <: U2 ->
    U1 ↘ typ_rcd {A >: S1 <: T1} ->
    U2 ↘ typ_rcd {A >: S2 <: T2} ->
    G ⊢ S2 <: S1

(** [[
G ⊢ U1 <: U2
U1 ↘ {A: S1..T1}
U2 ↘ {A: S2..T2}
_________________
G ⊢ T1 <: T2
]]
*)
| subtyp_rcd_inv2: forall G U1 U2 S1 S2 T1 T2 A,
    G ⊢ U1 <: U2 ->
    U1 ↘ typ_rcd {A >: S1 <: T1} ->
    U2 ↘ typ_rcd {A >: S2 <: T2} ->
    G ⊢ T1 <: T2

(** [[
G ⊢ ∀(S1)T1 <: ∀(S2)T2
_________________
G ⊢ S2 <: S1
]]
*)
| subtyp_all_inv1 : forall G S1 T1 S2 T2,
    G ⊢ ∀(S1)T1 <: ∀(S2)T2 ->
    G ⊢ S2 <: S1

(** [[
G ⊢ ∀(S1)T1 <: ∀(S2)T2
T1 and T2 is non-dependent
S2 is a trivial type
__________________________
G ⊢ T1 <: T2
]]
*)
(* | subtyp_all_inv2 : forall G S1 T1 S2 T2, *)
(*     G ⊢ ∀(S1)T1 <: ∀(S2)T2 -> *)
(*     (forall x, open_typ x T1 = T1) -> *)
(*     (forall x, open_typ x T2 = T2) -> *)
(*     trivial_typ S2 -> *)
(*     G ⊢ T1 <: T2 *)

(** [[
G ⊢ p: q.type
G ⊢ q
_________________
G ⊢ T <: T[q/p, n]
]]
*)
| subtyp_sngl_pq : forall G p q T T' U,
    G ⊢ trm_path p : {{ q }} ->
    G ⊢ trm_path q : U ->
    repl_typ p q T T' ->
    G ⊢ T <: T'

(** [[
G ⊢ p: q.type
G ⊢ q
_________________
G ⊢ T <: T[p/q, n]
]]
*)
| subtyp_sngl_qp : forall G p q T T' U,
    G ⊢ trm_path p : {{ q }} ->
    G ⊢ trm_path q : U ->
    repl_typ q p T T' ->
    G ⊢ T <: T'

(** [[
G ⊢ p: {A: S..T}
_________________
G ⊢ S <: p.A
]]
*)
| subtyp_sel2: forall G p A S T,
    G ⊢ trm_path p : typ_rcd { A >: S <: T } ->
    G ⊢ S <: (p ↓ A)

(** [[
G ⊢ p: {A: S..T}
_________________
G ⊢ p.A <: T
]]
*)
| subtyp_sel1: forall G p A S T,
    G ⊢ trm_path p : typ_rcd  { A >: S <: T } ->
    G ⊢ p ↓ A <: T

(** [[
G ⊢ S2 <: S1
G, x: S2 ⊢ T1^x <: T2^x
x fresh
_________________
G ⊢ forall(S1)T1 <: forall(S2)T2
]]
*)
| subtyp_all : forall (L : fset var) (G : ctx) (S1 T1 S2 T2 : typ),
    G ⊢ S2 <: S1 ->
    (forall x : var, x \notin L -> G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2) ->
      G ⊢ ∀(S1) T1 <: ∀(S2) T2
where "G '⊢' T '<:' U" := (subtyp G T U).


(** ** Well-typed stores *)

(** The operational semantics is defined in terms of pairs [(s, t)], where
s] is a store (runtime environment) and [t] is a term.
    Given a typing [G ⊢ (s, t): T], [well_typed] establishes a correspondence
    between [G] and the store [s].

    We say that [s] is well-typed with respect to [G] if
    - [G = {(xi mapsto Ti) | i = 1, ..., n}]
    - [s = {(xi mapsto vi) | i = 1, ..., n}]
    - [G ⊢ vi: Ti].

    We say that [e] is well-typed with respect to [G], denoted as [s: G]. *)

Reserved Notation "γ '⫶' G" (at level 40).

Inductive well_typed: ctx -> sta -> Prop :=
| well_typed_empty: empty ⫶ empty
| well_typed_push: forall G γ x T v,
    γ ⫶ G ->
    x # G ->
    x # γ ->
    G ⊢ trm_val v : T ->
    γ & x ~ v ⫶ G & x ~ T
where "γ ⫶ G" := (well_typed G γ).

(** ** Infrastructure *)

Hint Constructors
     inert_typ inert record_has record_dec record_typ
     ty_trm ty_def ty_defs subtyp well_typed.

Hint Unfold record_type.

(** *** Mutual Induction Principles *)

Scheme typ_mut := Induction for typ Sort Prop
  with   dec_mut := Induction for dec Sort Prop.
Combined Scheme typ_mutind from typ_mut, dec_mut.

Scheme trm_mut  := Induction for trm  Sort Prop
  with   val_mut  := Induction for val Sort Prop
  with   def_mut  := Induction for def  Sort Prop
  with   defs_mut := Induction for defs Sort Prop
  with   defrhs_mut := Induction for def_rhs Sort Prop.
Combined Scheme trm_mutind from trm_mut, val_mut, def_mut, defs_mut, defrhs_mut.

Scheme ty_trm_mut    := Induction for ty_trm    Sort Prop
  with   ty_def_mut    := Induction for ty_def    Sort Prop
  with   ty_defs_mut   := Induction for ty_defs   Sort Prop.
Combined Scheme ty_mutind from ty_trm_mut, ty_def_mut, ty_defs_mut.

Scheme tds_ty_trm_mut  := Induction for ty_trm    Sort Prop
  with   tds_ty_def_mut  := Induction for ty_def    Sort Prop
  with   tds_ty_defs_mut := Induction for ty_defs   Sort Prop
  with   tds_subtyp      := Induction for subtyp    Sort Prop.
Combined Scheme tds_mutind from tds_ty_trm_mut, tds_ty_def_mut, tds_ty_defs_mut, tds_subtyp.

Scheme ts_ty_trm_mut  := Induction for ty_trm    Sort Prop
  with   ts_subtyp      := Induction for subtyp    Sort Prop.
Combined Scheme ts_mutind from ts_ty_trm_mut, ts_subtyp.

Scheme rules_trm_mut    := Induction for ty_trm    Sort Prop
  with   rules_def_mut    := Induction for ty_def    Sort Prop
  with   rules_defs_mut   := Induction for ty_defs   Sort Prop
  with   rules_subtyp     := Induction for subtyp    Sort Prop.
Combined Scheme rules_mutind from rules_trm_mut, rules_def_mut, rules_defs_mut, rules_subtyp.

Scheme rcd_dec_mut := Induction for record_dec Sort Prop
  with rcd_typ_mut := Induction for record_typ Sort Prop
  with inert_mut   := Induction for inert_typ Sort Prop.
Combined Scheme rcd_mutind from rcd_dec_mut, rcd_typ_mut, inert_mut.

Scheme repl_typ_mut := Induction for repl_typ Sort Prop
  with repl_dec_mut := Induction for repl_dec Sort Prop.
Combined Scheme repl_mutind from repl_typ_mut, repl_dec_mut.

Scheme ty_def_mut' := Induction for ty_def Sort Prop
  with ty_defs_mut' := Induction for ty_defs Sort Prop.
Combined Scheme ty_def_mutind from ty_def_mut', ty_defs_mut'.

(** *** Tactics *)

(** Tactics for generating fresh variables. *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars      => x         ) in
  let B := gather_vars_with (fun x : var       => \{ x }    ) in
  let C := gather_vars_with (fun x : ctx       => (dom x) \u (fv_ctx_types x)) in
  let D := gather_vars_with (fun x : sta        => dom x \u fv_sta_vals x) in
  let E := gather_vars_with (fun x : avar      => fv_avar  x) in
  let F := gather_vars_with (fun x : trm       => fv_trm   x) in
  let G := gather_vars_with (fun x : val       => fv_val   x) in
  let H := gather_vars_with (fun x : def       => fv_def   x) in
  let I := gather_vars_with (fun x : defs      => fv_defs  x) in
  let J := gather_vars_with (fun x : typ       => fv_typ   x) in
  let K := gather_vars_with (fun x : def_rhs   => fv_defrhs x) in
  let L := gather_vars_with (fun x : path     => fv_path x)
in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J \u K \u L).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Ltac fresh_constructor :=
  apply_fresh ty_new_intro as z ||
  apply_fresh ty_all_intro as z ||
  apply_fresh ty_let as z ||
  apply_fresh subtyp_all as z; auto.

(** Tactics for naming cases in case analysis. *)

Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.

(** Automatically destruct premises *)
Ltac destruct_all :=
  repeat match goal with
  | [ H : exists x, _ |- _ ]  => destruct H
  | [ H : ?A /\ ?B |- _ ] => destruct H
  | [ H : ?A \/ ?B |- _ ] => destruct H
         end.

Ltac destruct_notin :=
  repeat match goal with
         | [ H: ?z \notin ?E1 \u ?E2 |- _ ] =>
           apply notin_union in H; destruct H
         end.

Ltac solve_ex_typ_L :=
  match goal with
  | |- typ => exact typ_top
  | |- fset var => exact \{}
  end.
