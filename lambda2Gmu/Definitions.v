(***************************************************************************
* Lambda_{2G\mu} calculus formalisation
* Based on the paper Guarded Recursive Datatype Constructors by Xi et al.
***************************************************************************)

(**
The approach is inspired by Locally Nameless Representation
and it has been created by adapting and extending LN tutorials an a SystemFSub formalization from
https://www.chargueraud.org/viewcoq.php?sFile=softs%2Fln%2Fsrc%2FFsub_Definitions.v

Original tutorial was made by authors of:
  Engineering Formal LibLN
   B. Aydemir, A. Charguéraud, B. C. Pierce, R. Pollack and S. Weirich
   Symposium on Principles of Programming Languages (POPL), January 2008

and its follow-up journal version:

   The Locally Nameless Representation
   Arthur Charguéraud
   Journal of Automated Reasoning (JAR), 2011.

which also reused material prepared for the POPL'08 tutorial:

  "How to write your next POPL paper in Coq"
  organized by B. Aydemir, A. Bohannon, B. Pierce, J. Vaughan,
  D. Vytiniotis, S. Weirich, S. Zdancewic
*)

Set Implicit Arguments.
Require Import TLC.LibLN.
Require Import TLC.LibTactics.
Require Import List.
Require Import Coq.Init.Nat.
Require Import GMu.Zip.

Notation "[ ]*" := nil (format "[ ]*") : list_scope.
Notation "[ x ]*" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]*" :=  (cons z .. (cons y (cons x nil)) ..) : list_scope.
Notation "A |,| B" := (B ++ A) (at level 32, left associativity).
Notation "A |, b" := (b :: A) (at level 32).

Inductive DistinctList : list var -> Prop :=
| distinctive_empty : DistinctList []*
| distinctive_cons : forall h t, (~ List.In h t) -> DistinctList t -> DistinctList (t |, h).

(* GADTName is a separate syntactic category for identyfing GADT type names in opposition to variables and type variables. *)
Definition GADTName : Set := var.

(* See definition below.
We define a GADT in the env as a type with a list of constructors
Each constructor is thus identified by its base typename and its index on that list, instead of a regular name.
*)
Definition GADTConstructor : Set := (GADTName * nat).

(* We will maintain a separate set of DeBruijn indices - one for type variables and one for term variables
So a term Λa. λx: ∀α. Unit. x[a] will be translated to
Λ@. λ#: ∀@. Unit. #0[@0] where #0 at term-level refers to λ and @0 at typelevel refers to Λ
*)

(* pre-type-terms *)
Inductive typ : Set :=
(* bound type variables, identified by De Bruijn indices *)
| typ_bvar   : nat -> typ
(* free type variables (should be bound in an enclosing environment), identified by name - var *)
| typ_fvar   : var -> typ
(* unit type - 1*)
| typ_unit   : typ
(* tuple type - T ** U *)
| typ_tuple  : typ -> typ -> typ
(* function type - T ==> U *)
| typ_arrow  : typ -> typ -> typ
(* type abstraction - ∀. T *)
| typ_all  : typ -> typ
(* a GADT - [T1, ..., Tn] GT - T1 to Tn are its type arguments and GT is the GADTName *)
| typ_gadt  : (list typ) -> GADTName -> typ
.

Notation "T1 ==> T2" := (typ_arrow T1 T2) (at level 49, right associativity).
Notation "T1 ** T2" := (typ_tuple T1 T2) (at level 49).

(* An induction principle for pre-types that allows to correctly handle induction over type lists in GADTs *)
Section typ_ind'.
  Variable P : typ -> Prop.
  Hypothesis typ_bvar_case : forall (n : nat), P (typ_bvar n).
  Hypothesis typ_fvar_case : forall (x : var), P (typ_fvar x).
  Hypothesis typ_unit_case : P (typ_unit).
  Hypothesis typ_tuple_case : forall (t1 t2 : typ),
      P t1 -> P t2 -> P (typ_tuple t1 t2).
  Hypothesis typ_arrow_case : forall (t1 t2 : typ),
      P t1 -> P t2 -> P (typ_arrow t1 t2).
  Hypothesis typ_all_case : forall (t1 : typ),
      P t1 -> P (typ_all t1).
 Hypothesis typ_gadt_case : forall (ls : list typ) (n : GADTName),
      Forall P ls -> P (typ_gadt ls n).

  Fixpoint typ_ind' (t : typ) : P t :=
    let fix list_typ_ind (ls : list typ) : Forall P ls :=
        match ls return (Forall P ls) with
        | nil => Forall_nil P
        | cons t' rest =>
          let Pt : P t' := typ_ind' t' in
          let LPt : Forall P rest := list_typ_ind rest in
          (Forall_cons t' Pt LPt)
        end in
    match t with
    | typ_bvar i => typ_bvar_case i
    | typ_fvar x => typ_fvar_case x
    | typ_unit => typ_unit_case
    | typ_tuple t1 t2 => typ_tuple_case (typ_ind' t1) (typ_ind' t2)
    | typ_arrow t1 t2 => typ_arrow_case (typ_ind' t1) (typ_ind' t2)
    | typ_all t1 => typ_all_case (typ_ind' t1)
    | typ_gadt tparams name => typ_gadt_case name (list_typ_ind tparams)
    end.
End typ_ind'.

(*
To make examples more concrete we will be using the following GADT definition as an example:
enum Expr[A] {
   case LitInt(x: Int) extends Expr[Int]
   case LitStr(x: String) extends Expr[String]
   case Plus(p: (Expr[Int], Expr[Int])) extends Expr[Int]
   case Pair[X,Y](p: (Expr[X], Expr[Y])) extends Expr[(X, Y)]
}

or in Haskell:
data Expr a =
| LitInt : Int -> Expr Int
| LitStr : String -> Expr String
| Plus : Expr Int -> Expr Int -> Expr Int
| Pair : Expr x -> Expr y -> Expr (x * y)
*)

(*
I propose a simple rewrite of original syntax (it is described in more detail in documentation):
since we assume all matches are exhaustive, instead of specifying the GADT name in each branch and specifying which constructor we refer to,
we specify inside of the *match* which GADT we plan to match and then
each case corresponds to consecutive constructors:
i.e. first case matches first constructor, second one second etc.
Checking if the match is exhaustive in this form is as simple as checking
length cases = length constructors

Another thing to consider is that originally the clauses would look like this:
constructor[T1, T2, ..., Tm](x) => expr[where T1,... and x are bound]
as we use DeBruijn indices for bound variables, we do not use these names, so we can remove them
BUT we keep the length of the list of types to be bound, so the new form is following
case (constructor id is implicit from order) [M] => expr with 1 bound value variable and M bound type variables.
This M is then checked in typing if it is consistent with constructor arguments count.
We need to know M in syntax to make properties like 'closed type' not dependent on typing environment.
It is quite expected, since we also have this information in the original syntax (the length of list of type variables to bind).

Overall, an expression
case e of
| c1[T1,...Tm1](x1) => e1
| ...
| cn[Tn,...Tmn](xn) => en
where c1, ..., cn are constructors of type TG (as explained in other notes, we do not allow matches that mix types)

becomes
case e matching TG of
| [m1] => e1'
| ...
| [mn] => en'

where ei' := ei[ T1 -> @0, ..., Tm -> @(m-1), xi -> #0 ]
 *)

(* kinds of variables *)
Inductive var_kind : Set :=
| lam_var (* variables bound by lambda expressions and pattern match clauses *)
| fix_var. (* variables bound by the fixpoint combinator *)

(* pre-terms *)
Inductive trm : Set :=
(* bound variables, identified by De Bruijn indices *)
| trm_bvar : nat -> trm (* bound variables do not need their kind stored, because it is implied by what term its De Bruijn index points to (as they always exist in a context of some binder in well formed terms) *)
(* free variables (should be bound in an enclosing environment), identified by name - var *)
| trm_fvar : var_kind -> var -> trm
(* GADT constructor application
   it creates an instance of the GADT type by applying a list of types and a term to the constructor
   C [T1, ..., Tn] e
   where
   C is the name of the constructor, in our case a tuple of (GADTName, constructor id)
   (but in the examples we will use names of constructors instead of these numeric identifiers, for readability)
   T1, ..., Tn are the types applied to the constructor

   the types T1, ..., Tn will determine the types of the resulting GADT type but are not necessarily equal to it
   for example, we can create a pair of int and string literals as follows:
   Pair[Int, String]((LitInt(42), LitString("foo"))) : Expr[(Int, String)]
   or in our language
   let p1 : [Int] Expr = LitInt[] 42 in -- here LitInt has an empty list of constructor type parameters and that uniquely identifies that the resulting GADT has exactly one type parameter equal to Int
   let p2 : [String] Expr = LitStr[] "foo" in
   let p : [Int] Expr ** [String] Expr = <p1, p2> in
   Pair[Int, String] p : [Int ** String] Expr
   -- and here we apply two type parameters to the constructor - Int and String and the proper value and as a result we get an instance of Expr GADT with a single type parameter that is a tuple Int ** String
*)
| trm_constructor : (list typ) -> GADTConstructor -> trm -> trm
(* the only value of type unit - <> *)
| trm_unit : trm
(* creates a tuple - <t1, t2> *)
| trm_tuple : trm -> trm -> trm
(* gets the first element from the tuple - fst <t1, t2> = t1 *)
| trm_fst : trm -> trm
(* gets the second element from the tuple - snd <t1, t2> = t2 *)
| trm_snd : trm -> trm
(* lambda abstraction - λ#: T. e * where in e the first De Bruijn index #0 is bound to the variable of type T introduced by this lambda *)
| trm_abs  : typ -> trm -> trm
(* function application *)
| trm_app  : trm -> trm -> trm
(* type abstraction - Λ@. e where in e the first type-level De Bruij index @0 is bound to a type variable introduced by this abstraction *)
| trm_tabs : trm -> trm
(* type application, (Λ@. e) [T] will yield e in which the index @0 has been replaced by T *)
| trm_tapp : trm -> typ -> trm
(* the fixpoint operator - fix #: T. e
can be used for recursion, for example
fix #: 1 ==> 1. λ#: 1. @1 @0
which is equivalent to
fix f: 1 ==> 1. λx: 1. f x which creates a function that once applied to an unit will loop
 *)
| trm_fix : typ -> trm -> trm
(* | trm_matchunit *)
(* | trm_matchtuple ( these two add nothing interesting, so they were removed) *)
(* pattern matching over a GADT
   the syntactic changes have been explained above, so now I will just include an example:
   let's write an eval function:
   def eval[A](e: Expr[A]): A = e match {
       case LitInt(i) => i
       case LitStr(s) => s
       case Plus(p) => eval[Int](p._1) + eval[Int](p._2)
       case Pair[X,Y](p) =>
            val x = eval[X](p._1)
            val y = eval[Y](p._2)
            (x, y)
   }

   which in our language will be:
   eval e = match e of type Expr with
   | LitInt[](i) => i
   | LitStr[](s) => s
   | Plus[](p) => eval[Int](fst p) + eval[Int](snd p)
   | Pair[X, Y](p) => <eval[X](fst p), eval[Y](snd p)>

which will become the following when we replace names with order of clauses:
   eval e = match e of type Expr with
   | [0] => #0
   | [0] => #0
   | [0] => eval[Int](fst #0) + eval[Int](snd #0)
   | [2] => <eval[@1](fst #0), eval[@0](snd #0)>
as we can see in the new formulation each clause consists of just two things -
  the expression on the right and the number indicating how many type variables are bound in that expression
the name of the constructor is inferred from its position in the match (so first constructor is the first ctor from definition, LitInt etc.)
the names of type parameters are consecutive type-level DeBruijn indices @0, @1, ... up to the arity indicated in the clause
the name of the variable is just #0

Actually, the arity of the constructor could theoretically be skipped because it can be inferred unambigously form Σ, but we want simple syntactic operations like type opening to work without knowing the actual environment, thus we wanted to preserve this information.

Another note is that this changed syntax **does not add** anything new:
as soon as we assume exhaustivity, that is equivalent to the original syntax
- the constructor arities are determined by the amount of type variables bound in the original syntax
- the name/identifier of the GADT that is matched is also unambiguous, because a well-formed match will contain constructors only belonging to a single GADT (otherwise it would fail to typecheck) and so we can just check which GADT the first constructor name belongs to.
The only difference is that the new syntax is a bit more 'strict' - it will reject some ill-typed programs that the old syntax would accept (but it is equivalent on well-typed programs). That seems to be a very minor change, especially as the check of pattern match constructor homogenity is very simple.
*)
| trm_matchgadt : trm -> GADTName -> (list Clause) -> trm
(* let # = e1 in e2 makes e1 bound to #0 in e2, equivalent of let x = e1 in e2 *)
| trm_let : trm -> trm -> trm
with
  Clause : Set :=
  (* pattern match clause, see above *)
| clause (clArity : nat) (e : trm)
.

(* A helper function to extract arity of a clause - i.e. the amount of type variables that are bound in its term. *)
Definition clauseArity (c : Clause) : nat :=
  match c with
  | clause n _ => n
  end.

(* A helper function to extract the clause's term. *)
Definition clauseTerm (c : Clause) : trm :=
  match c with
  | clause _ t => t
  end.

(* An induction principle for terms that allows correctly handle induction over the list of clauses *)
Section trm_ind'.
  Variable P : trm -> Prop.
  Hypothesis trm_bvar_case : forall (n : nat), P (trm_bvar n).
  Hypothesis trm_fvar_case : forall (k : var_kind) (x : var), P (trm_fvar k x).
  Hypothesis trm_constructor_case : forall (e : trm) (Ts : list typ) (GADTC : GADTConstructor),
      P e -> P (trm_constructor Ts GADTC e).
  Hypothesis trm_unit_case : P (trm_unit).
  Hypothesis trm_tuple_case : forall (t1 t2 : trm),
      P t1 -> P t2 -> P (trm_tuple t1 t2).
  Hypothesis trm_fst_case : forall (e : trm),
      P e -> P (trm_fst e).
  Hypothesis trm_snd_case : forall (e : trm),
      P e -> P (trm_snd e).
  Hypothesis trm_abs_case : forall T (e : trm),
      P e -> P (trm_abs T e).
  Hypothesis trm_app_case : forall (t1 t2 : trm),
      P t1 -> P t2 -> P (trm_app t1 t2).
  Hypothesis trm_tabs_case : forall (e : trm),
      P e -> P (trm_tabs e).
  Hypothesis trm_tapp_case : forall (e : trm) T,
      P e -> P (trm_tapp e T).
  Hypothesis trm_fix_case : forall (e : trm) T,
      P e -> P (trm_fix T e).
  Hypothesis trm_match_case : forall (clauses : list Clause) (G : GADTName) (e : trm),
      P e ->
      (* (forall TN e', In (clause TN e') ls -> P e') -> *)
      Forall (fun c => P (clauseTerm c)) clauses ->
      P (trm_matchgadt e G clauses).
  Hypothesis trm_let_case : forall (t1 t2 : trm),
      P t1 -> P t2 -> P (trm_let t1 t2).

  Fixpoint trm_ind' (t : trm) : P t :=
    let fix list_clause_ind (clauses : list Clause) : Forall (fun c => P (clauseTerm c)) clauses :=
        match clauses return (Forall (fun c => P (clauseTerm c)) clauses) with
        | nil => Forall_nil (fun c => P (clauseTerm c))
        | cons c rest =>
          let head_proof : P (clauseTerm c) := trm_ind' (clauseTerm c) in
          let tail_proof : Forall (fun c => P (clauseTerm c)) rest := list_clause_ind rest in
          (Forall_cons c head_proof tail_proof)
        end in
    match t with
  | trm_bvar i    => trm_bvar_case i
  | trm_fvar k x    => trm_fvar_case k x
  | trm_constructor tparams C t => trm_constructor_case tparams C (trm_ind' t)
  | trm_unit => trm_unit_case
  | trm_tuple e1 e2 => trm_tuple_case (trm_ind' e1) (trm_ind' e2)
  | trm_fst e => trm_fst_case (trm_ind' e)
  | trm_snd e => trm_snd_case (trm_ind' e)
  | trm_abs T e => trm_abs_case T (trm_ind' e)
  | trm_app e1 e2 => trm_app_case (trm_ind' e1) (trm_ind' e2)
  | trm_tabs e => trm_tabs_case (trm_ind' e)
  | trm_tapp e T => trm_tapp_case T (trm_ind' e)
  | trm_fix T e => trm_fix_case T (trm_ind' e)
  | trm_matchgadt e G clauses => trm_match_case G (trm_ind' e) (list_clause_ind clauses)
  | trm_let e1 e2 => trm_let_case (trm_ind' e1) (trm_ind' e2)
    end.
End trm_ind'.

Fixpoint sum (ls : list nat) : nat :=
  match ls with
    | nil => O
    | cons h t => plus h (sum t)
  end.

Fixpoint typ_size (t : typ) : nat :=
  (* let fix typlist_size (ts : list typ) : nat := *)
  (*   match ts with *)
  (*   | nil => 0 *)
  (*   | cons h t => typ_size h + typlist_size t *)
  (*   end in *)
  match t with
  | typ_bvar i => 1
  | typ_fvar x => 1
  | typ_unit => 1
  | typ_tuple t1 t2 => 1 + typ_size t1 + typ_size t2
  | typ_arrow t1 t2 => 1 + typ_size t1 + typ_size t2
  | typ_all t1 => 1 + typ_size t1
  | typ_gadt tparams name => 1 + (sum (map typ_size tparams))
    (*)1 + typlist_size tparams*)
  end
.

(* Fixpoint typlist_size (ts : list typ) : nat := *)
(*   match ts with *)
(*   | nil => 0 *)
(*   | cons h t => typ_size h + typlist_size t *)
(*   end. *)

Definition map_clause_trms {A : Type} (f : trm -> A) (cs : list Clause) : list A :=
  map (fun c => f (clauseTerm c)) cs.

Definition map_clause_trm_trm (f : trm -> trm) (cs : list Clause) : list Clause :=
  map (fun c => match c with
             | clause n e => clause n (f e)
             end) cs.

Fixpoint trm_size (e : trm) : nat :=
  match e with
  | trm_bvar i    => 1
  | trm_fvar _ x    => 1
  | trm_constructor tparams C e1 => 1 + trm_size e1
  | trm_unit => 1
  | trm_tuple e1 e2 => 1 + trm_size e1 + trm_size e2
  | trm_fst e1 => 1 + trm_size e1
  | trm_snd e1 => 1 + trm_size e1
  | trm_abs T e1    => 1 + trm_size e1
  | trm_app e1 e2 => 1 + trm_size e1 + trm_size e2
  | trm_tabs e1 => 1 + trm_size e1
  | trm_tapp e1 T => 1 + trm_size e1
  | trm_fix T e1 => 1 + trm_size e1
  | trm_matchgadt e G cs => trm_size e + sum (map_clause_trms trm_size cs)
  | trm_let e1 e2 => 1 + trm_size e1 + trm_size e2
  end.

(** ** Opening *)

(** Opening replaces an index with a term. It corresponds to informal
    substitution for a bound variable, such as in the rule for beta
    reduction. Note that only "dangling" indices (those that do not
    refer to any abstraction) can be opened. Opening has no effect for
    terms that are locally closed.

    Natural numbers are just an inductive datatype with two
    constructors: O and S, defined in Coq.Init.Datatypes.

    We make several simplifying assumptions in defining [open_rec].
    First, we assume that the argument [u] is locally closed.  This
    assumption simplifies the implementation since we do not need to
    shift indices in [u] when passing under a binder.  Second, we
    assume that this function is initially called with index zero and
    that zero is the only unbound index in the term.  This eliminates
    the need to possibly subtract one in the case of indices.

    There is no need to worry about variable capture because bound
    variables are indices.
 *)

Fixpoint open_tt_rec (k : nat) (u : typ) (t : typ) {struct t} : typ :=
  match t with
  (* | typ_bvar i => If (k < i) then (typ_bvar (i - 1)) else If k = i then u else (typ_bvar i) *)
  | typ_bvar i => match Nat.compare k i with
                 | Lt => typ_bvar (i-1)
                 | Eq => u
                 | Gt => typ_bvar i
                 end
  (*                                       (* We only decrement type variables though as values are substituted one by one only *) *)
  | typ_fvar x => typ_fvar x
  | typ_unit => typ_unit
  | typ_tuple t1 t2 => typ_tuple (open_tt_rec k u t1) (open_tt_rec k u t2)
  | typ_arrow t1 t2 => typ_arrow (open_tt_rec k u t1) (open_tt_rec k u t2)
  | typ_all t1 => typ_all (open_tt_rec (S k) u t1)
  | typ_gadt tparams name => typ_gadt (map (open_tt_rec k u) tparams) name
end.

Definition open_typlist_rec k u (ts : list typ) : list typ := map (open_tt_rec k u) ts.

Fixpoint open_te_rec (k : nat) (u : typ) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => trm_bvar i
  | trm_fvar vk x    => trm_fvar vk x
  | trm_constructor tparams C e1 => trm_constructor (open_typlist_rec k u tparams) C (open_te_rec k u e1)
  | trm_unit => trm_unit
  | trm_tuple e1 e2 => trm_tuple (open_te_rec k u e1) (open_te_rec k u e2)
  | trm_fst e1 => trm_fst (open_te_rec k u e1)
  | trm_snd e1 => trm_snd (open_te_rec k u e1)
  | trm_abs T e1    => trm_abs (open_tt_rec k u T) (open_te_rec k u e1)
  | trm_app e1 e2 => trm_app (open_te_rec k u e1) (open_te_rec k u e2)
  | trm_tabs e1 => trm_tabs (open_te_rec (S k) u e1)
  | trm_tapp e1 T => trm_tapp (open_te_rec k u e1) (open_tt_rec k u T)
  | trm_fix T e1 => trm_fix (open_tt_rec k u T) (open_te_rec k u e1)
  | trm_matchgadt e1 G cs =>
    (* each clause binds n type variables *)
    trm_matchgadt (open_te_rec k u e1) G
                  (map (fun c => match c with clause n e => clause n (open_te_rec (k + n) u e) end) cs)
  | trm_let e1 e2 => trm_let (open_te_rec k u e1) (open_te_rec k u e2)
  end.

Fixpoint open_ee_rec (k : nat) (u : trm) (e : trm) {struct e} : trm :=
  match e with
  (* | trm_bvar i    => If k = i then u else (trm_bvar i) *)
  | trm_bvar i    => if (k =? i) then u else (trm_bvar i)
  | trm_fvar vk x    => trm_fvar vk x
  | trm_constructor tparams C e1 => trm_constructor tparams C (open_ee_rec k u e1)
  | trm_unit => trm_unit
  | trm_tuple e1 e2 => trm_tuple (open_ee_rec k u e1) (open_ee_rec k u e2)
  | trm_fst e1 => trm_fst (open_ee_rec k u e1)
  | trm_snd e1 => trm_snd (open_ee_rec k u e1)
  | trm_abs T e1    => trm_abs T (open_ee_rec (S k) u e1)
  | trm_app e1 e2 => trm_app (open_ee_rec k u e1) (open_ee_rec k u e2)
  | trm_tabs e1 => trm_tabs (open_ee_rec k u e1)
  | trm_tapp e1 T => trm_tapp (open_ee_rec k u e1) T
  | trm_fix T e1 => trm_fix T (open_ee_rec (S k) u e1)
  | trm_matchgadt e1 G cs =>
    (* each clause binds 1 value variable *)
    trm_matchgadt (open_ee_rec k u e1) G
                  (map (fun c => match c with clause n e => clause n (open_ee_rec (S k) u e) end) cs)
  | trm_let e1 e2 => trm_let (open_ee_rec k u e1) (open_ee_rec (S k) u e2)
  end.

(** Many common applications of opening replace index zero with an
    expression or variable.  The following definition provides a
    convenient shorthand for such uses.  Note that the order of
    arguments is switched relative to the definition above.  For
    example, [(open e x)] can be read as "substitute the variable [x]
    for index [0] in [e]" and "open [e] with the variable [x]."
    Recall that the coercions above let us write [x] in place of
    [(fvar x)].
*)
Definition open_tt T U := open_tt_rec 0 U T.
Definition open_te t U := open_te_rec 0 U t.
Definition open_ee t u := open_ee_rec 0 u t.

(* (** We define notations for [open_rec] and [open]. *) *)

(* Notation "{ k ~> u } t" := (open_rec k u t) (at level 67). *)
(* Notation "t ^^ u" := (open t u) (at level 67). *)

(* (** We also define a notation for the specialization of [open] to *)
(*     the case where the argument is a free variable. This notation *)
(*     is not needed when [trm_fvar] is declared as a coercion like *)
(*     we do in this tutorial, but it is very handy when we don't want *)
(*     to have such a coercion. (Coercions are very convenient for *)
(*     simple developments, but they can make things very obscur when *)
(*     it comes to scaling up to larger developments.)  *) *)

(* Notation "t ^ x" := (open t (trm_fvar x)). *)

Notation "T 'open_tt_var' X" := (open_tt T (typ_fvar X)) (at level 67).
Notation "t 'open_te_var' X" := (open_te t (typ_fvar X)) (at level 67).
Notation "t 'open_ee_varlam' x" := (open_ee t (trm_fvar lam_var x)) (at level 67).
Notation "t 'open_ee_varfix' x" := (open_ee t (trm_fvar fix_var x)) (at level 67).

(* Definition open_tt_many (args : list typ) (T : typ) := fold_left open_tt args T. *)
(* Definition open_tt_many_var (args : list var) (T : typ) := fold_left (fun typ v => open_tt typ (typ_fvar v)) args T. *)

Fixpoint open_tt_many (args : list typ) (T : typ) :=
  match args with
  | ha :: ta => open_tt_many ta (open_tt T ha)
  | []* => T
  end.

Fixpoint open_te_many (args : list typ) (e : trm) :=
  match args with
  | ha :: ta => open_te_many ta (open_te e ha)
  | []* => e
  end.

Definition open_tt_many_var (args : list var) (T : typ) := open_tt_many (map typ_fvar args) T.

Definition open_te_many_var (args : list var) (e : trm) := open_te_many (map typ_fvar args) e.

(** * Free Variables *)
(* Free variables are the fvars which should be bound in some enclosing environments.
   As De Bruijn indices are used only for bound variables and a correct type/term must have all De Bruijn indices bound, only the fvars can contribute to free variables *)
(*
When computing free variables we mix-up term and type variables.
This may seem erroneous at first, but it is not a problem.
First we could imagine that the used variables come from different universes and can always be distinguished.
But an even easier explanation is:
we use the free variables solely for the purpose of instantiating new fresh variables that do not conflict with anything else
if we instantiate a fresh type variable, if it is fresh from some value-variables, it is not a problem.
Yes, it could never collide with them anyway, but if it is even 'more fresh' that does not introduce any issues.
*)

Fixpoint fv_typ (T : typ) {struct T} : vars :=
  match T with
  | typ_bvar J => \{}
  | typ_fvar X => \{X}
  | typ_unit   => \{}
  | T1 ** T2   => fv_typ T1 \u fv_typ T2
  | T1 ==> T2   => fv_typ T1 \u fv_typ T2
  | typ_all T1 => fv_typ T1
  | typ_gadt Ts _ => fold_left (fun fv T => fv \u fv_typ T) Ts \{}
  end.

Fixpoint fv_typs (Ts : list typ) : fset var :=
  match Ts with
  | nil => \{}
  | cons Th Tts => fv_typ Th \u fv_typs Tts
  end.

Lemma fv_typs_migration : forall Ts Z,
    fv_typs Ts \u Z =
    fold_left (fun fv T => fv \u fv_typ T) Ts Z.
Proof.
  induction Ts; introv; cbn.
  - rewrite* union_empty_l.
  - rewrite <- IHTs.
    rewrite (union_comm (fv_typ a) (fv_typs Ts)).
    rewrite <- union_assoc.
    rewrite (union_comm (fv_typ a) Z).
    auto.
Qed.

Fixpoint fv_trm (e : trm) {struct e} : vars :=
  match e with
  | trm_bvar i => \{}
  | trm_fvar _ x => \{x}
  | trm_unit   => \{}
  | trm_tuple e1 e2 => fv_trm e1 \u fv_trm e2
  | trm_fst e1 => fv_trm e1
  | trm_snd e1 => fv_trm e1
  | trm_abs T1 e1 => fv_typ T1 \u fv_trm e1
  | trm_app e1 e2 => fv_trm e1 \u fv_trm e2
  | trm_tabs e1 => fv_trm e1
  | trm_tapp e1 T1 => fv_typ T1 \u fv_trm e1
  | trm_fix T1 e1 => fv_typ T1 \u fv_trm e1
  | trm_let e1 e2 => fv_trm e1 \u fv_trm e2
  | trm_matchgadt e _ cs =>
    fold_left (fun fv c => fv \u fv_trm (clauseTerm c)) cs (fv_trm e)
  | trm_constructor Ts _ e1 =>
    fold_left (fun fv T => fv \u fv_typ T) Ts (fv_trm e1)
  end.


(** * Closed types and terms; and values *)

(* A type or term is closed if all its De Bruijn indices are bound. It may still contain free variables in terms of fvars. *)

Inductive type : typ -> Prop :=
  | type_var : forall X,
      type (typ_fvar X)
  | type_unit :
      type typ_unit
  | type_tuple : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_tuple T1 T2)
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow T1 T2)
  | type_all : forall L T2,
      (forall X, X \notin L -> type (T2 open_tt_var X)) ->
      type (typ_all T2) (* type (typ_all @0) <- type (X) *)
  | type_gadt : forall Tparams Name,
      (forall Tparam, In Tparam Tparams -> type Tparam) ->
       type (typ_gadt Tparams Name)
.

Inductive term : trm -> Prop :=
| term_var : forall vk x,
    term (trm_fvar vk x)
| term_constructor : forall Tparams Name e1,
    term e1 ->
    (forall Tparam, In Tparam Tparams -> type Tparam) ->
    term (trm_constructor Tparams Name e1)
| term_unit : term trm_unit
| term_tuple : forall e1 e2,
    term e1 ->
    term e2 ->
    term (trm_tuple e1 e2)
| term_fst : forall e1,
    term e1 ->
    term (trm_fst e1)
| term_snd : forall e1,
    term e1 ->
    term (trm_snd e1)
| term_abs : forall L V e1,
    type V ->
    (forall x, x \notin L -> term (e1 open_ee_varlam x)) ->
    term (trm_abs V e1)
| term_app : forall e1 e2,
    term e1 ->
    term e2 ->
    term (trm_app e1 e2)
| term_tabs : forall L e1,
    (forall X, X \notin L -> term (e1 open_te_var X)) ->
    (forall X, X \notin L -> value (e1 open_te_var X)) -> (* this has be separated to make some induction proofs work. we may consider completely splitting the values requirements to a separate property *)
    term (trm_tabs e1)
| term_tapp : forall v1 V,
    term v1 ->
    type V ->
    term (trm_tapp v1 V)
| term_fix : forall L T v1,
    type T ->
    (forall x, x \notin L -> term (v1 open_ee_varfix x)) ->
    (forall x, x \notin L -> value (v1 open_ee_varfix x)) -> (* this has be separated to make some induction proofs work. we may consider completely splitting the values requirements to a separate property *)
    term (trm_fix T v1)
| term_let : forall L e1 e2,
    term e1 ->
    (forall x, x \notin L -> term (e2 open_ee_varlam x)) ->
    term (trm_let e1 e2)
| term_matchgadt : forall L e1 G ms,
    term e1 ->
    (forall cl, In cl ms ->
           forall Alphas x,
             length Alphas = clauseArity cl ->
             DistinctList Alphas ->
             (forall A, In A Alphas -> A \notin L) ->
             x \notin L ->
             x \notin from_list Alphas ->
           term ((open_te_many_var Alphas (clauseTerm cl)) open_ee_varlam x)
    ) ->
    term (trm_matchgadt e1 G ms)
with
value : trm -> Prop :=
| value_abs : forall V e1, term (trm_abs V e1) ->
                      value (trm_abs V e1)
| value_tabs : forall e1, term (trm_tabs e1) ->
                     value (trm_tabs e1)
| value_unit : value (trm_unit)
| value_lamvar : forall x, value (trm_fvar lam_var x)
| value_tuple : forall e1 e2,
    value e1 ->
    value e2 ->
    value (trm_tuple e1 e2)
| value_gadt : forall Tparams Name e1,
    term (trm_constructor Tparams Name e1) ->
    value e1 ->
    value (trm_constructor Tparams Name e1)
.

(*


f : T → ∀α. T
f = λx : T. Λα. x - valid but we cannot encode it
but we can do
f' : T → ∀α. Unit → T
f' = λx : T. Λα. λignored: Unit. x

and instead of applying (f x)[U]
we would apply ((f x)[U]) <> to get the result
 *)

(** * GADT Environment definition *)
Record GADTConstructorDef : Set :=
  (* a constructor of type ∀(α...). τ → (β...) T)
     arity specifies how many type parameters (α) there are, they are referred to inside the types by DeBruijn indices
     τ is the type of argument (one arg only, use tuples for more; it can refer to α)
     β are the instantiated type parameters of the returned GADT type (they can refer to α) - βs are represented by rettypes
     T is the base GADT type name that is returned by this constructor, it is not included in the constructor definition as it is implicit from where this definition is
   *)
  mkGADTconstructor {
      Carity : nat;
      Cargtype : typ;
      Crettypes : list typ
    }.

Record GADTDef : Set :=
  mkGADT {
      Tarity : nat;
      Tconstructors : list GADTConstructorDef
    }.

(* This env is the signature of the available GADT types, it is Σ in the paper *)
Definition GADTEnv := env GADTDef.
(*
Some raw ideas:
- we will need to easily find the constructor signature by name
- GADT type name is contained (implicitly) in the signature

- we could refactor the syntax definition so that everywhere we use a constructor name c, we instead refer to it by T.c where T is the GADT name, this will make checking exhaustivity easier
-- then we could rename constructors of a type T to just numbers, so that first constructor is called T.0, second T.1 etc. this will make things even simpler
--- we could then even require the pattern match to preserve order of constructors (not sure if this helps with anything though, but probably with exhaustivity)
*)

(** * Context *)

Inductive bind : Set :=
| bind_var : var_kind -> typ -> bind.

Notation "x ~f T" := (x ~ bind_var fix_var T) (at level 27, left associativity).
Notation "x ~l T" := (x ~ bind_var lam_var T) (at level 27, left associativity).

Unset Implicit Arguments.
(* The context Γ mapping variables to their types *)
Definition ctx := env bind.

(** * Substitution *)

Fixpoint subst_tt (Z : var) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_bvar J => typ_bvar J
  (* | typ_fvar X => If X = Z then U else (typ_fvar X) *)
  | typ_fvar X => If X = Z then U else (typ_fvar X)
  | typ_unit   => typ_unit
  | T1 ** T2   => subst_tt Z U T1 ** subst_tt Z U T2
  | T1 ==> T2   => subst_tt Z U T1 ==> subst_tt Z U T2
  | typ_all T1 => typ_all (subst_tt Z U T1)
  | typ_gadt Ts Name => typ_gadt (map (subst_tt Z U) Ts) Name
end.

Fixpoint subst_te (Z : var) (U : typ) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i => trm_bvar i
  | trm_fvar vk x => trm_fvar vk x
  | trm_unit   => trm_unit
  | trm_tuple e1 e2 => trm_tuple (subst_te Z U e1) (subst_te Z U e2)
  | trm_fst e1 => trm_fst (subst_te Z U e1)
  | trm_snd e1 => trm_snd (subst_te Z U e1)
  | trm_abs T1 e1 => trm_abs (subst_tt Z U T1) (subst_te Z U e1)
  | trm_app e1 e2 => trm_app (subst_te Z U e1) (subst_te Z U e2)
  | trm_tabs e1 => trm_tabs (subst_te Z U e1)
  | trm_tapp e1 T1 => trm_tapp (subst_te Z U e1) (subst_tt Z U T1)
  | trm_fix T1 e1 => trm_fix (subst_tt Z U T1) (subst_te Z U e1)
  | trm_let e1 e2 => trm_let (subst_te Z U e1) (subst_te Z U e2)
  | trm_matchgadt e G cs =>
    trm_matchgadt (subst_te Z U e) G (map_clause_trm_trm (subst_te Z U) cs)
  | trm_constructor Ts N e1 => trm_constructor (map (subst_tt Z U) Ts) N (subst_te Z U e1)
  end.

Fixpoint subst_ee (z : var) (k : var_kind) (u : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i => trm_bvar i
  | trm_fvar vk x => If x = z /\ vk = k then u else (trm_fvar vk x)
  | trm_unit   => trm_unit
  | trm_tuple e1 e2 => trm_tuple (subst_ee z k u e1) (subst_ee z k u e2)
  | trm_fst e1 => trm_fst (subst_ee z k u e1)
  | trm_snd e1 => trm_snd (subst_ee z k u e1)
  | trm_abs T1 e1 => trm_abs T1 (subst_ee z k u e1)
  | trm_app e1 e2 => trm_app (subst_ee z k u e1) (subst_ee z k u e2)
  | trm_tabs e1 => trm_tabs (subst_ee z k u e1)
  | trm_tapp e1 T1 => trm_tapp (subst_ee z k u e1) T1
  | trm_fix T1 e1 => trm_fix T1 (subst_ee z k u e1)
  | trm_let e1 e2 => trm_let (subst_ee z k u e1) (subst_ee z k u e2)
  | trm_matchgadt e G cs =>
    trm_matchgadt (subst_ee z k u e) G (map_clause_trm_trm (subst_ee z k u) cs)
  | trm_constructor Ts N e1 => trm_constructor Ts N (subst_ee z k u e1)
  end.

Definition subst_tb (Z : var) (P : typ) (b : bind) : bind :=
  match b with
  (* | bind_typ => bind_typ *)
  | bind_var vk T => bind_var vk (subst_tt Z P T)
  end.

Fixpoint subst_tt_many (Xs : list var) (Us : list typ) (T : typ) :=
  match (Xs, Us) with
  (* | ((List.cons X Xt), (List.cons U Ut)) => subst_tt X U (subst_tt_many Xt Ut T) *)
  | ((List.cons X Xt), (List.cons U Ut)) => subst_tt_many Xt Ut (subst_tt X U T)
  | _ => T
  end.

(* Fixpoint subst_tb_many (As : list var) (Us : list typ) (b : bind) : bind := *)
(*   match (As, Us) with *)
(*   | (List.cons Ah At, List.cons Uh Ut) => subst_tb_many At Ut (subst_tb Ah Uh b) *)
(*   | _ => b *)
(*   end. *)
Definition subst_tb_many (As : list var) (Ps : list typ) (b : bind) : bind :=
  match b with
  | bind_var vk T => bind_var vk (subst_tt_many As Ps T)
  end.


(* In pDOT there is no such notion as a type is well formed if it is used in a typing judgement.
But this language requires it, because like in System F we have type-abstractions and type-applications.
In type-application we need a way to ensure that the type is well-formed.
In pDOT type-abstraction is handled by dependent typing and type-application is implemented by applying a term containing a type-member, so we get its well-formedness from the fact that the term containing this type is well-typed.
But in this calculus we apply 'naked' types, so there are no typing judgements for them, so we need a separate notion.
 *)

Definition substitution := list (var * typ).
Definition substitution_sources (Θ : substitution) : fset var := from_list (map fst Θ).

Inductive type_equation : Set := mk_type_equation (T U : typ).

Notation "T ≡ U" := (mk_type_equation T U) (at level 30).

Inductive typctx_elem : Set :=
| tc_var (A : var)
| tc_eq (eq : type_equation).

(* Type context Δ
   it contains available type variables and type equations that should hold *)
(* we keep the elements in reverse order, i.e. the head is the last added element *)
Definition typctx := list typctx_elem.
Definition is_var_defined (Δ : typctx) (X : var) : Prop := In (tc_var X) Δ.
(* Definition add_var (Δ : typctx) (X : var) : typctx := tc_var X :: Δ. *)
(* Definition add_eq (Δ : typctx) (eq : type_equation) : typctx := tc_eq eq :: Δ. *)
Definition emptyΔ : typctx := []*.

Fixpoint domΔ (Δ : typctx) : fset var :=
  match Δ with
  | []* => \{}
  | tc_var A :: r => \{ A } \u domΔ r
  | tc_eq _ :: r => domΔ r
  end.
Fixpoint fv_delta (Δ : typctx) : fset var :=
  match Δ with
  | []* => \{}
  | tc_var A :: r => fv_delta r
  | tc_eq (T1 ≡ T2) :: r => fv_typ T1 \u fv_typ T2 \u fv_delta r
  end.

Definition fv_env (E : ctx) : fset var :=
  List.fold_right (fun p acc => match snd p with bind_var _ T => fv_typ T \u acc end) \{} E.

(** * Well-formed types *)
(* A type is well formed if:
- it is closed
- all its type variables are present in the environment Δ
- if it is a GADT type, its name is present in the environment Σ and its amount of type parameters is the same as arity of that GADT

In the paper that is noted as Δ ⊢ T : *
(Σ is always implicit in the paper)
*)
Inductive wft : GADTEnv -> typctx -> typ -> Prop :=
| wft_unit : forall Σ Δ,
    wft Σ Δ typ_unit
| wft_var : forall Σ Δ X,
    is_var_defined Δ X ->
    wft Σ Δ (typ_fvar X)
| wft_arrow : forall Σ Δ T1 T2,
    wft Σ Δ  T1 ->
    wft Σ Δ T2 ->
    wft Σ Δ (typ_arrow T1 T2)
| wft_tuple : forall Σ Δ T1 T2,
    wft Σ Δ T1 ->
    wft Σ Δ T2 ->
    wft Σ Δ (typ_tuple T1 T2)
| wft_all : forall (L : fset var) Σ Δ T2,
    (forall X, X \notin L ->
          wft Σ (Δ |,| [tc_var X]*) (T2 open_tt_var X)) ->
    wft Σ Δ (typ_all T2)
| wft_gadt : forall Σ Δ Tparams Name Arity Defs,
    (forall T, In T Tparams -> wft Σ Δ T) ->
    binds Name (mkGADT Arity Defs) Σ ->
    length Tparams = Arity ->
    wft Σ Δ (typ_gadt Tparams Name)
.

(*Thanks to usage of de Bruijn indices, alpha equivalence reduces to plain equivalence *)
(* Definition alpha_equivalent (T U : typ) : Prop := T = U. *)

Fixpoint subst_tt' (T : typ) (Θ : substitution) :=
  match Θ with
  | nil => T
  | (A, U) :: Θ' => subst_tt' (subst_tt A U T) Θ'
  end.

(* Fixpoint subst_tt' (T : typ) (Θ : substitution) : typ := *)
(*   match T with *)
(*   | typ_bvar J => typ_bvar J *)
(*   (* | typ_fvar X => If X = Z then U else (typ_fvar X) *) *)
(*   | typ_fvar X => If X = Z then U else (typ_fvar X) *)
(*   | typ_unit   => typ_unit *)
(*   | T1 ** T2   => subst_tt Z U T1 ** subst_tt Z U T2 *)
(*   | T1 ==> T2   => subst_tt Z U T1 ==> subst_tt Z U T2 *)
(*   | typ_all T1 => typ_all (subst_tt Z U T1) *)
(*   | typ_gadt Ts Name => typ_gadt (map (subst_tt Z U) Ts) Name *)
(*   end. *)

(*
Substitution matching a type context, noted in the paper as ⊢ Θ : Δ.
It roughly means that the domain of the substitution is the same as free variables in Δ
and that the codomain is types without free variables
and that for each type equation, both sides are alpha equivalent after applying that substitution.
*)
Inductive subst_matches_typctx Σ : typctx -> substitution -> Prop :=
| tc_empty : subst_matches_typctx Σ []* []*
| tc_add_var : forall Θ Δ A T,
    wft Σ emptyΔ T ->
    subst_matches_typctx Σ Δ Θ ->
    A \notin substitution_sources Θ -> (* we want variables to be fresh as it helps with proofs *)
    A \notin domΔ Δ ->
    (* I'm adding to the env on the right to be consistent, but to subst to the left because the order does not matter - A's are different and T's have no free vars so reordering the substitution does not change anything. *)
    subst_matches_typctx Σ (Δ |, tc_var A) (Θ |, (A, T))
| tc_add_eq : forall Θ Δ T1 T2,
    subst_matches_typctx Σ Δ Θ ->
    (subst_tt' T1 Θ) = (subst_tt' T2 Θ) ->
    subst_matches_typctx Σ (Δ |, tc_eq (T1 ≡ T2)) Θ.

(* Semantic entailment of a set of equations, noted in the paper as Δ ⊨ T1 ≡ T2.
   It is defined such that an equation is entailed by Δ if for each substitution matching delta, both sides of that equation are alpha equivalent after applying that substitution.
 *)
Definition entails_semantic Σ (Δ : typctx) (eq : type_equation) :=
  match eq with
  | T1 ≡ T2 =>
    forall Θ, subst_matches_typctx Σ Δ Θ ->
         (subst_tt' T1 Θ) = (subst_tt' T2 Θ)
  end.

(* a shorthand allowing to define a list of free vars in Δ *)
Definition tc_vars (Xs : list var) : typctx :=
  List.map tc_var Xs.

Definition contradictory_bounds Σ Δ :=
  forall T1 T2, entails_semantic Σ Δ (T1 ≡ T2).

(** * Well-formedness of the GADT definitions and the envionment *)

(* Well-formedness of a single GADT constructor, see also okGadt.

We check the well-formedness of a single constructor in the context of the whole Σ.
In this way the definition is recursive - the constructor itself can refer to other constructors or itself, because it has the whole Σ available.

To better illustrate the conditions, let's see how the following constructor behaves:
case Pair[B,C](x: (B, C)) extends Expr[(B,C)]
or in Haskell: Pair (B * C) -> Expr (B * C)
or in the notation from the paper: ∀[B,C]. (B*C) -> [B*C] Expr
The constructor itself has two type parameters (existential types) and it creates a GADT that has a single type parameter.
If we match an [A]Expr with Pair[B,C] we will get a type equation A =:= B*C.
 *)
Inductive okConstructorDef : GADTEnv ->  nat -> GADTConstructorDef -> Prop :=
| ok_constr_def : forall Tarity Carity argT Σ retTs,
    (* First we need to ensure that the length of the parameter list of the returned GADT is equal to that GADT's arity - if Expr has arity 1, we need exactly one type parameter in the result, in our case the [B*C]. *)
    length retTs = Tarity ->

    (* now, we ensure that the argument type is well formed: *)
    (forall Alphas L Δ, (* we instantiate fresh (from ctx L) type variables for the type parameters, in our case these are: B, C (but we get fresh names) *)
        DistinctList Alphas -> (* We instantiate a set of fresh variables for all the type parameters of our constructors - the existential variables.
                                 They are existential, because when constructing the GADT they can be selected arbitrarily (however their choice impacts the type of constructed GADT) and once we are matching against a GADT we only know that these type names are *some* types and that they satisfy the type equations we got, we know only that there are some types that satisfy these equations and we do not know anything more about them.
                               *)
        length Alphas = Carity -> (* of course the amount of these fresh type names for type parameters we instantiate must be equal to the arity of the constructor *)
        (forall alpha, In alpha Alphas -> alpha \notin L) -> (* the freshness requirement as usual *)
        wft Σ (Δ |,| tc_vars Alphas) (open_tt_many_var Alphas argT) (* finally we specify that the constructor, once opened with these fresh type variables, must be a well formed type in every context delta (??? *** ???), since Δ can be empty, this constructor cannot have any more free variables other than its type parameters; that is to ensure that the GADT constructors are well formed in every possible environment *)
            (* in our example, we have two type parameters: B, C and the typ argument is @0 ** @1 which after opening resolves to B ** C;
               it is of course well formed in a Δ-env that has B and C as type variables and has no other free variables *)

            (* *** NOTE: actually I think this Δ can just be empty and we can then use typing weakening, TODO try fixing that *)
    ) ->
    (forall Alphas L Δ, (* we do completely analogusly for the type parameters of the returned GADT *)
        DistinctList Alphas ->
        length Alphas = Carity ->
        (forall alpha, In alpha Alphas -> alpha \notin L) ->
        (forall retT,
            In retT retTs ->
            (* each returned type must be well formed, i.e. it must be a good type only referring to the type parameters *)
            wft Σ (Δ |,| tc_vars Alphas) (open_tt_many_var Alphas retT))
          (* in our case we have one returned type parameter which takes two type variables (B, C as always) as arguments; the returned type is @0 ** @1 or after opening, B ** C *)
    ) ->
    (* Since the type parameters are handled as DeBruijn indices, the raw types of the argument and returned parameters should have no free variables - the only free variables they do have are the type parameters.
       This is the only place where we use DeBruijn indices not inside some explicit binder - these types are not closed in De Bruijn (`type` predicate) sense. But they are implicitly closed, because knowing the constructor definition, they can only be used after they are oppened with the right amount of free type variables, as defined abowe with wft.
       The types have no free variables, but they can refer to other GADTs - that is because GADT names are handled separately and we check the wft in context of the environment Σ - that ensures that only GADTs defined in that environment and no other are allowed.
     *)
    fv_typ argT = \{} -> (* fv_typ (@0 ** @1) = empty *)
    (forall rT, List.In rT retTs -> fv_typ rT = \{}) -> (* same as above *)
    okConstructorDef Σ Tarity (mkGADTconstructor Carity argT retTs).

(* okGadt defines that the whole Σ env is well formed, it checks that the defined GADTs have unique names and each of their constructors is well formed.

One unusual requirement is that the GADT should actually have at least one constructor, that was because if there are no GADT constructors it is impossible to correctly typecheck the pattern match.
The original paper did not explicitly state this requirement; technically it could be revised, because we could try proving that we can never actually create a value of a GADT with no constructors (it is an empty type, like bottom or False). This however is not the main scope of this whole work (as we want to be translating GADTs into Scala which simply has a builtin bottom type), so for now it is ignored and we assume that the GADTs must have some constructors.
 *)
Definition okGadt (Σ : GADTEnv) : Prop :=
  ok Σ /\
  forall Name Arity Defs,
    binds Name (mkGADT Arity Defs) Σ ->
    Defs <> []* /\
    (forall Def,
        In Def Defs ->
        okConstructorDef Σ Arity Def).

(* This seems to not be enforced in the paper, at least explicitly, and indeed maybe it is not necessary - in practice we will only add wft types, but for the equations that does not seem to matter *)
(* Definition oktypctx (Σ : GADTEnv) (Δ : typctx) : Prop := *)
(*   (forall T1 T2, (T1 ≡ T2) \in (Δeqs Δ) -> wft Σ Δ T1 /\ wft Σ Δ T2). *)

(* well formedness of the typing environment
   Currently we check that the bindings of variables to their types is unique and that the bound types are well formed in their earlier environment
 *)
Inductive okt : GADTEnv -> typctx -> ctx -> Prop :=
| okt_empty : forall Σ Δ,
    okGadt Σ ->
    (* oktypctx Σ Δ -> *)
    okt Σ Δ empty
| okt_typ : forall Σ Δ E x vk T,
    okt Σ Δ E ->
    wft Σ Δ T ->
    x # E ->
    x \notin domΔ Δ ->
    okt Σ Δ (E & x ~ bind_var vk T).

(** * Typing *)

(* A helper function that takes two lists of types and creates a set of equations where types from the first list are equal to corresponding types from the second one.
 Used mostly to shorten notation. *)
Definition equations_from_lists Ts Us : typctx :=
  zipWith (fun U V : typ => tc_eq (U ≡ V)) Ts Us.

Reserved Notation "{ Σ , Δ ,  E }  ⊢( L ) t ∈ T" (at level 0, Σ at level 99, T at level 69).

Inductive typing_taint : Set :=
| Treg (* this taint identifies the regular derivations, that is such which do not use equation as the last part (but they still can contain equations deeper inside) *)
| Tgen (* this taint identifies a general derivation, which may also use an equation *)
.

Inductive typing : typing_taint -> GADTEnv -> typctx -> ctx -> trm -> typ -> Prop :=
| typing_unit : forall Σ Δ E,
    okt Σ Δ E ->
    {Σ, Δ, E} ⊢(Treg) trm_unit ∈ typ_unit
| typing_var : forall Σ E Δ x vk T,
    binds x (bind_var vk T) E ->
    okt Σ Δ E ->
    {Σ, Δ, E} ⊢(Treg) (trm_fvar vk x) ∈ T (* x: T ⊢ x: T *)
| typing_cons : forall Σ E Δ TT1 Ts Name Ctor e1 Tarity Ctors Carity CargType CretTypes Targ Tret,
    (* to typecheck the constructor: *)
    {Σ, Δ, E} ⊢(TT1) e1 ∈ Targ -> (* we need to typecheck its only data parameter - its typ must match the argument type (see below) *)
    binds Name (mkGADT Tarity Ctors) Σ -> (* the GADT called `Name` that we are building must be bound in the Σ env and we check its constructors and arity *)
    nth_error Ctors Ctor = Some (mkGADTconstructor Carity CargType CretTypes) -> (* we specify that we construct the constructor with id Ctor, so we need to check that such constructor really exists and get its definition from the Ctors list *)
    length Ts = Carity -> (* the amount of concrete type parameters that we are instantiating the constructor with must be equal to the constructor's arity *)
    Targ = open_tt_many Ts CargType -> (* the argument type must be equal to the argument type as defined in the constructor, opened with the concrete types we use in this instance *)
    (forall T, In T Ts -> wft Σ Δ T) -> (* the concrete type parameters that we are instantiating the constructor with must be well formed in the current environment *)
    (* alternatively: Tret = open_tt_many (typ_gadt (List.map (fun T => open_tt_many T Ts) CretTypes) Name) Ts -> *)
    Tret = open_tt_many Ts (typ_gadt CretTypes Name) -> (* as with the argument, the types that will be in the type of the returned GADT must also be opened with the type parameters *)
    {Σ, Δ, E} ⊢(Treg) trm_constructor Ts (Name, Ctor) e1 ∈ Tret
| typing_abs : forall L Σ Δ E V e1 T1 TT,
    (forall x, x \notin L -> {Σ, Δ, E & x ~l V} ⊢(TT) e1 open_ee_varlam x ∈ T1) ->
    {Σ, Δ, E} ⊢(Treg) trm_abs V e1 ∈ V ==> T1
| typing_app : forall Σ Δ E T1 T2 e1 e2 TT1 TT2,
    {Σ, Δ, E} ⊢(TT1) e2 ∈ T1 ->
    {Σ, Δ, E} ⊢(TT2) e1 ∈ T1 ==> T2 ->
    {Σ, Δ, E} ⊢(Treg) trm_app e1 e2 ∈ T2
| typing_tabs : forall L Σ Δ E e1 T1 TT,
    (forall X, X \notin L ->
          value (e1 open_te_var X)) ->
    (forall X, X \notin L ->
          {Σ, Δ |,| [tc_var X]*, E} ⊢(TT) (e1 open_te_var X) ∈ (T1 open_tt_var X)) ->
    {Σ, Δ, E} ⊢(Treg) (trm_tabs e1) ∈ typ_all T1
| typing_tapp : forall Σ Δ E e1 T1 T T' TT,
    {Σ, Δ, E} ⊢(TT) e1 ∈ typ_all T ->
    wft Σ Δ T1 -> (* corresponds to the check `Δ ⊢ T1 : *` *)
    T' = open_tt T T1 ->
    {Σ, Δ, E} ⊢(Treg) trm_tapp e1 T1 ∈ T'
| typing_tuple : forall Σ Δ E T1 T2 e1 e2 TT1 TT2,
    {Σ, Δ, E} ⊢(TT1) e1 ∈ T1 ->
    {Σ, Δ, E} ⊢(TT2) e2 ∈ T2 ->
    {Σ, Δ, E} ⊢(Treg) trm_tuple e1 e2 ∈ T1 ** T2
| typing_fst : forall Σ Δ E T1 T2 e1 TT,
    {Σ, Δ, E} ⊢(TT) e1 ∈ T1 ** T2 ->
    {Σ, Δ, E} ⊢(Treg) trm_fst e1 ∈ T1
| typing_snd : forall Σ Δ E T1 T2 e1 TT,
    {Σ, Δ, E} ⊢(TT) e1 ∈ T1 ** T2 ->
    {Σ, Δ, E} ⊢(Treg) trm_snd e1 ∈ T2
| typing_fix : forall L Σ Δ E T v TT,
    (forall x, x \notin L -> value (v open_ee_varfix x)) ->
    (forall x, x \notin L -> {Σ, Δ, E & x ~f T} ⊢(TT) (v open_ee_varfix x) ∈ T) ->
    {Σ, Δ, E} ⊢(Treg) trm_fix T v ∈ T
| typing_let : forall L Σ Δ E V T2 e1 e2 TT1 TT2,
    {Σ, Δ, E} ⊢(TT1) e1 ∈ V ->
    (forall x, x \notin L -> {Σ, Δ, E & x ~l V} ⊢(TT2) e2 open_ee_varlam x ∈ T2) ->
    {Σ, Δ, E} ⊢(Treg) trm_let e1 e2 ∈ T2
(* typing case merges rules ty-case and pat-cons from the original paper *)
(* for example, let's see we are typing the match as in the eval function defined above; since there are many branches, we will look at the Pair branch in particular *)
| typing_case : forall L Σ Δ E e ms Ts T Name Tc Tarity Defs TT1,
    {Σ, Δ, E} ⊢(TT1) e ∈ T -> (* first we need to typecheck the expression that we will be matching, in our eval example it is the argument that we are matching *)
    T = (typ_gadt Ts Name) -> (* for the match to work, that expression must be a GADT and its name must match the one that is provided in the syntax, in our example `Expr` *)
    binds Name (mkGADT Tarity Defs) Σ -> (* that GADT must be bound in our Σ environment *)
    length Defs = length ms -> (* implicit exhaustivity check: our pattern match must have as many branches as the GADT we are matching has constructors since we have a 1-1 correspondence between branches and constructors; in our case there are 4 branches *)

    (* we use zip instead of Forall2 to get better induction for free, but can rephrase it as needed using equivalence theorems *)
    (forall def clause, In (def, clause) (zip Defs ms) ->
                   (* we need to make sure that the arity defined in the syntax actually matches the arity of the respective constructor,
                      in our example we check that the match brings two type variables [X,Y] and the arity of the Pair constructor is 2 *)
                   clauseArity clause = Carity def) ->
    (forall def clause, In (def, clause) (zip Defs ms) ->
                   (* now, for each pair of: constructor definition + a clause matching that constructor, we check the actual important properties: *)
               forall Alphas x,
                 length Alphas = Carity def -> (* since we instantiate the type variables, we need to ensure that the added type variables amount is equalt to the arity *)
                 (* below follow multiple freshness conditions that boil down to: Alphas and x are fresh and mutually distinct *)
                 DistinctList Alphas ->
                 (forall A, In A Alphas -> A \notin L) ->
                 x \notin L ->
                 x \notin from_list Alphas ->
                 (* finally we check if the term of the clause/branch, opened with the added existential type variables and opened with the one variable whose type is aligned with the type that the respective constructor accepts, is well typed and typechecks to some type Tc; that type Tc is important because it is the same for all branches - the return type must be the same for every branch *)
                 (*
                   in our example, we check that the expression
                   <eval[@0](fst #0), eval[@1](snd #0)> typechecks to A
                   opening the term with fresh type variables [X, Y] and variable e whose type is: [X]Expr ** [Y]Expr yields
                   <eval[X](fst e), eval[Y](snd e)> and we want it to typecheck to A
                   fst e is [X]Expr, so eval typechecks and returns X, analogously for the second one, so our branch typechecks to X ** Y
                   but we also have the equality X**Y =:= A so we will be able to replace that X**Y with A using ty_eq
                  *)
                 { Σ,
                   (Δ
                      |,| tc_vars Alphas (* in our example: Alphas = [X,Y] *)
                      |,| equations_from_lists Ts
                      (List.map (open_tt_many_var Alphas) (Crettypes def))
                   ),
                   (* Ts === Crettypes def; in our example that equation is X ** Y =:= A *)
                   E
                   & x ~l (open_tt_many_var Alphas (Cargtype def)) (* e: [X]Expr ** [Y]Expr *)
                 } ⊢(Tgen) (open_te_many_var Alphas (clauseTerm clause)) open_ee_varlam x ∈ Tc
            ) ->
    { Σ, Δ, E } ⊢(Treg) trm_matchgadt e Name ms ∈ Tc
| typing_eq : forall Σ Δ E T1 T2 e TT,
    { Σ, Δ, E } ⊢(TT) e ∈ T1 ->
    entails_semantic Σ Δ (T1 ≡ T2) ->
    wft Σ Δ T2 -> (* NOTE: This is not part of the original calculus; but without this assumption, we can get good typing judgements featuring ill-formed types, which complicates stuff for some proofs; theoretically it may be possible to do without it, but I decided to add it because it does not restrict the language in a meaningful way - yes, we are no longer allowed to type ill-formed types with contradictory bounds, but we still can derive all well-formed equalities from a contradiction and that is enough; it will actually be easier to translate to pDOT if we know that all types are wft; ill-formed types are never useful in our use cases. *)
    { Σ, Δ, E } ⊢(Tgen) e ∈ T2
where "{ Σ , Δ , E } ⊢( R ) t ∈ T" := (typing R Σ Δ E t T).

(** * Reduction rules (Small-step operational semantics) *)

Reserved Notation "e1 --> e2" (at level 49).
Inductive red : trm -> trm -> Prop :=
| red_beta : forall T e1 v2 e',
    term (trm_abs T e1) ->
    value v2 ->
    e' = open_ee e1 v2 ->
    trm_app (trm_abs T e1) v2 --> e'
| red_tbeta : forall e1 T e',
    term (trm_tabs e1) ->
    type T ->
    e' = open_te e1 T ->
    trm_tapp (trm_tabs e1) T --> e'
| red_letbeta : forall v1 e2 e',
    term (trm_let v1 e2) ->
    value v1 ->
    e' = open_ee e2 v1 ->
    trm_let v1 e2 --> e'
| red_fst : forall v1 v2,
    value (trm_tuple v1 v2) ->
    trm_fst (trm_tuple v1 v2) --> v1
| red_snd : forall v1 v2,
    value (trm_tuple v1 v2) ->
    trm_snd (trm_tuple v1 v2) --> v2
| red_fix : forall T v e',
    term (trm_fix T v) ->
    e' = open_ee v (trm_fix T v) ->
    trm_fix T v --> e'
| red_match : forall e1 G cid Ts ms Carity Ce e',
    (* we can proceed with a pattern match of a constructor: *)
    value (trm_constructor Ts (G, cid) e1) -> (* it must be a computed value *)
    nth_error ms cid = Some (clause Carity Ce) -> (* we get the branch corresponding to the constructor id encoded inside of the value *)
    length Ts = Carity -> (* this check will be derivable from typing and since we always execute well typed terms, we could technically skip it *)
    e' = open_ee (open_te_many Ts Ce) e1 -> (* we open the term of the selected branch with the types and value from the constructor,
this is still much weaker requirement than original calculus which explicitly checked if v matches the pattern;
as we got rid of separate matching rules we check that, only partially, implicitly:
- we check that the GADT name of the matched value and the one in the match are the same
- we select the branch corresponding to the correct constructor
- we check that the arity of that branch matches that of the constructor *)
    (* Example:
       We may be evaluating the following expression:
       match Pair[U,V](<x,y>) of type Expr with
             ... (other cases)
             case Pair[X,Y](p) => <eval[X](fst p), eval[Y](snd p)
       which reduces to
       <eval[U](fst <x,y>), eval[V](snd <x,y>)>
       (so we have substituted X ↦ U, Y ↦ V, p ↦ <x,y>)

       Of course here we skip the complexity of handling the types using De Bruijn indices, so X, Y and p are actually handled by indices; but that is just a detail and it works in the same way as everywhere else.
       What is more important here is that if we remove some of syntactic sugar, we get:
       match (trm_constructor [U,V] (Expr, 2) <x,y>) of type Expr with
            case [branch 0] => ...
            case [branch 1] => ...
            case [branch 2, arity 2] => <eval[@0](fst #0), eval[@1](snd #0)>
       What is important here that Pair was just an abbreviation of (Expr, 2) which means that Pair is the third constructor of type Expr.
       And thus it matches with the branch of the same index (2).
     *)
    trm_matchgadt (trm_constructor Ts (G, cid) e1) G ms --> e'
| ered_app_1 : forall e1 e1' e2,
    e1 --> e1' ->
    trm_app e1 e2 --> trm_app e1' e2
| ered_constructor : forall l Ctor e e',
    e --> e' ->
    trm_constructor l Ctor e --> trm_constructor l Ctor e'
| ered_app_2 : forall v1 e2 e2',
    value v1 ->
    e2 --> e2' ->
    trm_app v1 e2 --> trm_app v1 e2'
| ered_tapp : forall e1 e1' T,
    type T ->
    e1 --> e1' ->
    trm_tapp e1 T --> trm_tapp e1' T
| ered_fst : forall e e',
    e --> e' ->
    trm_fst e --> trm_fst e'
| ered_snd : forall e e',
    e --> e' ->
    trm_snd e --> trm_snd e'
| ered_tuple_fst : forall e1 e2 e1',
    e1 --> e1' ->
    trm_tuple e1 e2 --> trm_tuple e1' e2
| ered_tuple_snd : forall v1 e2 e2',
    value v1 ->
    e2 --> e2' ->
    trm_tuple v1 e2 --> trm_tuple v1 e2'
| ered_let : forall e1 e2 e1',
    e1 --> e1' ->
    trm_let e1 e2 --> trm_let e1' e2
| ered_match : forall e1 G ms e1',
    e1 --> e1' ->
    trm_matchgadt e1 G ms --> trm_matchgadt e1' G ms
where "e1 --> e2" := (red e1 e2).

(* These are not used directly in the definitions but they are used in proofs. *)
Definition subst_td (A : var) (U : typ) (d : typctx_elem) : typctx_elem :=
  match d with
  | tc_var A => tc_var A
  | tc_eq (T1 ≡ T2) => tc_eq ((subst_tt A U T1) ≡ (subst_tt A U T2))
  end.

Fixpoint subst_td_many (Xs : list var) (Us : list typ) (d : typctx_elem) : typctx_elem :=
  match (Xs, Us) with
  | ((List.cons X Xt), (List.cons U Ut)) => subst_td_many Xt Ut (subst_td X U d)
  | _ => d
  end.

(** * Statement of desired safety properties *)

Definition progress := forall TT Σ e T,
    {Σ, emptyΔ, empty} ⊢(TT) e ∈ T ->
    (value e) \/ (exists e', e --> e').

Definition preservation := forall TT Σ e T e',
    {Σ, emptyΔ, empty} ⊢(TT) e ∈ T ->
    e --> e' ->
    {Σ, emptyΔ, empty} ⊢(Tgen) e' ∈ T.
