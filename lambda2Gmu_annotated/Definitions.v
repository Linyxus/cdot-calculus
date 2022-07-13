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
Require Import GMu.Definitions.
Require Export GMu.Definitions.

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
(* creates a tuple - <t1, t2> - ANNOTATED with types of elements *)
| trm_tuple : typ -> trm -> typ -> trm -> trm
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

ANNOTATED with return type
*)
| trm_matchgadt : trm -> GADTName -> (list Clause) -> typ -> trm
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
  Hypothesis trm_tuple_case : forall (t1 t2 : trm) T1 T2,
      P t1 -> P t2 -> P (trm_tuple T1 t1 T2 t2).
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
  Hypothesis trm_match_case : forall (clauses : list Clause) (G : GADTName) (e : trm) T,
      P e ->
      (* (forall TN e', In (clause TN e') ls -> P e') -> *)
      Forall (fun c => P (clauseTerm c)) clauses ->
      P (trm_matchgadt e G clauses T).
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
  | trm_tuple T1 e1 T2 e2 => trm_tuple_case T1 T2 (trm_ind' e1) (trm_ind' e2)
  | trm_fst e => trm_fst_case (trm_ind' e)
  | trm_snd e => trm_snd_case (trm_ind' e)
  | trm_abs T e => trm_abs_case T (trm_ind' e)
  | trm_app e1 e2 => trm_app_case (trm_ind' e1) (trm_ind' e2)
  | trm_tabs e => trm_tabs_case (trm_ind' e)
  | trm_tapp e T => trm_tapp_case T (trm_ind' e)
  | trm_fix T e => trm_fix_case T (trm_ind' e)
  | trm_matchgadt e G clauses T => trm_match_case G T (trm_ind' e) (list_clause_ind clauses)
  | trm_let e1 e2 => trm_let_case (trm_ind' e1) (trm_ind' e2)
    end.
End trm_ind'.

Fixpoint sum (ls : list nat) : nat :=
  match ls with
    | nil => O
    | cons h t => plus h (sum t)
  end.

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
  | trm_tuple _ e1 _ e2 => 1 + trm_size e1 + trm_size e2
  | trm_fst e1 => 1 + trm_size e1
  | trm_snd e1 => 1 + trm_size e1
  | trm_abs T e1    => 1 + trm_size e1
  | trm_app e1 e2 => 1 + trm_size e1 + trm_size e2
  | trm_tabs e1 => 1 + trm_size e1
  | trm_tapp e1 T => 1 + trm_size e1
  | trm_fix T e1 => 1 + trm_size e1
  | trm_matchgadt e G cs _ => trm_size e + sum (map_clause_trms trm_size cs)
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

Fixpoint open_te_rec (k : nat) (u : typ) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => trm_bvar i
  | trm_fvar vk x    => trm_fvar vk x
  | trm_constructor tparams C e1 => trm_constructor (open_typlist_rec k u tparams) C (open_te_rec k u e1)
  | trm_unit => trm_unit
  | trm_tuple T1 e1 T2 e2 => trm_tuple (open_tt_rec k u T1) (open_te_rec k u e1) (open_tt_rec k u T2) (open_te_rec k u e2)
  | trm_fst e1 => trm_fst (open_te_rec k u e1)
  | trm_snd e1 => trm_snd (open_te_rec k u e1)
  | trm_abs T e1    => trm_abs (open_tt_rec k u T) (open_te_rec k u e1)
  | trm_app e1 e2 => trm_app (open_te_rec k u e1) (open_te_rec k u e2)
  | trm_tabs e1 => trm_tabs (open_te_rec (S k) u e1)
  | trm_tapp e1 T => trm_tapp (open_te_rec k u e1) (open_tt_rec k u T)
  | trm_fix T e1 => trm_fix (open_tt_rec k u T) (open_te_rec k u e1)
  | trm_matchgadt e1 G cs T =>
    (* each clause binds n type variables *)
    trm_matchgadt (open_te_rec k u e1) G
                  (map (fun c => match c with clause n e => clause n (open_te_rec (k + n) u e) end) cs)
                  (open_tt_rec k u T)
  | trm_let e1 e2 => trm_let (open_te_rec k u e1) (open_te_rec k u e2)
  end.

Fixpoint open_ee_rec (k : nat) (u : trm) (e : trm) {struct e} : trm :=
  match e with
  (* | trm_bvar i    => If k = i then u else (trm_bvar i) *)
  | trm_bvar i    => if (k =? i) then u else (trm_bvar i)
  | trm_fvar vk x    => trm_fvar vk x
  | trm_constructor tparams C e1 => trm_constructor tparams C (open_ee_rec k u e1)
  | trm_unit => trm_unit
  | trm_tuple T1 e1 T2 e2 => trm_tuple T1 (open_ee_rec k u e1) T2 (open_ee_rec k u e2)
  | trm_fst e1 => trm_fst (open_ee_rec k u e1)
  | trm_snd e1 => trm_snd (open_ee_rec k u e1)
  | trm_abs T e1    => trm_abs T (open_ee_rec (S k) u e1)
  | trm_app e1 e2 => trm_app (open_ee_rec k u e1) (open_ee_rec k u e2)
  | trm_tabs e1 => trm_tabs (open_ee_rec k u e1)
  | trm_tapp e1 T => trm_tapp (open_ee_rec k u e1) T
  | trm_fix T e1 => trm_fix T (open_ee_rec (S k) u e1)
  | trm_matchgadt e1 G cs T =>
    (* each clause binds 1 value variable *)
    trm_matchgadt (open_ee_rec k u e1) G
                  (map (fun c => match c with clause n e => clause n (open_ee_rec (S k) u e) end) cs)
                  T
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

Notation "t 'open_te_var' X" := (open_te t (typ_fvar X)) (at level 67).
Notation "t 'open_ee_varlam' x" := (open_ee t (trm_fvar lam_var x)) (at level 67).
Notation "t 'open_ee_varfix' x" := (open_ee t (trm_fvar fix_var x)) (at level 67).

(* Definition open_tt_many (args : list typ) (T : typ) := fold_left open_tt args T. *)
(* Definition open_tt_many_var (args : list var) (T : typ) := fold_left (fun typ v => open_tt typ (typ_fvar v)) args T. *)

Fixpoint open_te_many (args : list typ) (e : trm) :=
  match args with
  | ha :: ta => open_te_many ta (open_te e ha)
  | []* => e
  end.

Definition open_te_many_var (args : list var) (e : trm) := open_te_many (map typ_fvar args) e.

(** * Free Variables *)

Fixpoint fv_trm (e : trm) {struct e} : vars :=
  match e with
  | trm_bvar i => \{}
  | trm_fvar _ x => \{x}
  | trm_unit   => \{}
  | trm_tuple T1 e1 T2 e2 => fv_trm e1 \u fv_trm e2 \u fv_typ T1 \u fv_typ T2
  | trm_fst e1 => fv_trm e1
  | trm_snd e1 => fv_trm e1
  | trm_abs T1 e1 => fv_typ T1 \u fv_trm e1
  | trm_app e1 e2 => fv_trm e1 \u fv_trm e2
  | trm_tabs e1 => fv_trm e1
  | trm_tapp e1 T1 => fv_typ T1 \u fv_trm e1
  | trm_fix T1 e1 => fv_typ T1 \u fv_trm e1
  | trm_let e1 e2 => fv_trm e1 \u fv_trm e2
  | trm_matchgadt e _ cs T =>
    fold_left (fun fv c => fv \u fv_trm (clauseTerm c)) cs (fv_trm e) \u fv_typ T
  | trm_constructor Ts _ e1 =>
    fold_left (fun fv T => fv \u fv_typ T) Ts (fv_trm e1)
  end.

Inductive term : trm -> Prop :=
| term_var : forall vk x,
    term (trm_fvar vk x)
| term_constructor : forall Tparams Name e1,
    term e1 ->
    (forall Tparam, In Tparam Tparams -> type Tparam) ->
    term (trm_constructor Tparams Name e1)
| term_unit : term trm_unit
| term_tuple : forall e1 e2 T1 T2,
    term e1 ->
    type T1 ->
    term e2 ->
    type T2 ->
    term (trm_tuple T1 e1 T2 e2)
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
| term_matchgadt : forall L e1 G ms T,
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
    type T ->
    term (trm_matchgadt e1 G ms T)
with
value : trm -> Prop :=
| value_abs : forall V e1, term (trm_abs V e1) ->
                      value (trm_abs V e1)
| value_tabs : forall e1, term (trm_tabs e1) ->
                     value (trm_tabs e1)
| value_unit : value (trm_unit)
| value_lamvar : forall x, value (trm_fvar lam_var x)
| value_tuple : forall e1 e2 T1 T2,
    value e1 ->
    value e2 ->
    term (trm_tuple T1 e1 T2 e2) ->
    value (trm_tuple T1 e1 T2 e2)
| value_gadt : forall Tparams Name e1,
    term (trm_constructor Tparams Name e1) ->
    value e1 ->
    value (trm_constructor Tparams Name e1)
.

Unset Implicit Arguments.

(** * Substitution *)

Fixpoint subst_te (Z : var) (U : typ) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i => trm_bvar i
  | trm_fvar vk x => trm_fvar vk x
  | trm_unit   => trm_unit
  | trm_tuple T1 e1 T2 e2 => trm_tuple (subst_tt Z U T1) (subst_te Z U e1) (subst_tt Z U T2) (subst_te Z U e2)
  | trm_fst e1 => trm_fst (subst_te Z U e1)
  | trm_snd e1 => trm_snd (subst_te Z U e1)
  | trm_abs T1 e1 => trm_abs (subst_tt Z U T1) (subst_te Z U e1)
  | trm_app e1 e2 => trm_app (subst_te Z U e1) (subst_te Z U e2)
  | trm_tabs e1 => trm_tabs (subst_te Z U e1)
  | trm_tapp e1 T1 => trm_tapp (subst_te Z U e1) (subst_tt Z U T1)
  | trm_fix T1 e1 => trm_fix (subst_tt Z U T1) (subst_te Z U e1)
  | trm_let e1 e2 => trm_let (subst_te Z U e1) (subst_te Z U e2)
  | trm_matchgadt e G cs T =>
    trm_matchgadt (subst_te Z U e) G (map_clause_trm_trm (subst_te Z U) cs) (subst_tt Z U T)
  | trm_constructor Ts N e1 => trm_constructor (map (subst_tt Z U) Ts) N (subst_te Z U e1)
  end.

Fixpoint subst_ee (z : var) (k : var_kind) (u : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i => trm_bvar i
  | trm_fvar vk x => If x = z /\ vk = k then u else (trm_fvar vk x)
  | trm_unit   => trm_unit
  | trm_tuple T1 e1 T2 e2 => trm_tuple T1 (subst_ee z k u e1) T2 (subst_ee z k u e2)
  | trm_fst e1 => trm_fst (subst_ee z k u e1)
  | trm_snd e1 => trm_snd (subst_ee z k u e1)
  | trm_abs T1 e1 => trm_abs T1 (subst_ee z k u e1)
  | trm_app e1 e2 => trm_app (subst_ee z k u e1) (subst_ee z k u e2)
  | trm_tabs e1 => trm_tabs (subst_ee z k u e1)
  | trm_tapp e1 T1 => trm_tapp (subst_ee z k u e1) T1
  | trm_fix T1 e1 => trm_fix T1 (subst_ee z k u e1)
  | trm_let e1 e2 => trm_let (subst_ee z k u e1) (subst_ee z k u e2)
  | trm_matchgadt e G cs T =>
    trm_matchgadt (subst_ee z k u e) G (map_clause_trm_trm (subst_ee z k u) cs) T
  | trm_constructor Ts N e1 => trm_constructor Ts N (subst_ee z k u e1)
  end.

Reserved Notation "{ Σ , Δ ,  E }  ⊢( L ) t ∈ T" (at level 0, Σ at level 99, T at level 69).

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
    {Σ, Δ, E} ⊢(Treg) trm_tuple T1 e1 T2 e2 ∈ T1 ** T2
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
    { Σ, Δ, E } ⊢(Treg) trm_matchgadt e Name ms Tc ∈ Tc
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
| red_fst : forall v1 v2 T1 T2,
    value (trm_tuple T1 v1 T2 v2) ->
    trm_fst (trm_tuple T1 v1 T2 v2) --> v1
| red_snd : forall v1 v2 T1 T2,
    value (trm_tuple T1 v1 T2 v2) ->
    trm_snd (trm_tuple T1 v1 T2 v2) --> v2
| red_fix : forall T v e',
    term (trm_fix T v) ->
    e' = open_ee v (trm_fix T v) ->
    trm_fix T v --> e'
| red_match : forall e1 G cid Ts ms Carity Ce e' Tc,
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
    trm_matchgadt (trm_constructor Ts (G, cid) e1) G ms Tc --> e'
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
| ered_tuple_fst : forall e1 e2 e1' T1 T2,
    e1 --> e1' ->
    trm_tuple T1 e1 T2 e2 --> trm_tuple T1 e1' T2 e2
| ered_tuple_snd : forall v1 e2 e2' T1 T2,
    value v1 ->
    e2 --> e2' ->
    trm_tuple T1 v1 T2 e2 --> trm_tuple T1 v1 T2 e2'
| ered_let : forall e1 e2 e1',
    e1 --> e1' ->
    trm_let e1 e2 --> trm_let e1' e2
| ered_match : forall e1 G ms e1' Tc,
    e1 --> e1' ->
    trm_matchgadt e1 G ms Tc --> trm_matchgadt e1' G ms Tc
where "e1 --> e2" := (red e1 e2).

(** * Statement of desired safety properties *)

Definition progress := forall TT Σ e T,
    {Σ, emptyΔ, empty} ⊢(TT) e ∈ T ->
    (value e) \/ (exists e', e --> e').

Definition preservation := forall TT Σ e T e',
    {Σ, emptyΔ, empty} ⊢(TT) e ∈ T ->
    e --> e' ->
    {Σ, emptyΔ, empty} ⊢(Tgen) e' ∈ T.
