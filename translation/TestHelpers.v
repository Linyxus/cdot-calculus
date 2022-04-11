Require Import Helpers.
Require Import Library.
Require Import Coq.Arith.Compare_dec.

Definition lift_rec_avar (k: nat) (w: nat) (a: avar) : avar :=
  match a with
  | avar_b i => if le_gt_dec k i then avar_b (w + i) else avar_b i
  | avar_f x => avar_f x
end.

Definition lift_rec_path (k: nat) (w: nat) (p: path): path :=
  match p with
  | p_sel x bs => p_sel (lift_rec_avar k w x) bs
  end.

Fixpoint lift_rec_typ (k: nat) (w: nat) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (lift_rec_dec k w D)
  | T1 ∧ T2        => lift_rec_typ k w T1 ∧ lift_rec_typ k w T2
  | p ↓ L          => lift_rec_path k w p ↓ L
  | μ T            => μ (lift_rec_typ (S k) w T)
  | ∀(T1) T2      => ∀(lift_rec_typ k w T1) lift_rec_typ (S k) w T2
  | {{ p }}        => {{ lift_rec_path k w p }}
  end
with lift_rec_dec (k: nat) (u: nat) (D: dec): dec :=
  match D with
  | { A >: T <: U } => { A >: lift_rec_typ k u T <: lift_rec_typ k u U }
  | { a ⦂ T } => { a ⦂ lift_rec_typ k u T }
  end.

Fixpoint lift_rec_trm (k: nat) (u: nat) (t: trm): trm :=
  match t with
  | trm_val v      => trm_val (lift_rec_val k u v)
  | trm_path p     => trm_path (lift_rec_path k u p)
  | trm_app p q    => trm_app (lift_rec_path k u p) (lift_rec_path k u q)
  | trm_let t1 t2  => trm_let (lift_rec_trm k u t1) (lift_rec_trm (S k) u t2)
  end
with lift_rec_val (k: nat) (u: nat) (v: val): val :=
  match v with
  | ν(T)ds   => ν (lift_rec_typ (S k) u T) lift_rec_defs (S k) u ds
  | λ(T) e  => λ(lift_rec_typ k u T) lift_rec_trm (S k) u e
  end
with lift_rec_def (k: nat) (u: nat) (d: def): def :=
  match d with
  | def_typ A T => def_typ A (lift_rec_typ k u T)
  | { a := t } => { a := lift_rec_defrhs k u t }
  end
with lift_rec_defs (k: nat) (u: nat) (ds: defs): defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons tl d => defs_cons (lift_rec_defs k u tl) (lift_rec_def k u d)
  end
with lift_rec_defrhs (k: nat) (u: nat) (drhs: def_rhs) : def_rhs :=
  match drhs with
  | defp p => defp (lift_rec_path k u p)
  | defv v => defv (lift_rec_val k u v)
  end.

Definition shift1_typ (t : typ) : typ := lift_rec_typ 0 1 t.
Definition shift1_trm (t : trm) : trm := lift_rec_trm 0 1 t.
Definition shift1_p (p : path) : path := lift_rec_path 0 1 p.

Coercion trm_path : path >-> trm.

Ltac cleanup :=
  repeat
    match goal with
    | [ H: ?x <> ?y |- _ ] => clear H
    | [ H: ?x = ?y |- _ ] =>
      match x with
      | y => clear H
      end
    end.

Ltac var_subtyp :=
  match goal with
  | [ |- ?G ⊢ tvar ?x : ?T ] =>
    match goal with
    | [ |- context [x ~ ?BT] ] =>
      apply ty_sub with BT
    end
  end.

Ltac solve_bind :=
  repeat progress (
           lazymatch goal with
           | |- binds ?Var ?What (?Left & ?Right) =>
    match goal with
    | |- binds Var What (Left & Var ~ ?Sth) =>
      apply~ binds_concat_right; apply~ binds_single_eq
    | _ => apply~ binds_concat_left
    end
           end).
Ltac subsel2 :=
  match goal with
  | [ |- ?G ⊢ ?A <: ?B ] =>
    apply subtyp_sel2 with A
  end.

Ltac subsel1 :=
  match goal with
  | [ |- ?G ⊢ ?A <: ?B ] =>
    apply subtyp_sel1 with B
  end.

Ltac solve_subtyp_and :=
repeat
  match goal with
  | [ |- ?G ⊢ ?A ∧ ?B <: ?C ] =>
    match B with
    | C =>
      apply subtyp_and12
    | _ =>
      eapply subtyp_trans; try apply subtyp_and11
    end
  end.

Ltac var_subtyp_bind :=
  var_subtyp;
  [ apply ty_var; solve_bind
  | solve_subtyp_and].

Definition make_fun_apply (f : trm) (arg : trm) (withlet : bool) : trm :=
  let wrap t :=
      if withlet then (let_trm t) else t in
  match f with
  | trm_path pf =>
    match arg with
    | trm_path pa =>
      wrap (trm_app pf pa)
    | _ =>
      trm_let arg (wrap (trm_app (shift1_p pf) this))
    end
  | _ =>
    trm_let
      f
      (trm_let (shift1_trm arg)
               (wrap (trm_app super this))
      )
  end.

Notation "f $ a" := (make_fun_apply f a false) (at level 42).
Notation "f $$ a" := (make_fun_apply f a true) (at level 42).

Definition TLgen (T : typ) : trm :=
  let inner := shift1_typ T in
  let_trm (ν({GenT == inner}) {( {GenT ⦂= inner} )}).

Ltac invert_label :=
  match goal with
  | [ H: label_typ ?A = label_typ ?B |- _ ] =>
    inversion H
  | [ H: label_trm ?A = label_trm ?B |- _ ] =>
    inversion H
  end.
Ltac var_subtyp_mu :=
  match goal with
  | [ |- ?G ⊢ tvar ?x : ?T ] =>
    match goal with
    | [ |- context [x ~ μ ?BT] ] =>
      apply ty_sub with (open_typ_p (pvar x) BT)
    end
  end.
Ltac var_subtyp_mu2 :=
  var_subtyp_mu; [
    apply ty_rec_elim; apply ty_var; solve_bind
  | crush
  ].
Ltac var_subtyp2 :=
  var_subtyp; [
    apply ty_var; solve_bind
  | idtac ].
