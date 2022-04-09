Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import Definitions Lookup Sequences.

(** * Operational Semantics *)

Definition resolved_path γ p :=
  exists v, γ ⟦ p ⤳ defv v ⟧.

(** Term-reduction relation *)
Reserved Notation "t1 '⟼' t2" (at level 40, t2 at level 39).

Inductive red : sta * trm -> sta * trm -> Prop :=

(** [γ ⊢ p ⤳ q ]      #<br>#
    [―――――――――――――――――――――]      #<br>#
    [γ | p ⟼ γ | q]      *)
| red_resolve: forall γ p q,
    γ ⟦ p ⤳ defp q ⟧ ->
    (γ, trm_path p) ⟼ (γ, trm_path q)

(** [γ ⊢ q ⤳ λ(T)t ]      #<br>#
    [―――――――――――――――――――――]      #<br>#
    [γ | q p ⟼ γ | tᵖ]      *)
| red_app: forall γ p q T t,
    γ ⟦ q ⤳ defv (λ(T) t) ⟧ ->
    resolved_path γ p ->
    (γ, trm_app q p) ⟼ (γ, open_trm_p p t)

(** [γ | q ⟼ q' ]      #<br>#
    [―――――――――――――――――――――]      #<br>#
    [γ | q p ⟼ γ | q' p]      *)
| red_ctx_app1: forall γ p q q',
    (γ, trm_path q) ⟼ (γ, trm_path q') ->
    (γ, trm_app q p) ⟼ (γ, trm_app q' p)

(** [γ | p ⟼ p' ]      #<br>#
    [―――――――――――――――――――――]      #<br>#
    [γ | ρ^γ p ⟼ γ | ρ^γ p']      *)
| red_ctx_app2: forall γ p p' q,
    resolved_path γ q ->
    (γ, trm_path p) ⟼ (γ, trm_path p') ->
    (γ, trm_app q p) ⟼ (γ, trm_app q p')

(** [γ | let x = v in t ⟼ γ, x = v | tˣ] *)
| red_let_val : forall v t γ x,
    x # γ ->
    (γ, trm_let (trm_val v) t) ⟼ (γ & x ~ v, open_trm x t)

(** [γ | let y = p in t ⟼ γ | tᵖ] *)
| red_let_path : forall t γ p,
    resolved_path γ p ->
    (γ, trm_let (trm_path p) t) ⟼ (γ, open_trm_p p t)

(** [γ | t0 ⟼ γ' | t0']                            #<br>#
    [―――――――――――――――――――――――――――――――――――――――――――――――]  #<br>#
    [γ | let x = t0 in t ⟼ γ' | let x = t0' in t]  *)
| red_let_tgt : forall t0 t γ t0' γ',
    (γ, t0) ⟼ (γ', t0') ->
    (γ, trm_let t0 t) ⟼ (γ', trm_let t0' t)

(** [γ ⊢ p ⤳ ν[q.A](x: T)ds ]      #<br>#
    [γ ⊢ q ⤳* ρ^γ ]      #<br>#
    [―――――――――――――――――――――]      #<br>#
    [γ | case p of y: (ρ^γ).A y => t1 else t2 ⟼ γ | t1^p ]      *)
| red_case_match : forall γ p q A T ds r t1 t2,
    resolved_path γ r ->
    γ ⟦ p ⤳ defv (ν[q↘A](T)ds) ⟧ ->
    γ ⟦ defp (open_path_p p q) ⤳* defp r ⟧ ->
    (γ, trm_case p r A t1 t2) ⟼ (γ, open_trm_p p t1)

(** [γ ⊢ p ⤳ ν[q.A](x: T)ds ]      #<br>#
    [γ ⊢ q ⤳* ρ₁^γ ]      #<br>#
    [ρ₁ ≠ ρ₂]      #<br>#
    [―――――――――――――――――――――]      #<br>#
    [γ | case p of y: (ρ₂^γ).A y => t1 else t2 ⟼ γ | t1^p ]      *)
| red_case_else : forall γ p q A1 A2 T ds r1 r2 t1 t2,
    resolved_path γ r1 ->
    resolved_path γ r2 ->
    γ ⟦ p ⤳ defv (ν[q ↘ A1](T)ds) ⟧ ->
    γ ⟦ defp (open_path_p p q) ⤳* defp r1 ⟧ ->
    (r1 <> r2 \/ A1 <> A2) ->
    (γ, trm_case p r2 A2 t1 t2) ⟼ (γ, t2)

(** [γ ⊢ p ⤳ λ(x: T)t ]      #<br>#
    [―――――――――――――――――――――]      #<br>#
    [γ | case p of y: r.A y => t1 else=> t2 ⟼ γ | t2 ]      *)
| red_case_lambda : forall γ p t T r A t1 t2,
    γ ⟦ p ⤳ defv (λ(T) t) ⟧ ->
    (γ, trm_case p r A t1 t2) ⟼ (γ, t2)

(** [γ ⊢ p ⤳ p' ]      #<br>#
    [―――――――――――――――――――――]      #<br>#
    [γ | case p of y: r.A y => t1 else t2 ⟼ γ | case p' of tag r.A y => t1 else t2 ]      *)
| red_ctx_case1 : forall γ p p' r A t1 t2,
    (γ, trm_path p) ⟼ (γ, trm_path p') ->
    (γ, trm_case p r A t1 t2) ⟼ (γ, trm_case p' r A t1 t2)

(** [γ ⊢ r ⤳ r' ]      #<br>#
    [―――――――――――――――――――――]      #<br>#
    [γ | case ρ^λ of y: r'.A y => t1 else t2 ⟼ γ | case ρ^γ of tag r'.A y => t1 else t2 ]      *)
| red_ctx_case2 : forall γ p r r' A t1 t2,
    resolved_path γ p ->
    (γ, trm_path r) ⟼ (γ, trm_path r') ->
    (γ, trm_case p r A t1 t2) ⟼ (γ, trm_case p r' A t1 t2)

where "t1 '⟼' t2" := (red t1 t2).

(** Reflexive, transitive closure of reduction relation *)
Notation "t1 '⟼*' t2" := (star red t1 t2) (at level 40).

(** ** Normal forms *)

(** Paths and values are considered to be in normal form. *)
Inductive norm_form: sta -> trm -> Prop :=
| nf_path: forall γ p, (exists v, γ ⟦ p ⤳ defv v ⟧) -> norm_form γ (trm_path p)
| nf_val: forall γ v, norm_form γ (trm_val v).

Hint Constructors red norm_form.
