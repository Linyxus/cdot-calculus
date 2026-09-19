import CDotFCCT.WitnessScopes

/-!
# Fresh witness scopes throughout the source derivation

Derivation addresses provide fresh binder identities for every chosen cofinite
premise. This invariant is proved for the full traversal, so the freshness premise
of target witness weakening need not be supplied by a caller of the analysis.
-/

set_option autoImplicit false

namespace CDotFCCT.MemberUses

open CDot

structure Scope.Before (scope : Scope) (address : Address) : Prop where
  unique : (scope.map Prod.snd).Nodup
  earlier : ∀ origin ∈ scope.map Prod.snd, origin.length < address.length

theorem Scope.Before.empty (address : Address) : Scope.Before [] address :=
  ⟨List.nodup_nil, fun _ member => nomatch member⟩

theorem Scope.Before.fresh {scope : Scope} {address : Address}
    (before : scope.Before address) : address ∉ scope.map Prod.snd :=
  fun member => Nat.lt_irrefl _ (before.earlier _ member)

theorem Scope.Before.child {scope : Scope} {address : Address}
    (before : scope.Before address) (branch : Nat) : scope.Before (address ++ [branch]) := by
  refine ⟨before.unique, fun origin member => ?_⟩
  simpa only [List.length_append, List.length_singleton] using
    Nat.lt_succ_of_lt (before.earlier origin member)

theorem Scope.Before.enter {scope : Scope} {address : Address}
    (before : scope.Before address) (name : Var) (branch : Nat) :
    (scope.bind name address).Before (address ++ [branch]) := by
  refine ⟨List.nodup_cons.mpr ⟨before.fresh, before.unique⟩, ?_⟩
  simp only [Scope.bind, List.map_cons, List.mem_cons, List.length_append, List.length_singleton]
  exact fun origin member => member.elim (fun equal => equal ▸ Nat.lt_succ_self _)
    (fun inherited => Nat.lt_succ_of_lt (before.earlier origin inherited))

variable [Signature]

def Event.FreshBinder : Event → Prop
  | .binder entry => entry.address ∉ entry.scope.map Prod.snd
  | _ => True

def Event.Valid (event : Event) : Prop :=
  (event.scope.map Prod.snd).Nodup ∧ event.FreshBinder

def ValidEvents (events : List Event) : Prop := ∀ event ∈ events, event.Valid

theorem ValidEvents.nil : ValidEvents ([] : List Event) := fun _ member => nomatch member

theorem ValidEvents.cons {event : Event} {events : List Event}
    (head : event.Valid) (tail : ValidEvents events) : ValidEvents (event :: events) :=
  List.forall_mem_cons.mpr ⟨head, tail⟩

theorem ValidEvents.append {first second : List Event}
    (left : ValidEvents first) (right : ValidEvents second) : ValidEvents (first ++ second) :=
  List.forall_mem_append.mpr ⟨left, right⟩

theorem subjectUse_valid {scope : Scope} (context : Ctx) (term : Trm)
    (unique : (scope.map Prod.snd).Nodup) : ValidEvents (subjectUse scope context term) :=
  match term with
  | .path _ => ValidEvents.cons ⟨unique, trivial⟩ ValidEvents.nil
  | .val _ | .app _ _ | .letE _ _ | .caseE _ _ _ _ _ => ValidEvents.nil

mutual
  theorem typing_valid {context : Ctx} {term : Trm} {type : Typ}
      (derivation : Core.Typing context term type) {scope : Scope} {address : Address}
      (before : scope.Before address) : ValidEvents (typing derivation scope address) := by
    rw [typing.eq_def]
    refine ValidEvents.cons ⟨before.unique, trivial⟩ ?_
    refine (subjectUse_valid context term before.unique).append ?_
    exact match derivation with
    | .var _ => ValidEvents.nil
    | .allIntro excluded body => by
        refine ValidEvents.cons ⟨before.unique, before.fresh⟩ ?_
        exact typing_valid _ (before.enter _ 0)
    | .allElim function argument =>
        (typing_valid function (before.child 0)).append (typing_valid argument (before.child 1))
    | .newIntro excluded fields tag => by
        refine ValidEvents.cons ⟨before.unique, before.fresh⟩ ?_
        exact (definitions_valid _ (before.enter _ 0)).append (typing_valid _ (before.enter _ 1))
    | .newElim object | .rcdIntro object => typing_valid object (before.child 0)
    | .letE excluded rhs body => by
        refine (typing_valid rhs (before.child 0)).append
          (ValidEvents.cons ⟨before.unique, before.fresh⟩ ?_)
        exact typing_valid _ (before.enter _ 1)
    | .sngl equality value =>
        ValidEvents.cons ⟨before.unique, trivial⟩
          ((typing_valid equality (before.child 0)).append (typing_valid value (before.child 1)))
    | .self value => typing_valid value (before.child 0)
    | .pathElim equality field =>
        ValidEvents.cons ⟨before.unique, trivial⟩
          ((typing_valid equality (before.child 0)).append (typing_valid field (before.child 1)))
    | .recIntro value | .recElim value => typing_valid value (before.child 0)
    | .andIntro left right =>
        (typing_valid left (before.child 0)).append (typing_valid right (before.child 1))
    | .sub value subtype =>
        (typing_valid value (before.child 0)).append (subtyping_valid subtype (before.child 1))

  theorem definition_valid {self : Var} {fields : Fields} {context : Ctx} {field : Def} {type : Dec}
      (derivation : Core.DefinitionTyping self fields context field type)
      {scope : Scope} {address : Address} (before : scope.Before address) :
      ValidEvents (definition derivation scope address) := by
    rw [definition.eq_def]
    refine ValidEvents.cons ⟨before.unique, trivial⟩ ?_
    exact match derivation with
    | .typ => ValidEvents.cons ⟨before.unique, trivial⟩ ValidEvents.nil
    | .all function => typing_valid function (before.child 0)
    | .new _ _ _ fields tag =>
        (definitions_valid fields (before.child 0)).append (typing_valid tag (before.child 1))
    | .path value => typing_valid value (before.child 0)

  theorem definitions_valid {self : Var} {fields : Fields} {context : Ctx}
      {values : Defs} {type : Typ}
      (derivation : Core.DefinitionsTyping self fields context values type)
      {scope : Scope} {address : Address} (before : scope.Before address) :
      ValidEvents (definitions derivation scope address) := by
    rw [definitions.eq_def]
    refine ValidEvents.cons ⟨before.unique, trivial⟩ ?_
    exact match derivation with
    | .one field => definition_valid field (before.child 0)
    | .cons earlier field _ =>
        (definitions_valid earlier (before.child 0)).append
          (definition_valid field (before.child 1))

  theorem subtyping_valid {context : Ctx} {left right : Typ}
      (derivation : Core.Subtyping context left right) {scope : Scope} {address : Address}
      (before : scope.Before address) : ValidEvents (subtyping derivation scope address) := by
    rw [subtyping.eq_def]
    refine ValidEvents.cons ⟨before.unique, trivial⟩ ?_
    exact match derivation with
    | .top | .bot | .refl | .andLeft | .andRight => ValidEvents.nil
    | .trans first second | .andIntro first second | .typ first second =>
        (subtyping_valid first (before.child 0)).append (subtyping_valid second (before.child 1))
    | .fld field => subtyping_valid field (before.child 0)
    | .snglPQ equality value _ | .snglQP equality value _ =>
        ValidEvents.cons ⟨before.unique, trivial⟩
          ((typing_valid equality (before.child 0)).append (typing_valid value (before.child 1)))
    | .selLo member | .selHi member =>
        ValidEvents.cons ⟨before.unique, trivial⟩ (typing_valid member (before.child 0))
    | .all excluded param result => by
        refine (subtyping_valid param (before.child 0)).append
          (ValidEvents.cons ⟨before.unique, before.fresh⟩ ?_)
        exact subtyping_valid _ (before.enter _ 1)
end

theorem typing_scopes {context : Ctx} {term : Trm} {type : Typ}
    (derivation : Core.Typing context term type) : ValidEvents (typing derivation [] []) :=
  typing_valid derivation (.empty [])

theorem subtyping_scopes {context : Ctx} {left right : Typ}
    (derivation : Core.Subtyping context left right) : ValidEvents (subtyping derivation [] []) :=
  subtyping_valid derivation (.empty [])

end CDotFCCT.MemberUses
