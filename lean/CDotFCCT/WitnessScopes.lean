import CDotFCCT.MemberUses
import CTMLCore.Language.TypeBlocks

/-!
# Scoped target names for the source member table

The complete derivation supplies finite support, but a function's local members
are not quantified at the outer scope. External owners are allocated at the root;
entering a binder adds just that owner's member block. Outer members retain their
names under target type weakening. Every recorded use has a name in its own scope.

This module allocates names only. It does not assume that the recorded bounds are
target subtyping facts; constructing and discharging those constraints is separate.
-/

set_option autoImplicit false

namespace CDotFCCT.MemberUses

open CDot CTMLCore

def Scope.Owns (scope : Scope) : Owner → Prop
  | .external _ => True
  | .bound address => address ∈ scope.map Prod.snd

theorem Scope.owns_owner (scope : Scope) (variableName : Var) :
    scope.Owns (scope.owner variableName) := by
  induction scope with
  | nil => trivial
  | cons entry rest ih =>
      rcases entry with ⟨name, address⟩
      by_cases same : variableName = name
      · simp [Scope.owner, same, Owns]
      · simp only [Scope.owner, ite_eq_right same]
        cases equal : Scope.owner rest variableName <;> simp_all [Owns]

variable [Signature]

mutual
  theorem typeKeys_owned (scope : Scope) (type : Typ) :
      ∀ key ∈ typeKeys scope type, scope.Owns key.path.owner :=
    match type with
    | .top | .bot | .sngl _ | .path (.select (.bound _) _) _ =>
        fun _ member => nomatch member
    | .path (.select (.free name) _) _ =>
        List.forall_mem_cons.mpr ⟨scope.owns_owner name, fun _ member => nomatch member⟩
    | .and left right | .all left right =>
        List.forall_mem_append.mpr ⟨typeKeys_owned scope left, typeKeys_owned scope right⟩
    | .bnd body => typeKeys_owned scope body
    | .rcd declaration => decKeys_owned scope declaration

  theorem decKeys_owned (scope : Scope) (declaration : Dec) :
      ∀ key ∈ decKeys scope declaration, scope.Owns key.path.owner :=
    match declaration with
    | .typ _ lower upper =>
        List.forall_mem_append.mpr ⟨typeKeys_owned scope lower, typeKeys_owned scope upper⟩
    | .trm _ body => typeKeys_owned scope body
end

theorem PathKey.ofNamed_owned (scope : Scope) (path : Path) (named : path.Named) :
    scope.Owns (PathKey.ofNamed scope path named).owner :=
  match path with
  | .select (.free variableName) _ => scope.owns_owner variableName
  | .select (.bound _) _ => False.elim (named.elim (fun _ equal => AVar.noConfusion equal))

theorem Event.key_owned {event : Event} {key : MemberKey}
    (found : event.memberKey = some key) : event.scope.Owns key.path.owner := by
  cases event with
  | lower view | upper view =>
      cases found
      exact PathKey.ofNamed_owned view.scope view.path view.source.pathNamed
  | declaration entry =>
      cases found
      exact entry.scope.owns_owner entry.self
  | «alias» equality => cases found
  | binder entry => cases found
  | typeUse use => cases found

theorem Event.support_owned (event : Event) :
    ∀ key ∈ event.support, event.scope.Owns key.path.owner :=
  match event with
  | .typeUse use => typeKeys_owned use.scope use.type
  | .lower view | .upper view =>
      List.forall_mem_cons.mpr
        ⟨PathKey.ofNamed_owned view.scope view.path view.source.pathNamed,
          fun _ member => nomatch member⟩
  | .declaration entry =>
      List.forall_mem_cons.mpr ⟨entry.scope.owns_owner entry.self,
        fun _ member => nomatch member⟩
  | .alias _ | .binder _ => fun _ member => nomatch member

def ownerKeys (events : List Event) (owner : Owner) : List MemberKey :=
  (keys events).filter (fun key => key.path.owner == owner)

def externalKeys (events : List Event) : List MemberKey :=
  (keys events).filter (fun key => match key.path.owner with
    | .external _ => true
    | .bound _ => false)

def visibleKeys (events : List Event) : Scope → List MemberKey
  | [] => externalKeys events
  | (_, address) :: rest => ownerKeys events (.bound address) ++ visibleKeys events rest

theorem mem_visibleKeys {events : List Event} {scope : Scope} {key : MemberKey} :
    key ∈ visibleKeys events scope ↔ key ∈ keys events ∧ scope.Owns key.path.owner := by
  induction scope with
  | nil =>
      cases equal : key.path.owner <;> simp [visibleKeys, externalKeys, Scope.Owns, equal]
  | cons entry rest ih =>
      cases equal : key.path.owner <;>
        simp [visibleKeys, ownerKeys, Scope.Owns, equal, ih, and_or_left]

/-- Every recorded bound or declaration has a target name at the site where it is used. -/
theorem Event.key_visible {events : List Event} {event : Event} {key : MemberKey}
    (member : event ∈ events) (found : event.memberKey = some key) :
    key ∈ visibleKeys events event.scope :=
  mem_visibleKeys.mpr ⟨key_present member found, Event.key_owned found⟩

theorem Event.support_visible {events : List Event} {event : Event} {key : MemberKey}
    (member : event ∈ events) (found : key ∈ event.support) :
    key ∈ visibleKeys events event.scope :=
  mem_visibleKeys.mpr ⟨support_present member found, event.support_owned key found⟩

def scopedSlot (events : List Event) (scope : Scope) (key : MemberKey)
    (present : key ∈ visibleKeys events scope) : Fin (visibleKeys events scope).length :=
  ⟨(visibleKeys events scope).idxOf key, List.idxOf_lt_length_of_mem present⟩

def scopedWitness (events : List Event) (scope : Scope) (key : MemberKey)
    (present : key ∈ visibleKeys events scope) : WFTy (visibleKeys events scope).length :=
  WFTy.var (scopedSlot events scope key present) (scopedSlot events scope key present).isLt

theorem scopedSlot_injective {events : List Event} {scope : Scope} {left right : MemberKey}
    (leftPresent : left ∈ visibleKeys events scope)
    (rightPresent : right ∈ visibleKeys events scope)
    (equal : scopedSlot events scope left leftPresent =
      scopedSlot events scope right rightPresent) : left = right :=
  (List.idxOf_inj leftPresent).mp (congrArg Fin.val equal)

theorem scopedWitness_injective {events : List Event} {scope : Scope} {left right : MemberKey}
    (leftPresent : left ∈ visibleKeys events scope)
    (rightPresent : right ∈ visibleKeys events scope)
    (equal : scopedWitness events scope left leftPresent =
      scopedWitness events scope right rightPresent) : left = right :=
  (List.idxOf_inj leftPresent).mp (Syntax.Ty.var.inj (congrArg WFTy.raw equal))

theorem visibleKeys_bind_length (events : List Event) (scope : Scope) (name : Var)
    (address : Address) : (visibleKeys events (scope.bind name address)).length =
      (visibleKeys events scope).length + (ownerKeys events (.bound address)).length := by
  simp [visibleKeys, Scope.bind, Nat.add_comm]

theorem visibleKeys_bind {events : List Event} {scope : Scope} {key : MemberKey}
    (present : key ∈ visibleKeys events scope) (name : Var) (address : Address) :
    key ∈ visibleKeys events (scope.bind name address) := List.mem_append_right _ present

theorem ownerKeys_not_mem {events : List Event} {owner : Owner} {key : MemberKey}
    (different : key.path.owner ≠ owner) : key ∉ ownerKeys events owner := by
  simp [ownerKeys, different]

theorem visibleKey_other_owner {events : List Event} {scope : Scope} {key : MemberKey}
    (present : key ∈ visibleKeys events scope) {address : Address}
    (fresh : address ∉ scope.map Prod.snd) : key.path.owner ≠ .bound address := by
  intro equal
  exact fresh (Eq.mp (congrArg scope.Owns equal) (mem_visibleKeys.mp present).2)

/-- A fresh binder's witnesses cannot be used in the parent's target type scope. -/
theorem fresh_owner_not_visible {events : List Event} {scope : Scope} {key : MemberKey}
    {address : Address} (fresh : address ∉ scope.map Prod.snd)
    (owned : key.path.owner = .bound address) : key ∉ visibleKeys events scope :=
  fun present => visibleKey_other_owner present fresh owned

/-- Entering a fresh owner's scope performs the usual target type-variable weakening. -/
theorem scopedWitness_bind {events : List Event} {scope : Scope} {key : MemberKey}
    (present : key ∈ visibleKeys events scope) (name : Var) (address : Address)
    (different : key.path.owner ≠ .bound address) :
    WFTy.castDepth (visibleKeys_bind_length events scope name address)
      (scopedWitness events (scope.bind name address) key
        (visibleKeys_bind present name address)) =
    (scopedWitness events scope key present).weakenBy
      (ownerKeys events (.bound address)).length := by
  apply WFTy.eq_of_raw_eq
  rw [WFTy.raw_castDepth]
  simp [scopedWitness, scopedSlot, visibleKeys, Scope.bind, WFTy.var, WFTy.weakenBy,
    Syntax.Ty.lift, List.idxOf_append, ownerKeys_not_mem different]

theorem scopedWitness_bind_fresh {events : List Event} {scope : Scope} {key : MemberKey}
    (present : key ∈ visibleKeys events scope) (name : Var) (address : Address)
    (fresh : address ∉ scope.map Prod.snd) :
    WFTy.castDepth (visibleKeys_bind_length events scope name address)
      (scopedWitness events (scope.bind name address) key
        (visibleKeys_bind present name address)) =
    (scopedWitness events scope key present).weakenBy (ownerKeys events (.bound address)).length :=
  scopedWitness_bind present name address (visibleKey_other_owner present fresh)

end CDotFCCT.MemberUses
