import CDotFCCT.MemberScopeSafety
import CDotFCCT.CTML.Coercions

/-!
# Native witness equations generated from scoped source aliases

For each recorded singleton equality, this pass finds matching member references
in the finite support. It includes common field extensions, so `p = q` relates
`p.child.A` and `q.child.A`. Each emitted equation retains the source equality and
its two source subtyping derivations. Equations are emitted only at that equality's
scope; they do not identify witnesses in an enclosing scope.

The pass constructs native subtyping and identity-coercion derivations under its
generated guards. Discharging the guards is a separate obligation of the package
constructor; this module does not assume that arbitrary aliases can be equated in
an empty target context.
-/

set_option autoImplicit false

namespace CDotFCCT.MemberUses

open CDot CTMLCore

variable [Signature]

def PathKey.selectFields (path : PathKey) (fields : Fields) : PathKey :=
  ⟨path.owner, fields ++ path.fields⟩

def Alias.leftMember (equality : Alias) (fields : Fields) (label : Signature.TypLabel) :
    MemberKey := ⟨equality.leftKey.selectFields fields, label⟩

def Alias.rightMember (equality : Alias) (fields : Fields) (label : Signature.TypLabel) :
    MemberKey := ⟨equality.rightKey.selectFields fields, label⟩

theorem PathKey.ofNamed_selectFields (scope : Scope) (path : Path) (named : path.Named)
    (fields : Fields) :
    PathKey.ofNamed scope (path.selectFields fields) (named.selectFields fields) =
      (PathKey.ofNamed scope path named).selectFields fields :=
  match path with
  | .select (.free _) _ => rfl
  | .select (.bound _) _ => False.elim (named.elim (fun _ equal => AVar.noConfusion equal))

namespace AliasConstraints

structure Entry (events : List Event) (scope : Scope) where
  equality : Alias
  occurs : Event.alias equality ∈ events
  atScope : equality.scope = scope
  fields : Fields
  label : Signature.TypLabel
  leftPresent : equality.leftMember fields label ∈ visibleKeys events scope
  rightPresent : equality.rightMember fields label ∈ visibleKeys events scope

def Entry.left {events : List Event} {scope : Scope} (entry : Entry events scope) :
    WFTy (visibleKeys events scope).length :=
  scopedWitness events scope (entry.equality.leftMember entry.fields entry.label) entry.leftPresent

def Entry.right {events : List Event} {scope : Scope} (entry : Entry events scope) :
    WFTy (visibleKeys events scope).length :=
  scopedWitness events scope (entry.equality.rightMember entry.fields entry.label)
    entry.rightPresent

def Entry.guards {events : List Event} {scope : Scope} (entry : Entry events scope) :
    List (WFConstraint (visibleKeys events scope).length) :=
  [WFConstraint.constr entry.left entry.right, WFConstraint.constr entry.right entry.left]

theorem Entry.source {events : List Event} {scope : Scope} (entry : Entry events scope) :
    Subtyp entry.equality.context
      (.path (entry.equality.left.selectFields entry.fields) entry.label)
      (.path (entry.equality.right.selectFields entry.fields) entry.label) ∧
    Subtyp entry.equality.context
      (.path (entry.equality.right.selectFields entry.fields) entry.label)
      (.path (entry.equality.left.selectFields entry.fields) entry.label) :=
  ⟨entry.equality.memberSubtype entry.fields entry.label,
    entry.equality.memberSupertype entry.fields entry.label⟩

/-- A successful candidate checks both the field suffix and the two available names. -/
def candidate (events : List Event) (scope : Scope) (equality : Alias)
    (occurs : Event.alias equality ∈ events) (atScope : equality.scope = scope)
    (key : MemberKey) : Option (Entry events scope) :=
  let fields := key.path.fields.take (key.path.fields.length - equality.leftKey.fields.length)
  if equality.leftMember fields key.label = key then
    if leftPresent : equality.leftMember fields key.label ∈ visibleKeys events scope then
      if rightPresent : equality.rightMember fields key.label ∈ visibleKeys events scope then
        some ⟨equality, occurs, atScope, fields, key.label, leftPresent, rightPresent⟩
      else none
    else none
  else none

def generate (events : List Event) (scope : Scope) : List (Entry events scope) :=
  events.attach.flatMap (fun ⟨event, occurs⟩ =>
    match event, occurs with
    | .alias equality, occurs =>
        if atScope : equality.scope = scope then
          (visibleKeys events scope).filterMap (candidate events scope equality occurs atScope)
        else []
    | _, _ => [])

theorem candidate_exact {events : List Event} {scope : Scope} {equality : Alias}
    (occurs : Event.alias equality ∈ events) (atScope : equality.scope = scope)
    (fields : Fields) (label : Signature.TypLabel)
    (leftPresent : equality.leftMember fields label ∈ visibleKeys events scope)
    (rightPresent : equality.rightMember fields label ∈ visibleKeys events scope) :
    candidate events scope equality occurs atScope (equality.leftMember fields label) =
      some ⟨equality, occurs, atScope, fields, label, leftPresent, rightPresent⟩ := by
  have suffix : (equality.leftMember fields label).path.fields.take
      ((equality.leftMember fields label).path.fields.length - equality.leftKey.fields.length) =
      fields := by
    simp [Alias.leftMember, PathKey.selectFields]
  simp [candidate, suffix, show (equality.leftMember fields label).label = label from rfl,
    leftPresent, rightPresent]

/-- Every common field extension whose two names are in scope is emitted. -/
theorem generate_complete {events : List Event} {scope : Scope} {equality : Alias}
    (occurs : Event.alias equality ∈ events) (atScope : equality.scope = scope)
    (fields : Fields) (label : Signature.TypLabel)
    (leftPresent : equality.leftMember fields label ∈ visibleKeys events scope)
    (rightPresent : equality.rightMember fields label ∈ visibleKeys events scope) :
    (⟨equality, occurs, atScope, fields, label, leftPresent, rightPresent⟩ : Entry events scope) ∈
      generate events scope := by
  unfold generate
  refine List.mem_flatMap.mpr ⟨⟨.alias equality, occurs⟩, List.mem_attach _ _, ?_⟩
  simp only [dite_eq_left atScope]
  exact List.mem_filterMap.mpr ⟨equality.leftMember fields label, leftPresent,
    candidate_exact occurs atScope fields label leftPresent rightPresent⟩

def guards (events : List Event) (scope : Scope) :
    List (WFConstraint (visibleKeys events scope).length) :=
  (generate events scope).flatMap Entry.guards

def context (events : List Event) (scope : Scope) : SubtypingContext :=
  CTML.assumeMany ⟨(visibleKeys events scope).length, []⟩ (guards events scope)

theorem Entry.forward {events : List Event} {scope : Scope} {entry : Entry events scope}
    (present : entry ∈ generate events scope) :
    Subtype (context events scope) entry.left entry.right :=
  CTML.assumedGuard (subtyping := ⟨(visibleKeys events scope).length, []⟩)
    (guards := AliasConstraints.guards events scope)
    (guard := WFConstraint.constr entry.left entry.right)
    (List.mem_flatMap.mpr ⟨entry, present, List.mem_cons_self⟩)

theorem Entry.backward {events : List Event} {scope : Scope} {entry : Entry events scope}
    (present : entry ∈ generate events scope) :
    Subtype (context events scope) entry.right entry.left :=
  CTML.assumedGuard (subtyping := ⟨(visibleKeys events scope).length, []⟩)
    (guards := AliasConstraints.guards events scope)
    (guard := WFConstraint.constr entry.right entry.left)
    (List.mem_flatMap.mpr ⟨entry, present, List.mem_cons_of_mem _ List.mem_cons_self⟩)

theorem Entry.coercionTyping {events : List Event} {scope : Scope} {entry : Entry events scope}
    (present : entry ∈ generate events scope) (answer : WFTy (visibleKeys events scope).length) :
    HasType (context events scope) TypingContext.empty CTML.Coercion.identity
      (CTML.Coercion.type entry.left entry.right answer) :=
  CTML.Coercion.identityTyping _ (Entry.forward present)

theorem Entry.guardedCoercionTyping {events : List Event} {scope : Scope}
    {entry : Entry events scope} (present : entry ∈ generate events scope)
    (answer : WFTy (visibleKeys events scope).length) :
    HasType ⟨(visibleKeys events scope).length, []⟩ TypingContext.empty CTML.Coercion.identity
      (CTML.qualify (AliasConstraints.guards events scope)
        (CTML.Coercion.type entry.left entry.right answer)) :=
  CTML.qualifyTyping (AliasConstraints.guards events scope) (.value (.abs _))
    (Entry.coercionTyping present answer)

structure Compiled (events : List Event) (scope : Scope)
    (answer : WFTy (visibleKeys events scope).length) where
  entry : Entry events scope
  typing : HasType ⟨(visibleKeys events scope).length, []⟩ TypingContext.empty
    CTML.Coercion.identity (CTML.qualify (guards events scope)
      (CTML.Coercion.type entry.left entry.right answer))

/-- The source trace and an answer type suffice to produce the guarded target derivations. -/
def compile (events : List Event) (scope : Scope)
    (answer : WFTy (visibleKeys events scope).length) : List (Compiled events scope answer) :=
  (generate events scope).attach.map (fun entry =>
    ⟨entry.val, Entry.guardedCoercionTyping entry.property answer⟩)

end AliasConstraints

end CDotFCCT.MemberUses
