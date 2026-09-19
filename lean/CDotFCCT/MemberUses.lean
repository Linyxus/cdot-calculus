import CDotFCCT.CoreSyntax
import CDot.Weakening
import CTMLCore.Language.WellFormed
import Mathlib.Data.List.Basic

/-!
# Scoped member uses in a full core-DOT derivation

This source analysis visits every core rule, including its typing, definition,
and subtyping premises. It chooses a fresh representative at each cofinite binder.
Binder identities are positions in the derivation tree, so unrelated binders do
not become the same owner just because their source representatives have the
same numeric name. Nested objects keep their enclosing owner's field path.

Each bound use and singleton equality retains its actual source context and
source proof. Bounds on the same path and label share a key, including when
different upper bounds expose that path through an opaque member. Equalities
remain scoped facts: this pass never globally merges owners using an equality
that may depend on a function's hypothetical argument.

The resulting finite table allocates one slot per distinct member key. This is
source analysis for the general translation, not a proof that its target guards
can be discharged or that independently opened existential packages can be fused.
-/

set_option autoImplicit false

namespace CDotFCCT.MemberUses

open CDot

abbrev Address := List Nat

inductive Owner where
  | external (variableName : Var)
  | bound (binder : Address)
  deriving DecidableEq

abbrev Scope := List (Var × Address)

def Scope.owner : Scope → Var → Owner
  | [], variableName => .external variableName
  | (name, address) :: rest, variableName =>
      if variableName = name then .bound address else owner rest variableName

def Scope.bind (scope : Scope) (variableName : Var) (address : Address) : Scope :=
  (variableName, address) :: scope

theorem Scope.owner_bound (scope : Scope) (variableName : Var) (address : Address) :
    (scope.bind variableName address).owner variableName = .bound address := by
  simp [Scope.bind, Scope.owner]

theorem Scope.owner_other (scope : Scope) {variableName bound : Var}
    (different : variableName ≠ bound) (address : Address) :
    (scope.bind bound address).owner variableName = scope.owner variableName := by
  simp [Scope.bind, Scope.owner, different]

variable [Signature]

structure PathKey where
  owner : Owner
  fields : Fields
  deriving DecidableEq

def PathKey.ofNamed (scope : Scope) (path : Path) (named : path.Named) : PathKey :=
  match path with
  | .select (.free variableName) fields => ⟨scope.owner variableName, fields⟩
  | .select (.bound _) _ => False.elim (named.elim (fun _ equal => AVar.noConfusion equal))

structure MemberKey where
  path : PathKey
  label : Signature.TypLabel
  deriving DecidableEq

mutual
  /-- Free selections need names even when no bound-selection rule is used. Bound
  paths are handled after the corresponding source binder is opened. -/
  def typeKeys (scope : Scope) : Typ → List MemberKey
    | .top | .bot | .sngl _ => []
    | .path (.select (.free name) fields) label => [⟨⟨scope.owner name, fields⟩, label⟩]
    | .path (.select (.bound _) _) _ => []
    | .and left right | .all left right => typeKeys scope left ++ typeKeys scope right
    | .bnd body => typeKeys scope body
    | .rcd declaration => decKeys scope declaration

  def decKeys (scope : Scope) : Dec → List MemberKey
    | .typ _ lower upper => typeKeys scope lower ++ typeKeys scope upper
    | .trm _ body => typeKeys scope body
end

structure TypeUse where
  scope : Scope
  context : Ctx
  type : Typ

structure View where
  scope : Scope
  context : Ctx
  path : Path
  label : Signature.TypLabel
  lower : Typ
  upper : Typ
  source : Typed context (.path path) (.rcd (.typ label lower upper))

def View.key (view : View) : MemberKey :=
  ⟨PathKey.ofNamed view.scope view.path view.source.pathNamed, view.label⟩

def View.ofTyping (scope : Scope) {context : Ctx} {path : Path}
    {label : Signature.TypLabel} {lower upper : Typ}
    (typing : Core.Typing context (.path path) (.rcd (.typ label lower upper))) : View :=
  ⟨scope, context, path, label, lower, upper, typing.source⟩

/-- A bound's endpoints and the proof exposing them do not choose its witness. -/
theorem View.same_key (scope : Scope) {firstContext secondContext : Ctx} {path : Path}
    {label : Signature.TypLabel} {firstLower firstUpper secondLower secondUpper : Typ}
    (first : Core.Typing firstContext (.path path) (.rcd (.typ label firstLower firstUpper)))
    (second : Core.Typing secondContext (.path path) (.rcd (.typ label secondLower secondUpper))) :
    (View.ofTyping scope first).key = (View.ofTyping scope second).key := rfl

structure Alias where
  scope : Scope
  context : Ctx
  left : Path
  right : Path
  source : Typed context (.path left) (.sngl right)
  rightType : Typ
  rightSource : Typed context (.path right) rightType

def Alias.rightNamed (equality : Alias) : equality.right.Named := equality.rightSource.pathNamed

def Alias.leftKey (equality : Alias) : PathKey :=
  PathKey.ofNamed equality.scope equality.left equality.source.pathNamed

def Alias.rightKey (equality : Alias) : PathKey :=
  PathKey.ofNamed equality.scope equality.right equality.rightNamed

def Alias.ofTyping (scope : Scope) {context : Ctx} {left right : Path} {type : Typ}
    (equality : Core.Typing context (.path left) (.sngl right))
    (value : Core.Typing context (.path right) type) : Alias :=
  ⟨scope, context, left, right, equality.source, type, value.source⟩

theorem Alias.memberSubtype (equality : Alias) (fields : Fields) (label : Signature.TypLabel) :
    Subtyp equality.context (.path (equality.left.selectFields fields) label)
      (.path (equality.right.selectFields fields) label) :=
  .snglPQ equality.source equality.rightSource .path

theorem Alias.memberSupertype (equality : Alias) (fields : Fields) (label : Signature.TypLabel) :
    Subtyp equality.context (.path (equality.right.selectFields fields) label)
      (.path (equality.left.selectFields fields) label) :=
  .snglQP equality.source equality.rightSource .path

structure Declaration where
  scope : Scope
  context : Ctx
  self : Var
  fields : Fields
  label : Signature.TypLabel
  body : Typ
  source : TypedDef self fields context (.typ label body) (.typ label body body)

def Declaration.key (declaration : Declaration) : MemberKey :=
  ⟨⟨declaration.scope.owner declaration.self, declaration.fields⟩, declaration.label⟩

def Declaration.ofTyping (scope : Scope) {context : Ctx} {self : Var} {fields : Fields}
    {label : Signature.TypLabel} {body : Typ}
    (typing : Core.DefinitionTyping self fields context (.typ label body) (.typ label body body)) :
    Declaration := ⟨scope, context, self, fields, label, body, typing.source⟩

inductive BinderKind where
  | functionArgument
  | objectSelf
  | letValue
  | subtypingArgument
  deriving DecidableEq

structure Binder where
  kind : BinderKind
  address : Address
  scope : Scope
  context : Ctx
  variableName : Var
  fresh : variableName ∉ context.dom

inductive Event where
  | lower (view : View)
  | upper (view : View)
  | declaration (declaration : Declaration)
  | alias (equality : Alias)
  | binder (binder : Binder)
  | typeUse (use : TypeUse)

def Event.memberKey : Event → Option MemberKey
  | .lower view | .upper view => some view.key
  | .declaration entry => some entry.key
  | .alias _ | .binder _ | .typeUse _ => none

def Event.support : Event → List MemberKey
  | .typeUse use => typeKeys use.scope use.type
  | event => event.memberKey.toList

def Event.scope : Event → Scope
  | .lower view | .upper view => view.scope
  | .declaration entry => entry.scope
  | .alias equality => equality.scope
  | .binder entry => entry.scope
  | .typeUse use => use.scope

def Event.context : Event → Ctx
  | .lower view | .upper view => view.context
  | .declaration entry => entry.context
  | .alias equality => equality.context
  | .binder entry => entry.context
  | .typeUse use => use.context

def representative (excluded extra : Vars) : Var := Core.fresh (excluded ∪ extra)

omit [Signature] in
theorem representative_fresh (excluded extra : Vars) :
    representative excluded extra ∉ excluded :=
  fun member => Core.fresh_not_mem _ (Finset.mem_union_left _ member)

omit [Signature] in
theorem representative_extra (excluded extra : Vars) :
    representative excluded extra ∉ extra :=
  fun member => Core.fresh_not_mem _ (Finset.mem_union_right _ member)

def binder (kind : BinderKind) (address : Address) (scope : Scope) (context : Ctx)
    (excluded extra : Vars) : Binder :=
  ⟨kind, address, scope, context, representative excluded (context.dom ∪ extra),
    fun member => representative_extra _ _ (Finset.mem_union_left _ member)⟩

/-- A path used only as a judgment's subject still needs a shared carrier node. -/
def subjectUse (scope : Scope) (context : Ctx) : Trm → List Event
  | .path path => [.typeUse ⟨scope, context, .sngl path⟩]
  | _ => []

mutual
  /-- Traverse the complete input judgment; no core constructor is rejected. -/
  def typing {context : Ctx} {term : Trm} {type : Typ}
      (derivation : Core.Typing context term type) (scope : Scope) (address : Address) :
      List Event :=
    .typeUse ⟨scope, context, type⟩ :: subjectUse scope context term ++
    match derivation with
    | .var _ => []
    | .allIntro excluded body =>
        let bound := binder .functionArgument address scope context excluded
          (context.fvTypes ∪ term.fv ∪ type.fv)
        .binder bound :: typing (body bound.variableName (representative_fresh _ _))
          (scope.bind bound.variableName address) (address ++ [0])
    | .allElim function argument =>
        typing function scope (address ++ [0]) ++ typing argument scope (address ++ [1])
    | .newIntro excluded fields tag =>
        let bound := binder .objectSelf address scope context excluded
          (context.fvTypes ∪ term.fv ∪ type.fv)
        .binder bound ::
          (definitions (fields bound.variableName (representative_fresh _ _))
            (scope.bind bound.variableName address) (address ++ [0]) ++
          typing (tag bound.variableName (representative_fresh _ _))
            (scope.bind bound.variableName address) (address ++ [1]))
    | .newElim object | .rcdIntro object => typing object scope (address ++ [0])
    | .letE excluded rhs body =>
        let bound := binder .letValue address scope context excluded
          (context.fvTypes ∪ term.fv ∪ type.fv)
        typing rhs scope (address ++ [0]) ++ .binder bound ::
          typing (body bound.variableName (representative_fresh _ _))
            (scope.bind bound.variableName address) (address ++ [1])
    | .sngl equality value =>
        .alias (Alias.ofTyping scope equality value) ::
          (typing equality scope (address ++ [0]) ++ typing value scope (address ++ [1]))
    | .self value => typing value scope (address ++ [0])
    | .pathElim equality field =>
        .alias ⟨scope, _, _, _, equality.source, _, .rcdIntro field.source⟩ ::
          (typing equality scope (address ++ [0]) ++ typing field scope (address ++ [1]))
    | .recIntro value | .recElim value => typing value scope (address ++ [0])
    | .andIntro left right =>
        typing left scope (address ++ [0]) ++ typing right scope (address ++ [1])
    | .sub value subtype =>
        typing value scope (address ++ [0]) ++ subtyping subtype scope (address ++ [1])

  def definition {self : Var} {fields : Fields} {context : Ctx} {field : Def} {type : Dec}
      (derivation : Core.DefinitionTyping self fields context field type)
      (scope : Scope) (address : Address) : List Event :=
    .typeUse ⟨scope, context, .rcd type⟩ ::
    match derivation with
    | @Core.DefinitionTyping.typ _ self fields context label body =>
        [.declaration ⟨scope, context, self, fields, label, body, .typ⟩]
    | .all function => typing function scope (address ++ [0])
    | .new _ _ _ fields tag =>
        definitions fields scope (address ++ [0]) ++ typing tag scope (address ++ [1])
    | .path value => typing value scope (address ++ [0])

  def definitions {self : Var} {fields : Fields} {context : Ctx} {values : Defs} {type : Typ}
      (derivation : Core.DefinitionsTyping self fields context values type)
      (scope : Scope) (address : Address) : List Event :=
    .typeUse ⟨scope, context, type⟩ ::
    match derivation with
    | .one field => definition field scope (address ++ [0])
    | .cons earlier field _ =>
        definitions earlier scope (address ++ [0]) ++ definition field scope (address ++ [1])

  def subtyping {context : Ctx} {left right : Typ}
      (derivation : Core.Subtyping context left right) (scope : Scope) (address : Address) :
      List Event :=
    .typeUse ⟨scope, context, .and left right⟩ ::
    match derivation with
    | .top | .bot | .refl | .andLeft | .andRight => []
    | .trans first second | .andIntro first second | .typ first second =>
        subtyping first scope (address ++ [0]) ++ subtyping second scope (address ++ [1])
    | .fld field => subtyping field scope (address ++ [0])
    | .snglPQ equality value _ | .snglQP equality value _ =>
        .alias (Alias.ofTyping scope equality value) ::
          (typing equality scope (address ++ [0]) ++ typing value scope (address ++ [1]))
    | .selLo member =>
        .lower (View.ofTyping scope member) :: typing member scope (address ++ [0])
    | .selHi member =>
        .upper (View.ofTyping scope member) :: typing member scope (address ++ [0])
    | .all excluded param result =>
        let bound := binder .subtypingArgument address scope context excluded
          (context.fvTypes ∪ left.fv ∪ right.fv)
        subtyping param scope (address ++ [0]) ++ .binder bound ::
          subtyping (result bound.variableName (representative_fresh _ _))
            (scope.bind bound.variableName address) (address ++ [1])
end

def keys (events : List Event) : List MemberKey := (events.flatMap Event.support).eraseDups

def slot (events : List Event) (key : MemberKey) (present : key ∈ keys events) :
    Fin (keys events).length :=
  ⟨(keys events).idxOf key, List.idxOf_lt_length_of_mem present⟩

theorem slot_injective {events : List Event} {left right : MemberKey}
    (leftPresent : left ∈ keys events) (rightPresent : right ∈ keys events)
    (equal : slot events left leftPresent = slot events right rightPresent) : left = right :=
  (List.idxOf_inj leftPresent).mp (congrArg Fin.val equal)

/-- All occurrences of one key use the same slot; a new slot is never chosen per use. -/
def witness (events : List Event) (key : MemberKey) (present : key ∈ keys events) :
    CTMLCore.WFTy (keys events).length :=
  CTMLCore.WFTy.var (slot events key present) (slot events key present).isLt

theorem support_present {events : List Event} {event : Event} {key : MemberKey}
    (member : event ∈ events) (found : key ∈ event.support) : key ∈ keys events :=
  List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨event, member, found⟩)

theorem Event.member_supported {event : Event} {key : MemberKey}
    (found : event.memberKey = some key) : key ∈ event.support := by
  cases event <;> simp_all [Event.memberKey, Event.support]

theorem key_present {events : List Event} {event : Event} {key : MemberKey}
    (member : event ∈ events) (found : event.memberKey = some key) : key ∈ keys events :=
  support_present member (Event.member_supported found)

/-- Facts established under a binder are not assumptions at its parent scope. -/
def localEvents (events : List Event) (scope : Scope) : List Event :=
  events.filter (fun event => event.scope == scope)

theorem mem_localEvents {events : List Event} {scope : Scope} {event : Event} :
    event ∈ localEvents events scope ↔ event ∈ events ∧ event.scope = scope := by
  simp [localEvents]

theorem localEvents_scope {events : List Event} {scope : Scope} {event : Event}
    (member : event ∈ localEvents events scope) : event.scope = scope :=
  (mem_localEvents.mp member).2

end CDotFCCT.MemberUses
