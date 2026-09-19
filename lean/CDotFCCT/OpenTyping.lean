import CDotFCCT.OpenTypes
import CDotFCCT.CTML.Records

/-!
# Proof-producing translation of the opened path fragment

The input is data describing DOT rules, with an erasure theorem into the actual
source judgment. Its target proof uses CTML Core's existing rules. In particular,
the same translated path is used by both premises of intersection introduction.
The context of member witnesses is shared across the entire derivation.
-/

set_option autoImplicit false

namespace CDotFCCT.OpenCore

open CTMLCore

variable [CDot.Signature]

abbrev Context := List (CDot.Var × Typ)

def Context.source (context : Context) : CDot.Ctx :=
  context.map (fun entry => (entry.1, entry.2.source))

def Context.translate {n : Nat} (w : Witnesses n) (context : Context) : TypingContext n :=
  ⟨context.map (fun entry => entry.2.translate w)⟩

/-- The same deterministic name resolution is used by every typing of a path. -/
def Context.index (x : CDot.Var) : Context → Nat
  | [] => 0
  | (y, _) :: rest => if x = y then 0 else 1 + Context.index x rest

inductive Lookup : Context → CDot.Var → Typ → Type where
  | here {context x type} : Lookup ((x, type) :: context) x type
  | there {context x y type other} :
      x ≠ y → Lookup context x type → Lookup ((y, other) :: context) x type

theorem Lookup.source {context : Context} {x : CDot.Var} {type : Typ}
    (lookup : Lookup context x type) : CDot.Env.Binds x type.source context.source :=
  match lookup with
  | .here => .here
  | .there different rest => .there different rest.source

theorem Lookup.translate {n : Nat} (w : Witnesses n)
    {context : Context} {x : CDot.Var} {type : Typ} (lookup : Lookup context x type) :
    TypingContext.Lookup (context.translate w) (context.index x) (type.translate w) := by
  induction lookup with
  | here =>
      simpa only [Context.index, Context.translate, TypingContext.bind, List.map_cons,
        ite_true] using TypingContext.Lookup.here
  | there different rest ih =>
      simpa only [Context.index, Context.translate, TypingContext.bind, List.map_cons,
        different, ite_false, Nat.add_comm] using
        TypingContext.Lookup.there ih

def Path.translate {n : Nat} (w : Witnesses n) (context : Context) (path : Path) :
    CTMLCore.Syntax.Term :=
  path.fields.foldr (fun field term => .proj term (w.fieldName field))
    (.var (context.index path.root))

/-- A fragment of source derivations, not an assumed target-typing certificate. -/
inductive PathTyping (bounds : List Bound) (context : Context) : Path → Typ → Type where
  | var {x type} : Lookup context x type → PathTyping bounds context ⟨x, []⟩ type
  | field {path label type} :
      PathTyping bounds context path (.field label type) →
      PathTyping bounds context (path.field label) type
  | record {path label type} :
      PathTyping bounds context (path.field label) type →
      PathTyping bounds context path (.field label type)
  | inter {path left right} :
      PathTyping bounds context path left → PathTyping bounds context path right →
      PathTyping bounds context path (.inter left right)
  | subsumption {path left right} :
      PathTyping bounds context path left → Subtyping bounds left right →
      PathTyping bounds context path right

theorem PathTyping.source {bounds : List Bound} {context : Context} {path : Path} {type : Typ}
    (h : PathTyping bounds context path type) (members : SourceBounds context.source bounds) :
    CDot.Typed context.source (.path path.source) type.source :=
  match h with
  | .var lookup => .var lookup.source
  | .field body => .newElim (body.source members)
  | .record body => .rcdIntro (body.source members)
  | .inter left right => .andIntro (left.source members) (right.source members)
  | .subsumption body sub => .sub (body.source members) (sub.source members)

/-- An opened self binding may be supplied by DOT's recursive elimination rule. -/
theorem PathTyping.sourceIn {bounds : List Bound} {context : Context} {path : Path} {type : Typ}
    (h : PathTyping bounds context path type) {sourceContext : CDot.Ctx}
    (bindings : ∀ {x type}, Lookup context x type →
      CDot.Typed sourceContext (.var x) type.source)
    (members : SourceBounds sourceContext bounds) :
    CDot.Typed sourceContext (.path path.source) type.source :=
  match h with
  | .var lookup => bindings lookup
  | .field body => .newElim (body.sourceIn bindings members)
  | .record body => .rcdIntro (body.sourceIn bindings members)
  | .inter left right =>
      .andIntro (left.sourceIn bindings members) (right.sourceIn bindings members)
  | .subsumption body sub => .sub (body.sourceIn bindings members) (sub.source members)

/-- This function constructs a target derivation by recursion over the source derivation. -/
theorem PathTyping.translate {n : Nat} (w : Witnesses n) {bounds : List Bound}
    {context : Context} {path : Path} {type : Typ} (h : PathTyping bounds context path type) :
    HasType (boundsContext w bounds) (context.translate w)
      (path.translate w context) (type.translate w) :=
  match h with
  | .var lookup => .var _ _ _ (lookup.translate w)
  | .field body => .projection (body.translate w)
  | .record body => CTML.projectionInverse (body.translate w)
  | .inter left right => .intersection (left.translate w) (right.translate w)
  | .subsumption body sub => .subsumption (body.translate w) (sub.translate w)

inductive Term where
  | path (path : Path)
  | app (function argument : Path)

def Term.source : Term → CDot.Trm
  | .path p => .path p.source
  | .app function argument => .app function.source argument.source

def Term.translate {n : Nat} (w : Witnesses n) (context : Context) : Term → CTMLCore.Syntax.Term
  | .path p => p.translate w context
  | .app function argument => .app (function.translate w context) (argument.translate w context)

inductive Typing (bounds : List Bound) (context : Context) : Term → Typ → Type where
  | path {path type} : PathTyping bounds context path type → Typing bounds context (.path path) type
  | app {function argument param result} :
      PathTyping bounds context function (.arrow param result) →
      PathTyping bounds context argument param →
      Typing bounds context (.app function argument) result
  | subsumption {term left right} :
      Typing bounds context term left → Subtyping bounds left right →
      Typing bounds context term right

theorem Typing.source {bounds : List Bound} {context : Context} {term : Term} {type : Typ}
    (h : Typing bounds context term type) (members : SourceBounds context.source bounds) :
    CDot.Typed context.source term.source type.source := by
  induction h with
  | path body => exact body.source members
  | app function argument =>
      simpa only [Term.source, CDot.Typ.openPath, Typ.source_openRecPath] using
        CDot.Typed.allElim (function.source members) (argument.source members)
  | subsumption _ sub ih => exact .sub ih (sub.source members)

theorem Typing.translate {n : Nat} (w : Witnesses n) {bounds : List Bound}
    {context : Context} {term : Term} {type : Typ} (h : Typing bounds context term type) :
    HasType (boundsContext w bounds) (context.translate w)
      (term.translate w context) (type.translate w) :=
  match h with
  | .path body => body.translate w
  | .app function argument => .application (function.translate w) (argument.translate w)
  | .subsumption body sub => .subsumption (body.translate w) (sub.translate w)

theorem Typing.sourceIn {bounds : List Bound} {context : Context} {term : Term} {type : Typ}
    (h : Typing bounds context term type) {sourceContext : CDot.Ctx}
    (bindings : ∀ {x type}, Lookup context x type →
      CDot.Typed sourceContext (.var x) type.source)
    (members : SourceBounds sourceContext bounds) :
    CDot.Typed sourceContext term.source type.source := by
  induction h with
  | path body => exact body.sourceIn bindings members
  | app function argument =>
      simpa only [Term.source, CDot.Typ.openPath, Typ.source_openRecPath] using
        CDot.Typed.allElim (function.sourceIn bindings members) (argument.sourceIn bindings members)
  | subsumption _ sub ih => exact .sub ih (sub.source members)

theorem Path.translate_liftTy {n : Nat} (w : Witnesses n) (context : Context)
    (path : Path) (amount : Nat) :
    (path.translate w context).liftTy amount = path.translate w context := by
  rcases path with ⟨root, fields⟩
  induction fields <;>
    simp_all only [Path.translate, List.foldr, CTMLCore.Syntax.Term.liftTy,
      CTMLCore.Syntax.Term.liftTyAt]

theorem Term.translate_liftTy {n : Nat} (w : Witnesses n) (context : Context)
    (term : Term) (amount : Nat) :
    (term.translate w context).liftTy amount = term.translate w context :=
  match term with
  | .path p => p.translate_liftTy w context amount
  | .app function argument => congrArg₂ CTMLCore.Syntax.Term.app
      (function.translate_liftTy w context amount) (argument.translate_liftTy w context amount)

/-- Close a compiled open derivation by abstracting its member witness and all bounds.
The consumer's lambda satisfies CTML's value restriction even when the body is an application. -/
theorem Typing.consumerAt {n : Nat} (w : Witnesses (n + 1)) {bounds : List Bound}
    {x : CDot.Var} {payload result : Typ} {term : Term} (answer : WFTy n)
    (h : Typing bounds [(x, payload)] term result)
    (resultType : result.translate w = answer.weaken) :
    HasType ⟨n, []⟩ TypingContext.empty
      (.abs (term.translate w [(x, payload)]))
      (CTML.consumer (bounds.flatMap (Bound.guards w)) (payload.translate w) answer) := by
  apply CTML.consumerTyping
  rw [Term.translate_liftTy, ← resultType]
  refine (h.translate w).mapAssumptions ?_
  exact fun guard membership =>
    @Subtype.hyp (CTML.assumeMany (SubtypingContext.bindType ⟨n, []⟩)
      (bounds.flatMap (Bound.guards w))) guard
    (List.mem_append_left _ (List.mem_reverse.mpr membership))

theorem Typing.consumer {n : Nat} (w : Witnesses (n + 1)) {bounds : List Bound}
    {x : CDot.Var} {payload : Typ} {term : Term}
    (h : Typing bounds [(x, payload)] term .top) :
    HasType ⟨n, []⟩ TypingContext.empty
      (.abs (term.translate w [(x, payload)]))
      (CTML.consumer (bounds.flatMap (Bound.guards w)) (payload.translate w) WFTy.top) :=
  h.consumerAt w WFTy.top rfl

end CDotFCCT.OpenCore
