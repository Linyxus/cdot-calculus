import CDotFCCT.CTML.CarrierEquationModel
import CDotFCCT.CTML.MixedContext
import CTMLCore.Declarative.IndexedSystems

/-!
# Scoped carrier equations in the mixed target

Every name in a finite carrier block is bound simultaneously. The generated
context contains both directions of every equation followed by the weakened
outer assumptions. The interpretation bridge validates these equations using
the pure carrier solver; it does not introduce a typing rule.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierEquation

open CTMLCore CTMLCore.Syntax CTMLCore.Indexed

variable {ghost : FieldName → Bool} {depth size : Nat}

/-- Compiling preserves denotation when the recursive names are downward closed. -/
theorem Expr.interpret_compile (expr : Expr ghost depth size) (env : Environment)
    (selves : Fin size → Indexed.Candidate) (closed : ∀ index, Downward (selves index)) :
    interpret ghost (env.prepend selves) expr.compile.raw =
      expr.denote (fun type => interpret ghost env type.raw) selves :=
  match expr with
  | .leaf type => interpret_liftAt ghost type.raw (env.prepend_lifted selves)
  | .ref index => by
      simpa only [Expr.compile, WFTy.var, interpret, Environment.prepend,
        dite_eq_left index.isLt, Expr.denote] using prefixClosure_eq (closed index)
  | .neg body => congrArg negative (body.interpret_compile env selves closed)
  | .joint kind left right => congrArg₂ (Indexed.joint kind)
      (left.interpret_compile env selves closed) (right.interpret_compile env selves closed)
  | .record field marked body => by
      simpa only [Expr.compile, WFTy.record, interpret, Expr.denote,
        Mixed.record, marked, ↓reduceIte] using
        congrArg (TransparentRecord.record field) (body.interpret_compile env selves closed)

namespace System

def name (_ : System ghost depth size) (index : Fin size) : WFTy (depth + size) :=
  WFTy.var index (Nat.lt_of_lt_of_le index.isLt (Nat.le_add_left _ _))

def unfoldGuard (system : System ghost depth size) (index : Fin size) :
    WFConstraint (depth + size) := WFConstraint.constr (system.name index) (system.compile index)

def foldGuard (system : System ghost depth size) (index : Fin size) :
    WFConstraint (depth + size) := WFConstraint.constr (system.compile index) (system.name index)

def equations (system : System ghost depth size) : List (WFConstraint (depth + size)) :=
  List.ofFn system.unfoldGuard ++ List.ofFn system.foldGuard

def openContext {size : Nat} (s : SubtypingContext) (system : System ghost s.typeDepth size) :
    SubtypingContext :=
  ⟨s.typeDepth + size, system.equations ++ s.assumptions.map (WFConstraint.weakenBy size)⟩

theorem unfold {size : Nat} (s : SubtypingContext) (system : System ghost s.typeDepth size)
    (index : Fin size) :
    Subtype (system.openContext s) (system.name index) (system.compile index) :=
  @Subtype.hyp (system.openContext s) (system.unfoldGuard index)
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨index, rfl⟩)))

theorem fold {size : Nat} (s : SubtypingContext) (system : System ghost s.typeDepth size)
    (index : Fin size) :
    Subtype (system.openContext s) (system.compile index) (system.name index) :=
  @Subtype.hyp (system.openContext s) (system.foldGuard index)
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨index, rfl⟩)))

theorem interpret_name (system : System ghost depth size) (env : Environment)
    (selves : Fin size → Indexed.Candidate) (closed : ∀ index, Downward (selves index))
    (index : Fin size) :
    interpret ghost (env.prepend selves) (system.name index).raw = selves index :=
  (Expr.ref index : Expr ghost depth size).interpret_compile env selves closed

/-- Any downward solution validates each compiled carrier equation. -/
theorem equation_of_solution (system : System ghost depth size) (env : Environment)
    (selves : Fin size → Indexed.Candidate) (closed : ∀ index, Downward (selves index))
    (solved : ∀ index, selves index =
      (system.body index).denote (fun type => interpret ghost env type.raw) selves)
    (index : Fin size) :
    interpret ghost (env.prepend selves) (system.name index).raw =
      interpret ghost (env.prepend selves) (system.compile index).raw :=
  (system.interpret_name env selves closed index).trans
    ((solved index).trans ((system.body index).interpret_compile env selves closed).symm)

theorem guards_of_solution (system : System ghost depth size) (env : Environment)
    (selves : Fin size → Indexed.Candidate) (closed : ∀ index, Downward (selves index))
    (solved : ∀ index, selves index =
      (system.body index).denote (fun type => interpret ghost env type.raw) selves)
    (index : Fin size) (n : Nat) :
    interpretGuard ghost (env.prepend selves) (system.unfoldGuard index).raw n ∧
      interpretGuard ghost (env.prepend selves) (system.foldGuard index).raw n := by
  change Includes _ _ n ∧ Includes _ _ n
  rw [system.equation_of_solution env selves closed solved index]
  exact ⟨fun _ _ _ => ⟨id, id⟩, fun _ _ _ => ⟨id, id⟩⟩

/-- Solving the block preserves every weakened outer assumption. -/
theorem validates_of_solution {size : Nat} {s : SubtypingContext} {env : Environment} {n : Nat}
    (system : System ghost s.typeDepth size) (selves : Fin size → Indexed.Candidate)
    (closed : ∀ index, Downward (selves index))
    (solved : ∀ index, selves index =
      (system.body index).denote (fun type => interpret ghost env type.raw) selves)
    (valid : Validates ghost s env n) :
    Validates ghost (system.openContext s) (env.prepend selves) n := by
  intro guard membership
  rcases List.mem_append.mp membership with equation | outer
  · exact (List.mem_append.mp equation).elim
      (fun contains => match List.mem_ofFn.mp contains with
        | ⟨index, equal⟩ => equal ▸ (system.guards_of_solution env selves closed solved index n).1)
      (fun contains => match List.mem_ofFn.mp contains with
        | ⟨index, equal⟩ => equal ▸ (system.guards_of_solution env selves closed solved index n).2)
  obtain ⟨old, member, rfl⟩ := List.mem_map.mp outer
  exact congrFun (interpretGuard_liftAt ghost old.raw (env.prepend_lifted selves)) n ▸
    valid old member

def interpretation (system : System ghost depth size) (env : Environment) (index : Fin size) :
    Indexed.Candidate := system.solution (fun type => interpret ghost env type.raw) index

def environment (system : System ghost depth size) (env : Environment) : Environment :=
  env.prepend (system.interpretation env)

theorem downward (system : System ghost depth size) (env : Environment) (index : Fin size) :
    Downward (system.interpretation env index) :=
  system.solution_downward (fun type => interpret_downward ghost type.raw env) index

/-- The generated simultaneous solution satisfies every equation in the actual target model. -/
theorem equation (system : System ghost depth size) (env : Environment) (index : Fin size) :
    interpret ghost (system.environment env) (system.name index).raw =
      interpret ghost (system.environment env) (system.compile index).raw :=
  system.equation_of_solution env (system.interpretation env) (system.downward env)
    (system.solution_equation (fun type => interpret ghost env type.raw)) index

theorem guards (system : System ghost depth size) (env : Environment) (index : Fin size) (n : Nat) :
    interpretGuard ghost (system.environment env) (system.unfoldGuard index).raw n ∧
      interpretGuard ghost (system.environment env) (system.foldGuard index).raw n :=
  system.guards_of_solution env (system.interpretation env) (system.downward env)
    (system.solution_equation (fun type => interpret ghost env type.raw)) index n

/-- Opening the solved block introduces valid equations without changing outer assumptions. -/
theorem validates {size : Nat} {s : SubtypingContext} {env : Environment} {n : Nat}
    (system : System ghost s.typeDepth size) (valid : Validates ghost s env n) :
    Validates ghost (system.openContext s) (system.environment env) n :=
  system.validates_of_solution (system.interpretation env) (system.downward env)
    (system.solution_equation (fun type => interpret ghost env type.raw)) valid

end System

end CDotFCCT.CTML.Mixed.CarrierEquation
