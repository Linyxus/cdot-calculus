import CDotFCCT.CTML.CarrierRuntimeEquations

/-!
# A single scope for coupled runtime rows and pure carriers

Carrier names precede runtime names. Both directions of every generated equation
are available inside the scope, with all outer assumptions weakened by its size.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed.CarrierRuntime.System

open CTMLCore CTMLCore.Syntax CTMLCore.Indexed

variable {ghost : FieldName → Bool} {depth runtimeSize carrierSize : Nat}

def unfoldGuard (system : System ghost depth runtimeSize carrierSize)
    (index : Fin system.size) : WFConstraint (depth + system.size) :=
  WFConstraint.constr (system.name index) (system.bodyAt index)

def foldGuard (system : System ghost depth runtimeSize carrierSize)
    (index : Fin system.size) : WFConstraint (depth + system.size) :=
  WFConstraint.constr (system.bodyAt index) (system.name index)

def equations (system : System ghost depth runtimeSize carrierSize) :
    List (WFConstraint (depth + system.size)) :=
  List.ofFn system.unfoldGuard ++ List.ofFn system.foldGuard

def openContext (s : SubtypingContext) (system : System ghost s.typeDepth runtimeSize carrierSize) :
    SubtypingContext :=
  ⟨s.typeDepth + system.size,
    system.equations ++ s.assumptions.map (WFConstraint.weakenBy system.size)⟩

theorem unfold (s : SubtypingContext) (system : System ghost s.typeDepth runtimeSize carrierSize)
    (index : Fin system.size) :
    Subtype (system.openContext s) (system.name index) (system.bodyAt index) :=
  @Subtype.hyp (system.openContext s) (system.unfoldGuard index)
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨index, rfl⟩)))

theorem fold (s : SubtypingContext) (system : System ghost s.typeDepth runtimeSize carrierSize)
    (index : Fin system.size) :
    Subtype (system.openContext s) (system.bodyAt index) (system.name index) :=
  @Subtype.hyp (system.openContext s) (system.foldGuard index)
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨index, rfl⟩)))

theorem guards (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) (index : Fin system.size) (n : Nat) :
    interpretGuard ghost (system.environment env) (system.unfoldGuard index).raw n ∧
      interpretGuard ghost (system.environment env) (system.foldGuard index).raw n := by
  simp only [unfoldGuard, foldGuard, WFConstraint.constr, interpretGuard, system.equation env index]
  exact ⟨fun _ _ _ => ⟨id, id⟩, fun _ _ _ => ⟨id, id⟩⟩

theorem validates {s : SubtypingContext} {env : Environment} {n : Nat}
    (system : System ghost s.typeDepth runtimeSize carrierSize)
    (valid : Validates ghost s env n) :
    Validates ghost (system.openContext s) (system.environment env) n := by
  intro guard membership
  rcases List.mem_append.mp membership with equation | outer
  · exact (List.mem_append.mp equation).elim
      (fun contains => match List.mem_ofFn.mp contains with
        | ⟨index, equal⟩ => equal ▸ (system.guards env index n).1)
      (fun contains => match List.mem_ofFn.mp contains with
        | ⟨index, equal⟩ => equal ▸ (system.guards env index n).2)
  · obtain ⟨old, member, rfl⟩ := List.mem_map.mp outer
    exact congrFun (interpretGuard_liftAt ghost old.raw (system.environment_lifted env)) n ▸
      valid old member

theorem noCollapse (system : System ghost 0 runtimeSize carrierSize) :
    ¬ InvertingSubtype ghost (system.openContext SubtypingContext.empty) WFTy.top WFTy.bottom :=
  Mixed.noCollapse (system.validates (s := SubtypingContext.empty)
    (empty_validates ghost (fun _ _ => (fun _ => False, fun _ => False)) 0))

end CDotFCCT.CTML.Mixed.CarrierRuntime.System
