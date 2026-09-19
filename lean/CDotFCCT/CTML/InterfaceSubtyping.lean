import CDotFCCT.CTML.Interfaces

/-! # Subtyping shared-witness interfaces -/

set_option autoImplicit false

namespace CDotFCCT.CTML.Interface

open CTMLCore

def liftAt {n : Nat} (interface : Interface n) (index : Nat) (valid : index ≤ n) :
    Interface (n + 1) :=
  match interface with
  | .payload type => .payload (type.liftAt index valid)
  | .guard constraint rest => .guard (constraint.liftAt index valid) (rest.liftAt index valid)
  | .bind rest => .bind (rest.liftAt (index + 1) (by omega))

def weaken {n : Nat} (interface : Interface n) : Interface (n + 1) :=
  interface.liftAt 0 (Nat.zero_le n)

theorem consumer_liftAt {n : Nat} (interface : Interface n) (answer : WFTy n)
    (index : Nat) (valid : index ≤ n) :
    (interface.consumer answer).liftAt index valid =
      (interface.liftAt index valid).consumer (answer.liftAt index valid) :=
  match interface with
  | .payload type => by
      simpa only [consumer, liftAt] using WFTy.liftAt_arrow valid type answer
  | .guard constraint rest => by
      simpa only [consumer, liftAt] using
        (WFTy.liftAt_constrained valid constraint (rest.consumer answer)).trans
          (congrArg (WFTy.constrained (constraint.liftAt index valid))
            (rest.consumer_liftAt answer index valid))
  | .bind rest => by
      simpa only [consumer, liftAt] using
        (WFTy.liftAt_all valid (rest.consumer answer.weaken)).trans
          ((congrArg WFTy.all (rest.consumer_liftAt answer.weaken (index + 1) (by omega))).trans
            (congrArg
              (fun result => WFTy.all ((rest.liftAt (index + 1) (by omega)).consumer result))
              (WFTy.liftAt_weaken valid answer)))

theorem consumer_weaken {n : Nat} (interface : Interface n) (answer : WFTy n) :
    (interface.consumer answer).weaken = interface.weaken.consumer answer.weaken :=
  interface.consumer_liftAt answer 0 (Nat.zero_le n)

/-- A package transformation opens each source witness once. It may use source
guards to discharge target guards, forget source witnesses, or choose witnesses
for the target. Every leaf carries ordinary payload subtyping. -/
inductive Map : (s : SubtypingContext) → Interface s.typeDepth → Interface s.typeDepth → Prop where
  | payload {s : SubtypingContext} {source target : WFTy s.typeDepth} :
      Subtype s source target → Map s (.payload source) (.payload target)
  | sourceGuard {s : SubtypingContext} {constraint : WFConstraint s.typeDepth}
      {source target : Interface s.typeDepth} :
      Map (s.assume constraint) source target → Map s (.guard constraint source) target
  | targetGuard {s : SubtypingContext} {constraint : WFConstraint s.typeDepth}
      {source target : Interface s.typeDepth} :
      Subtype s constraint.sub constraint.sup → Map s source target →
      Map s source (.guard constraint target)
  | sourceBind {s : SubtypingContext} {source : Interface (s.typeDepth + 1)}
      {target : Interface s.typeDepth} :
      Map s.bindType source target.weaken → Map s (.bind source) target
  | targetBind {s : SubtypingContext} {source : Interface s.typeDepth}
      {target : Interface (s.typeDepth + 1)} (witness : WFTy s.typeDepth) :
      Map s source (target.instantiate witness) → Map s source (.bind target)
  | bind {s : SubtypingContext} {source target : Interface (s.typeDepth + 1)} :
      Map s.bindType source target → Map s (.bind source) (.bind target)

theorem Map.consumerSubtype {s : SubtypingContext} {source target : Interface s.typeDepth}
    (map : Map s source target) (answer : WFTy s.typeDepth) :
    Subtype s (target.consumer answer) (source.consumer answer) :=
  match map with
  | .payload sub => .arrow sub .refl
  | .sourceGuard (constraint := constraint) map =>
      .trans (.constrainedRight constraint _) (.constrainedCovariant constraint _ _
        (map.consumerSubtype answer))
  | .targetGuard evidence map =>
      .trans (.constrainedLeft _ _ evidence) (map.consumerSubtype answer)
  | .sourceBind (target := target) map =>
      .trans .forallRight (.forallCovariant _ _
        ((target.consumer_weaken answer).symm ▸ map.consumerSubtype answer.weaken))
  | .targetBind (target := target) witness map =>
      .trans (.forallLeft (argument := witness))
        ((target.consumer_instantiate answer witness).symm ▸ map.consumerSubtype answer)
  | .bind map => .forallCovariant _ _ (map.consumerSubtype answer.weaken)

/-- Coercion of the existential package uses contravariance of its single consumer. -/
theorem Map.packageSubtype {s : SubtypingContext} {source target : Interface s.typeDepth}
    (map : Map s source target) (answer : WFTy s.typeDepth) :
    Subtype s (source.package answer) (target.package answer) :=
  .arrow (map.consumerSubtype answer) .refl

end CDotFCCT.CTML.Interface
