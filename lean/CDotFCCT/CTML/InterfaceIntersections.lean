import CDotFCCT.CTML.InterfaceSubtyping

/-!
# Intersections that share their existential witnesses

Two views of one DOT path must use the same member witnesses. `Alignment` records
that common binder structure. Merging it conjoins the bounds and intersects the
native payloads under those binders. It does not identify the unrelated witnesses
of two independently produced existential packages.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML

open CTMLCore

inductive Alignment : Nat → Type where
  | payload {n : Nat} (left right : WFTy n) : Alignment n
  | leftGuard {n : Nat} (constraint : WFConstraint n) (rest : Alignment n) : Alignment n
  | rightGuard {n : Nat} (constraint : WFConstraint n) (rest : Alignment n) : Alignment n
  | bind {n : Nat} (rest : Alignment (n + 1)) : Alignment n

namespace Alignment

def left {n : Nat} : Alignment n → Interface n
  | .payload first _ => .payload first
  | .leftGuard constraint rest => .guard constraint rest.left
  | .rightGuard _ rest => rest.left
  | .bind rest => .bind rest.left

def right {n : Nat} : Alignment n → Interface n
  | .payload _ second => .payload second
  | .leftGuard _ rest => rest.right
  | .rightGuard constraint rest => .guard constraint rest.right
  | .bind rest => .bind rest.right

def meet {n : Nat} : Alignment n → Interface n
  | .payload first second => .payload (WFTy.intersection first second)
  | .leftGuard constraint rest | .rightGuard constraint rest => .guard constraint rest.meet
  | .bind rest => .bind rest.meet

theorem meetLeft {n : Nat} (alignment : Alignment n) (assumptions : List (WFConstraint n)) :
    Interface.Map ⟨n, assumptions⟩ alignment.meet alignment.left :=
  match alignment with
  | .payload _ _ => .payload .interLeft
  | .leftGuard constraint rest =>
      .sourceGuard (.targetGuard
        (@Subtype.hyp ⟨n, constraint :: assumptions⟩ constraint List.mem_cons_self)
        (rest.meetLeft (constraint :: assumptions)))
  | .rightGuard constraint rest => .sourceGuard (rest.meetLeft (constraint :: assumptions))
  | .bind rest => .bind (rest.meetLeft (assumptions.map WFConstraint.weaken))

theorem meetRight {n : Nat} (alignment : Alignment n) (assumptions : List (WFConstraint n)) :
    Interface.Map ⟨n, assumptions⟩ alignment.meet alignment.right :=
  match alignment with
  | .payload _ _ => .payload .interRight
  | .leftGuard constraint rest => .sourceGuard (rest.meetRight (constraint :: assumptions))
  | .rightGuard constraint rest =>
      .sourceGuard (.targetGuard
        (@Subtype.hyp ⟨n, constraint :: assumptions⟩ constraint List.mem_cons_self)
        (rest.meetRight (constraint :: assumptions)))
  | .bind rest => .bind (rest.meetRight (assumptions.map WFConstraint.weaken))

theorem packageLeft {s : SubtypingContext} (alignment : Alignment s.typeDepth)
    (answer : WFTy s.typeDepth) :
    Subtype s (alignment.meet.package answer) (alignment.left.package answer) :=
  (alignment.meetLeft s.assumptions).packageSubtype answer

theorem packageRight {s : SubtypingContext} (alignment : Alignment s.typeDepth)
    (answer : WFTy s.typeDepth) :
    Subtype s (alignment.meet.package answer) (alignment.right.package answer) :=
  (alignment.meetRight s.assumptions).packageSubtype answer

end Alignment

end CDotFCCT.CTML
