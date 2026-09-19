import CDotFCCT.CarrierRuntime
import CDotFCCT.CTML.CarrierRuntimeSelf
import CDotFCCT.CTML.MixedFieldNames

/-!
# A source-directed entry for a whole-child self field

This partial pass recognizes `{ a = self }` with the source annotation
`{ a : self.type }`. It chooses the shared payload, presence and child slots,
solves their coupled carrier/runtime equations, and returns a typing derivation
for the exact runtime compiler output. No target witness or bound is supplied.

The result uses the specialized solved self-object interface. Checking the exact
source result prevents silently accepting a different requested source type;
a uniform `CarrierTranslation.TypeCode` for recursive objects remains separate.
-/

set_option autoImplicit false

namespace CDotFCCT.CarrierRuntimeSelfSource

open CDot CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTML.Mixed CarrierTranslation

section Generic

variable [Signature]

def body (field : Signature.TrmLabel) : Typ :=
  .rcd (.trm field (.sngl (.select (.bound 0) [])))

def sourceObject (tag : Path) (tagLabel : Signature.TypLabel) (field : Signature.TrmLabel) : Trm :=
  .val (.new tag tagLabel (body field)
    (.cons .nil (.trm field (.path (.select (.bound 0) [])))))

/-- The only field is present, and its complete child carrier is shared with self. -/
def support (field : Signature.TrmLabel) : List Slot :=
  [.payload, .present field, .child field]

def environment (context : Ctx) (source : Trm) : TermCPS.Env :=
  TermCPS.programEnv (runtimeIndex context) source

structure Shape (source : Trm) where
  tag : Path
  tagLabel : Signature.TypLabel
  field : Signature.TrmLabel
  source_eq : source = sourceObject tag tagLabel field

/-- Equality checks the annotation and complete definition list, including the bound self path. -/
def inspect (source : Trm) : Option (Shape source) :=
  match found : source with
  | .val (.new tag tagLabel (.rcd (.trm field _)) _) =>
      if equal : source = sourceObject tag tagLabel field then
        some ⟨tag, tagLabel, field, found.symm.trans equal⟩
      else none
  | _ => none

def Shape.interface {source : Trm} (shape : Shape source) (context : Ctx) (answer : WFTy 0) :
    CTML.Interface 0 :=
  CarrierRuntimeSelf.exportedInterface (support shape.field) Slot.payload (.child shape.field)
    (fun _ => WFTy.top) ((environment context source).fieldName shape.field)
    (TermCPS.programEnv_ordinary _ _ _) answer

/-- Tags are erased and the only runtime path is bound self, so this output is closed. -/
theorem Shape.runtime_eq {context : Ctx} {source : Trm} {result : Typ}
    (shape : Shape source) (derivation : Core.Typing context source result) :
    TermCPS.compile (environment context source) derivation =
      CTML.pack (SelfFieldAnchor.object ((environment context source).fieldName shape.field)) := by
  rcases shape with ⟨tag, tagLabel, field, rfl⟩
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The generated finite support and trivial presence marker discharge every target obligation. -/
theorem Shape.typing {context : Ctx} {source : Trm} {result : Typ}
    (shape : Shape source) (derivation : Core.Typing context source result) (answer : WFTy 0) :
    CTML.Mixed.HasType carrierPolicy SubtypingContext.empty TypingContext.empty
      (TermCPS.compile (environment context source) derivation)
      ((shape.interface context answer).package answer) := by
  rw [shape.runtime_eq derivation]
  exact CarrierRuntimeSelf.packTyping (s := SubtypingContext.empty)
    (support shape.field) Slot.payload (.child shape.field)
    List.mem_cons_self (by intro impossible; cases impossible) TypingContext.empty
    (fun _ => WFTy.top) _ (TermCPS.programEnv_ordinary _ _ _) answer

/-- The returned data carries the actual target derivation and exact source-result check. -/
structure Compiled {context : Ctx} {source : Trm} {result : Typ}
    (derivation : Core.Typing context source result) (answer : WFTy 0) where
  shape : Shape source
  result_eq : result = .bnd (body shape.field)
  typing : CTML.Mixed.HasType carrierPolicy SubtypingContext.empty TypingContext.empty
    (TermCPS.compile (environment context source) derivation)
    ((shape.interface context answer).package answer)

/-- A partial derivation-to-derivation compiler for the single self-alias constructor. -/
def compile {context : Ctx} {source : Trm} {result : Typ}
    (derivation : Core.Typing context source result) (answer : WFTy 0) :
    Option (Compiled derivation answer) := do
  let shape ← inspect source
  if equal : result = .bnd (body shape.field) then
    return ⟨shape, equal, shape.typing derivation answer⟩
  else none

end Generic

namespace Example

local instance : Signature where
  TypLabel := String
  TrmLabel := String
  typLabelDecidableEq := inferInstance
  trmLabelDecidableEq := inferInstance

def context : Ctx := [(0, .rcd (.typ "Tag" .top .top))]

def source : Trm := sourceObject (.var 0) "Tag" "a"

/-- A real core derivation retains the source tag premise and the bound self singleton. -/
def derivation : Core.Typing context source (.bnd (body "a")) :=
  .newIntro {0}
    (fun _ _ => .one (.path (.var .here)))
    (fun self fresh => by
      have different : (0 : Var) ≠ self := by
        intro equal
        subst self
        simp at fresh
      exact .sub (.sub (.var .here) .top) (.selLo (.var (.there different .here))))

theorem sourceTyping : CDot.Typed context source (.bnd (body "a")) := derivation.source

/-- The compiler computes the field name, shared slots, equations, and full target derivation. -/
def compiled (answer : WFTy 0) : Compiled derivation answer :=
  (compile derivation answer).get (by rfl)

theorem generatedSupport (answer : WFTy 0) :
    support (compiled answer).shape.field = [Slot.payload, .present "a", .child "a"] := rfl

theorem sourceRuntime : TermCPS.compile (environment context source) derivation =
    CTML.pack (SelfFieldAnchor.object "f") := rfl

theorem compiledTyping (answer : WFTy 0) :
    CTML.Mixed.HasType carrierPolicy SubtypingContext.empty TypingContext.empty
      (TermCPS.compile (environment context source) derivation)
      (((compiled answer).shape.interface context answer).package answer) :=
  (compiled answer).typing

/-- Subsuming the source result is not silently treated as the specialized recursive result. -/
def anotherResult : Core.Typing context source .top := .sub derivation .top

theorem rejectsAnotherResult (answer : WFTy 0) : compile anotherResult answer = none := rfl

theorem compiledSafe (answer : WFTy 0) {reached : Term}
    (steps : Steps (TermCPS.compile (environment context source) derivation) reached) :
    Value reached ∨ ∃ next, Step reached next := (compiledTyping answer).safe steps

end Example

end CDotFCCT.CarrierRuntimeSelfSource
