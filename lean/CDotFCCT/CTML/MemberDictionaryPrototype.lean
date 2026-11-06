import CDotFCCT.CTML.Interfaces
import CTMLCore.Language.EvaluationTheory
import CTMLCore.Language.TermSubstitutionAlgebra

/-!
# Constructive dictionaries for one relational self-member type

The representation of `μself. { A : Bottom .. Top; a : self.A }` may hide two
runtime types `A` and `C` together with `lo : Bottom → A`, `hi : A → Top`,
`asA : C → A`, and `a : C`. Projection applies `asA` rather than inverting a
scalar carrier inclusion to recover `C ≤ A`. All fields below are native records;
the construction uses neither ghost-row inversion nor a new typing rule.

Exact aliases choose both witnesses as the payload's actual translated type.
Their three dictionaries are identity functions, and the complete client reduces
to the original value. For general aliases, function typing alone is insufficient
to guarantee this coherence in a target with fixpoints: the compiler must generate
coercions and prove their behavior. This is a prototype, not a source translation.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.MemberDictionaryPrototype

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

def identity : Term := .abs (.var 0)

def dictionaryType {depth : Nat} (member child : WFTy depth) : WFTy depth :=
  recordResultType "$MemberDictionary"
    [("lo", WFTy.arrow WFTy.bottom member), ("hi", WFTy.arrow member WFTy.top),
      ("asA", WFTy.arrow child member), ("a", child)]

def dictionary (payload : Term) : Term :=
  .record "$MemberDictionary" (.cons "lo" identity
    (.cons "hi" identity (.cons "asA" identity (.cons "a" payload .nil (by decide))
      (by decide)) (by decide)) (by decide))

/-- The two abstract names and their connecting function occur in one package. -/
def interface {depth : Nat} : Interface depth :=
  .bind (.bind (.payload (dictionaryType (WFTy.var 1 (by omega)) (WFTy.var 0 (by omega)))))

theorem identityTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {sub sup : WFTy s.typeDepth} (included : Subtype s sub sup) :
    HasType s context identity (WFTy.arrow sub sup) :=
  .abstraction ((HasType.var _ 0 _ .here).subsumption included)

/-- The exact-alias producer computes every coercion; it assumes only payload typing. -/
theorem dictionaryTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {payload : Term} {type : WFTy s.typeDepth} (typing : HasType s context payload type) :
    HasType s context (dictionary payload) (dictionaryType type type) :=
  .record (.cons (identityTyping (.extremum .bottom))
    (.cons (identityTyping (.extremum .top)) (.cons (identityTyping .refl) (.cons typing .nil))))

theorem dictionaryType_substAt {depth : Nat} (member child : WFTy (depth + 1))
    (index : Nat) (valid : index ≤ depth) (replacement : WFTy depth) :
    (dictionaryType member child).substAt index valid replacement =
      dictionaryType (member.substAt index valid replacement)
        (child.substAt index valid replacement) := by
  simp only [dictionaryType, recordResultType, List.foldl_cons, List.foldl_nil,
    WFTy.intersection, WFTy.substAt_joint, WFTy.substAt_record, WFTy.substAt_arrow,
    WFTy.bottom, WFTy.top, WFTy.substAt_extremum]
  rfl

def exactInstance (s : SubtypingContext) (type : WFTy s.typeDepth) :
    Interface.Instance s interface (dictionaryType type type) := by
  refine .bind type ?_
  simp only [Interface.instantiate, Interface.substAt, dictionaryType_substAt]
  change Interface.Instance s
    (.bind (.payload (dictionaryType type.weaken (WFTy.var 0 (by omega)))))
    (dictionaryType type type)
  refine .bind type ?_
  simp only [Interface.instantiate, Interface.substAt, dictionaryType_substAt]
  change Interface.Instance s
    (.payload (dictionaryType (type.weaken.instantiate type) type)) (dictionaryType type type)
  rw [WFTy.weaken_instantiate_cancel]
  exact .payload _

theorem packageTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {payload : Term} {type : WFTy s.typeDepth} (typing : HasType s context payload type)
    (answer : WFTy s.typeDepth) :
    HasType s context (pack (dictionary payload)) (interface.package answer) :=
  Interface.packTyping (exactInstance s type) (dictionaryTyping typing)

def select (object : Term) : Term :=
  .app (.proj object "asA") (.proj object "a")

def read (object : Term) : Term := .app (.proj object "hi") (select object)

/-- The child-to-member relation is usable as a function, without scalar subtyping evidence. -/
theorem selectTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {object : Term} {member child : WFTy s.typeDepth}
    (typing : HasType s context object (dictionaryType member child)) :
    HasType s context (select object) member :=
  .application (.projection (typing.subsumption (.trans .interLeft .interRight)))
    (.projection (typing.subsumption .interRight))

theorem readTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {object : Term} {member child : WFTy s.typeDepth}
    (typing : HasType s context object (dictionaryType member child)) :
    HasType s context (read object) WFTy.top :=
  .application
    (.projection (typing.subsumption (.trans .interLeft (.trans .interLeft .interRight))))
    (selectTyping typing)

theorem clientOpened (s : SubtypingContext) (context : TypingContext s.typeDepth) :
    Interface.OpenedBody s context (read (.var 0)) WFTy.top interface := by
  change HasType s.bindType.bindType
    (context.bindType.bindType.bind
      (dictionaryType (WFTy.var 1 (by omega)) (WFTy.var 0 (by omega))))
    (read (.var 0)) WFTy.top
  exact readTyping (.var _ 0 _ .here)

def program (payload : Term) : Term :=
  .app (pack (dictionary payload)) (.abs (read (.var 0)))

theorem programTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {payload : Term} {type : WFTy s.typeDepth} (typing : HasType s context payload type) :
    HasType s context (program payload) WFTy.top :=
  Interface.unpackTyping (packageTyping typing WFTy.top) (clientOpened s context)

theorem dictionaryValue {payload : Term} (value : Value payload) : Value (dictionary payload) :=
  .record _ _ (.cons (.abs _) (.cons (.abs _) (.cons (.abs _) (.cons value .nil))))

/-- Each generated dictionary is an administrative cast, with one concrete beta step. -/
theorem identityStep {value : Term} (isValue : Value value) :
    Step (.app identity value) value := .appBeta _ _ isValue

/-- The field-to-member cast returns exactly the stored field value. -/
theorem selectSteps {payload : Term} (value : Value payload) :
    Steps (select (dictionary payload)) payload := by
  refine .trans (.appHead _ (.proj (dictionaryValue value) (.there (.there .here)))) ?_
  refine .trans (.appArg (.abs _) (.proj (dictionaryValue value)
    (.there (.there (.there .here))))) ?_
  exact .single (identityStep value)

/-- Member upper-bound conversion preserves the same payload after field conversion. -/
theorem readSteps {payload : Term} (value : Value payload) :
    Steps (read (dictionary payload)) payload := by
  refine .trans (.appHead _ (.proj (dictionaryValue value) (.there .here))) ?_
  exact ((selectSteps value).appArg (.abs _)).trans' (.single (identityStep value))

/-- Existential opening and both dictionary calls reduce to the original value. -/
theorem programSteps {payload : Term} (value : Value payload) :
    Steps (program payload) payload := by
  refine .trans (.appBeta _ _ (.abs _)) ?_
  change Steps (.app (.abs (read (.var 0)))
    ((dictionary payload).lift 1 |>.substAt 0 (.abs (read (.var 0))))) payload
  rw [Term.lift_substAt_cancel]
  refine .trans (.appBeta _ _ (dictionaryValue value)) ?_
  exact readSteps value

def unit : Term := .record "$Unit" .nil

/-- The generated administrative cast cannot manufacture a value of `Bottom`. -/
theorem identity_not_top_bottom :
    ¬ HasType SubtypingContext.empty TypingContext.empty identity
      (WFTy.arrow WFTy.top WFTy.bottom) := by
  intro typing
  have unitTop : HasType SubtypingContext.empty TypingContext.empty unit WFTy.top :=
    (HasType.record .nil).subsumption (.extremum .top)
  have bottom := (HasType.application typing unitTop).preservation
    (identityStep (.record _ _ .nil))
  exact (bottom.toInhabits (.record _ _ .nil)).bottom_elim

/-- Correlation lives in the generated term dictionary: the bad mixed pair is rejected. -/
theorem rejectsOffDiagonal :
    ¬ HasType SubtypingContext.empty TypingContext.empty (dictionary unit)
      (dictionaryType WFTy.bottom WFTy.top) := by
  intro typing
  have castTyping := (typing.subsumption (.trans .interLeft .interRight)).record_field_typing
    (dictionaryValue (.record _ _ .nil)) (.there (.there .here))
  exact identity_not_top_bottom castTyping

theorem closedProgramTyping :
    HasType SubtypingContext.empty TypingContext.empty (program unit) WFTy.top :=
  programTyping (.record .nil)

theorem closedProgramSteps : Steps (program unit) unit :=
  programSteps (.record _ _ .nil)

end CDotFCCT.CTML.MemberDictionaryPrototype
