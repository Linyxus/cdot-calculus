import CDotFCCT.CTML.MixedInversion
import CDotFCCT.CTML.MixedValuation
import CDotFCCT.CTML.MixedRuntime
import CTMLCore.Declarative.IndexedFixpoint

/-! # Semantic typing with ordinary record guards and reflective ghost labels -/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation CTMLCore.Indexed

/-- Every well-related substitution yields a safe computation at each finite observation budget. -/
def Typing (ghost : FieldName → Bool) (s : SubtypingContext) (context : TypingContext s.typeDepth)
    (term : Term) (type : WFTy s.typeDepth) : Prop :=
  ∀ env n substitute, Validates ghost s env n → Valuation ghost env context n substitute →
    Computation (fun k => (interpret ghost env type.raw k).1) n
      (instantiate s.typeDepth substitute term)

def FieldsTyping (ghost : FieldName → Bool) (s : SubtypingContext)
    (context : TypingContext s.typeDepth) {names : List FieldName} (fields : TermFields names)
    (types : List (FieldName × WFTy s.typeDepth)) : Prop :=
  ∀ env n substitute, Validates ghost s env n → Valuation ghost env context n substitute →
    FieldsComputation ghost env n (instantiateFields s.typeDepth substitute fields) types

variable {ghost : FieldName → Bool}

theorem Typing.var {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {index : Nat} {type : WFTy s.typeDepth} (lookup : TypingContext.Lookup context index type) :
    Typing ghost s context (.var index) type :=
  fun _ _ substitute _ valuation => (instantiate_var s.typeDepth substitute index).symm ▸
    Computation.ofValue (valuation index type lookup).1 (valuation index type lookup).2

theorem Typing.subsumption {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {term : Term} {sub sup : WFTy s.typeDepth} (typing : Typing ghost s context term sub)
    (subtype : InvertingSubtype ghost s sub sup) : Typing ghost s context term sup :=
  fun env n substitute valid valuation =>
    (typing env n substitute valid valuation).mono (subtype.sound env n valid)

theorem Typing.forall {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {term : Term} {body : WFTy (s.typeDepth + 1)} (nonexpansive : Nonexpansive term)
    (inScope : ∀ index, term = .var index → index < context.entries.length)
    (typing : Typing ghost s.bindType context.bindType (term.liftTy 1) body) :
    Typing ghost s context term (WFTy.all body) := by
  intro env n substitute valid valuation
  refine .ofValue (nonexpansive_instantiate valuation nonexpansive inScope) ?_
  exact fun argument =>
    (show Computation (fun k => (interpret ghost (env.cons argument) body.raw k).1) n
      (instantiate s.typeDepth substitute term) from
        instantiate_liftTy s.typeDepth substitute term ▸
          typing (env.cons argument) n substitute (valid.bindType argument)
            (valuation.bindType argument)).atValue
      (nonexpansive_instantiate valuation nonexpansive inScope)

theorem Typing.constrained {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {term : Term} {guard : WFConstraint s.typeDepth} {body : WFTy s.typeDepth}
    (nonexpansive : Nonexpansive term)
    (inScope : ∀ index, term = .var index → index < context.entries.length)
    (typing : Typing ghost (s.assume guard) context term body) :
    Typing ghost s context term (WFTy.constrained guard body) :=
  fun env _n substitute valid valuation =>
    .ofValue (nonexpansive_instantiate valuation nonexpansive inScope)
      (fun k within holds =>
        (typing env k substitute ((valid.below within).assume holds)
          (valuation.below within)).atValue
            (nonexpansive_instantiate valuation nonexpansive inScope))

theorem Typing.recursive {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {term : Term} {type : WFTy s.typeDepth} (definition : Definition ghost s.typeDepth)
    (typing : Typing ghost (definition.native.openContext s) context.bindType
      (term.liftTy 1) type.weaken) :
    Typing ghost s context term type := by
  intro env n substitute valid valuation
  simpa only [interpret_lift, instantiate_liftTy] using
    (show Computation (fun k =>
      (interpret ghost (env.cons (definition.interpretation env)) (type.raw.lift 1) k).1) n
      (instantiate (s.typeDepth + 1) substitute (term.liftTy 1)) from
        typing (env.cons (definition.interpretation env)) n substitute
          (definition.validates valid) (valuation.bindType _))

theorem Typing.abstraction {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {body : Term} {param ret : WFTy s.typeDepth}
    (typing : Typing ghost s (context.bind param) body ret) :
    Typing ghost s context (.abs body) (WFTy.arrow param ret) :=
  fun env _n substitute valid valuation => (instantiate_abs s.typeDepth substitute body).symm ▸
    Computation.ofValue (.abs _) ⟨_, rfl, fun k smaller argument value related =>
      (instantiate_beta s.typeDepth substitute body argument).symm ▸
        typing env k _ (valid.below (Nat.le_of_lt smaller))
          ((valuation.below (Nat.le_of_lt smaller)).bind value related)⟩

theorem Typing.application {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {function argument : Term} {param ret : WFTy s.typeDepth}
    (functionTyping : Typing ghost s context function (WFTy.arrow param ret))
    (argumentTyping : Typing ghost s context argument param) :
    Typing ghost s context (.app function argument) ret :=
  fun env n substitute valid valuation =>
    (instantiate_app s.typeDepth substitute function argument).symm ▸
      Computation.application (interpret_downward ghost param.raw env)
        (functionTyping env n substitute valid valuation)
        (argumentTyping env n substitute valid valuation)

theorem Typing.record {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {names : List FieldName} {fields : TermFields names}
    {types : List (FieldName × WFTy s.typeDepth)}
    (typing : FieldsTyping ghost s context fields types)
    (className : ClassName) : Typing ghost s context (.record className fields)
      (recordResultType className types) :=
  fun env n substitute valid valuation =>
    (instantiate_record s.typeDepth substitute className fields).symm ▸
      (typing env n substitute valid valuation).record className

theorem Typing.projection {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {term : Term} {field : FieldName} {type : WFTy s.typeDepth}
    (typing : Typing ghost s context term (WFTy.record field type)) :
    Typing ghost s context (.proj term field) type :=
  fun env n substitute valid valuation =>
    (instantiate_proj s.typeDepth substitute term field).symm ▸
      Mixed.projection (interpret_downward ghost type.raw env)
        (typing env n substitute valid valuation)

theorem Typing.ascription {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {term : Term} {sub sup : WFTy s.typeDepth} (typing : Typing ghost s context term sub)
    (subtype : InvertingSubtype ghost s sub sup) :
    Typing ghost s context (.ascribe term sup.raw) sup :=
  fun env n substitute valid valuation =>
    (instantiate_ascribe s.typeDepth substitute term sup.raw).symm ▸
      Computation.ascription (interpret_downward ghost sup.raw env)
        (typing.subsumption subtype env n substitute valid valuation) _

theorem Typing.intersection {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {term : Term} {left right : WFTy s.typeDepth} (first : Typing ghost s context term left)
    (second : Typing ghost s context term right) :
    Typing ghost s context term (WFTy.intersection left right) :=
  fun env n substitute valid valuation => (first env n substitute valid valuation).intersection
    (second env n substitute valid valuation)

theorem Typing.fixpoint {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {function : Term} {param ret : WFTy s.typeDepth}
    (typing : Typing ghost s context function
      (WFTy.arrow (WFTy.arrow param ret) (WFTy.arrow param ret))) :
    Typing ghost s context (.fix function) (WFTy.arrow param ret) :=
  fun env n substitute valid valuation => (instantiate_fix s.typeDepth substitute function).symm ▸
    Computation.fixpoint (interpret_downward ghost param.raw env)
      (typing env n substitute valid valuation)

theorem Typing.ifThen {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {scrutinee yes no : Term} {className : ClassName} {scrutineeType result : WFTy s.typeDepth}
    (typing : Typing ghost s context scrutinee scrutineeType)
    (subtype : InvertingSubtype ghost s scrutineeType (WFTy.cls className))
    (branch : Typing ghost s (context.bind scrutineeType) yes result) :
    Typing ghost s context (.ifIs scrutinee className yes no) result :=
  fun env n substitute valid valuation =>
    (instantiate_ifIs s.typeDepth substitute scrutinee className yes no).symm ▸
      Computation.ifThen (interpret_downward ghost scrutineeType.raw env)
        (typing env n substitute valid valuation) className _ _
        (fun k within term => (subtype.sound env n valid k within term).1)
        (fun k within term value related =>
          (instantiate_beta s.typeDepth substitute yes term).symm ▸
            branch env k _ (valid.below within) ((valuation.below within).bind value related))

theorem Typing.ifElse {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {scrutinee yes no : Term} {className : ClassName} {scrutineeType result : WFTy s.typeDepth}
    (typing : Typing ghost s context scrutinee scrutineeType)
    (subtype : InvertingSubtype ghost s scrutineeType (WFTy.neg (WFTy.cls className)))
    (branch : Typing ghost s (context.bind scrutineeType) no result) :
    Typing ghost s context (.ifIs scrutinee className yes no) result :=
  fun env n substitute valid valuation =>
    (instantiate_ifIs s.typeDepth substitute scrutinee className yes no).symm ▸
      Computation.ifElse (interpret_downward ghost scrutineeType.raw env)
        (typing env n substitute valid valuation) className _ _
        (fun k within term => (subtype.sound env n valid k within term).1)
        (fun k within term value related =>
          (instantiate_beta s.typeDepth substitute no term).symm ▸
            branch env k _ (valid.below within) ((valuation.below within).bind value related))

theorem FieldsTyping.nil {s : SubtypingContext} {context : TypingContext s.typeDepth} :
    FieldsTyping ghost s context .nil [] :=
  fun _ _ substitute _ _ => (instantiateFields_nil s.typeDepth substitute).symm ▸
    FieldsComputation.nil

theorem FieldsTyping.cons {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {name : FieldName} {value : Term} {names : List FieldName} {tail : TermFields names}
    {fresh : name ∉ names} {type : WFTy s.typeDepth}
    {types : List (FieldName × WFTy s.typeDepth)} (head : Typing ghost s context value type)
    (rest : FieldsTyping ghost s context tail types) :
    FieldsTyping ghost s context (.cons name value tail fresh) ((name, type) :: types) :=
  fun env n substitute valid valuation =>
    (instantiateFields_cons s.typeDepth substitute name value tail fresh).symm ▸
      FieldsComputation.cons (head env n substitute valid valuation)
        (rest env n substitute valid valuation)

end CDotFCCT.CTML.Mixed
