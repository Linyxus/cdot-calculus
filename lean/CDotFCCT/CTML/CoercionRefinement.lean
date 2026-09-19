import CDotFCCT.CTML.Coercions

/-!
# Coercions that retain an existing view

An identity conversion can receive two typing derivations at the same syntax:
one for its original type and one for its new view. Native intersection
introduction then retains both. The lower-bound rule here needs the precise
row's marker answer to be the selected witness; a fixed, unrelated CPS answer
does not supply that stronger premise.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Coercion

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

theorem memberUpperRefinementTyping {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {payload value : Term}
    {data witness lower upper answer original : WFTy s.typeDepth}
    (bound : Subtype s (preciseMember data witness answer) (memberView lower upper answer))
    (input : Subtype s original witness)
    (hd : HasType s context payload data) (hv : HasType s context value original) :
    HasType s context (.app (.app memberUpperDirect payload) value)
      (WFTy.intersection original upper) :=
  .intersection
    (.application (.application (memberUpperDirectTyping context
      (preciseMemberOwnView s data original answer)) hd) hv)
    (.application (.application (memberUpperDirectTyping context bound) hd)
      (hv.subsumption input))

def memberLowerDirect : Term :=
  .abs (.abs (.app (.app (.app memberLower (.var 1)) (.var 0)) (.abs (.var 0))))

/-- Choosing the local marker answer to be the witness produces a direct cast. -/
theorem memberLowerDirectTyping {s : SubtypingContext} (context : TypingContext s.typeDepth)
    {data witness lower upper : WFTy s.typeDepth}
    (bound : Subtype s (preciseMember data witness witness) (memberView lower upper witness)) :
    HasType s context memberLowerDirect (WFTy.arrow data (WFTy.arrow lower witness)) :=
  .abstraction (.abstraction (.application
    (.application (.application (memberLowerTyping _ bound) (.var _ 1 _ (.there .here)))
      (.var _ 0 _ .here)) (.abstraction (.var _ 0 _ .here))))

theorem memberLowerRefinementTyping {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {payload value : Term}
    {data witness lower upper original : WFTy s.typeDepth}
    (bound : Subtype s (preciseMember data witness witness) (memberView lower upper witness))
    (input : Subtype s original lower)
    (hd : HasType s context payload data) (hv : HasType s context value original) :
    HasType s context (.app (.app memberLowerDirect payload) value)
      (WFTy.intersection original witness) :=
  .intersection
    (.application (.application (memberLowerDirectTyping context
      (preciseMemberOwnView s data original original)) hd) hv)
    (.application (.application (memberLowerDirectTyping context bound) hd)
      (hv.subsumption input))

theorem memberLowerDirectSteps {payload value : Term} (hd : Value payload) (hv : Value value) :
    Steps (.app (.app memberLowerDirect payload) value) value := by
  refine .trans (.appHead _ (.appBeta _ _ hd)) (.trans (.appBeta _ _ hv) ?_)
  change Steps (.app (.app (.app memberLower _) value) (.abs (.var 0))) value
  exact (memberLowerSteps ((hd.renameWith _).substWith _) hv (.abs _)).trans'
    (.single (.appBeta _ _ hv))

end CDotFCCT.CTML.Coercion
