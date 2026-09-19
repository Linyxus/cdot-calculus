import CDotFCCT.CTML.Existentials
import CTMLCore.Language.TermSubstitutionAlgebra
import CTMLCore.Language.EvaluationTheory

/-!
# Explicit CPS coercions

A target subtyping proof is sufficient, but not necessary, to convert a value
without changing it. These coercions use native CTML records and applications.
Their execution lemmas distinguish an administrative conversion from divergence
at an arbitrarily chosen result type.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Coercion

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

def type {n : Nat} (source target answer : WFTy n) : WFTy n :=
  WFTy.arrow source (WFTy.arrow (WFTy.arrow target answer) answer)

def identity : Term := .abs (.abs (.app (.var 0) (.var 1)))

theorem identityTyping {s : SubtypingContext} (context : TypingContext s.typeDepth)
    {source target answer : WFTy s.typeDepth} (sub : Subtype s source target) :
    HasType s context identity (type source target answer) :=
  .abstraction (.abstraction (.application (.var _ 0 _ .here)
    ((HasType.var _ 1 _ (.there .here)).subsumption sub)))

/-- Contravariant arrow information can be used by a continuation without
postulating an arrow-domain inversion rule in the target subtyping judgment. -/
theorem arrowDomainTyping {s : SubtypingContext} (context : TypingContext s.typeDepth)
    {source target answer : WFTy s.typeDepth}
    (sub : Subtype s (WFTy.arrow target answer) (WFTy.arrow source answer)) :
    HasType s context identity (type source target answer) :=
  .abstraction (.abstraction (.application
    ((HasType.var _ 0 _ .here).subsumption sub) (.var _ 1 _ (.there .here))))

theorem identitySteps {value continuation : Term}
    (hv : Value value) (hk : Value continuation) :
    Steps (.app (.app identity value) continuation) (.app continuation value) := by
  refine .trans (.appHead _ (.appBeta _ _ hv)) (.trans (.appBeta _ _ hk) ?_)
  change Steps (.app continuation ((value.lift 1).substAt 0 continuation)) _
  simpa only [Term.lift_substAt_cancel] using (Steps.refl (term := .app continuation value))

/-- A suspended loop inhabits any arrow. Administrative marker records may use
it only in the field that their projection does not select. -/
def unusedFunction : Term := .abs (.app (.fix (.abs (.var 0))) (.var 0))

theorem unusedFunctionTyping {s : SubtypingContext} (context : TypingContext s.typeDepth)
    (param ret : WFTy s.typeDepth) :
    HasType s context unusedFunction (WFTy.arrow param ret) :=
  .abstraction (.application (.fixpoint (.abstraction (.var _ 0 _ .here)))
    (.var _ 0 _ .here))

def memberView {n : Nat} (lower upper answer : WFTy n) : WFTy n :=
  WFTy.intersection (WFTy.record "lower" (WFTy.arrow lower answer))
    (WFTy.record "upper" (WFTy.arrow WFTy.top upper))

/-- The payload is arbitrary, but the surrounding row has a known shape. This
lets a coercion replace one marker while preserving the actual payload. -/
def preciseMember {n : Nat} (payload witness answer : WFTy n) : WFTy n :=
  recordResultType "DOT.Member"
    [("data", payload), ("lower", WFTy.arrow witness answer),
      ("upper", WFTy.arrow WFTy.top witness)]

theorem preciseMemberOwnView (s : SubtypingContext) (data witness answer : WFTy s.typeDepth) :
    Subtype s (preciseMember data witness answer) (memberView witness witness answer) :=
  .leInter (.trans .interLeft .interRight) .interRight

theorem memberViewVariance {s : SubtypingContext}
    {lower₁ lower₂ upper₁ upper₂ answer : WFTy s.typeDepth}
    (lower : Subtype s lower₂ lower₁) (upper : Subtype s upper₁ upper₂) :
    Subtype s (memberView lower₁ upper₁ answer) (memberView lower₂ upper₂ answer) :=
  .leInter (.trans .interLeft (.record (.arrow lower .refl)))
    (.trans .interRight (.record (.arrow .refl upper)))

def markerRecord (payload lower upper : Term) : Term :=
  .record "DOT.Member" (.cons "data" payload
    (.cons "lower" lower (.cons "upper" upper .nil (by decide)) (by decide)) (by decide))

theorem markerRecordTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {payload lower upper : Term} {data witness answer : WFTy s.typeDepth}
    (hd : HasType s context payload data)
    (hl : HasType s context lower (WFTy.arrow witness answer))
    (hu : HasType s context upper (WFTy.arrow WFTy.top witness)) :
    HasType s context (markerRecord payload lower upper) (preciseMember data witness answer) :=
  .record (.cons hd (.cons hl (.cons hu .nil)))

def memberLower : Term :=
  .abs (.abs (.abs (.app
    (.proj (markerRecord (.var 2) (.var 0) unusedFunction) "lower") (.var 1))))

/-- A constraint on a precise row recovers a member's lower bound as an
identity CPS coercion, even when the row constraint was obtained transitively
through an abstract type. No record or arrow inversion rule is assumed. -/
theorem memberLowerTyping {s : SubtypingContext} (context : TypingContext s.typeDepth)
    {data witness lower upper answer : WFTy s.typeDepth}
    (bound : Subtype s (preciseMember data witness answer) (memberView lower upper answer)) :
    HasType s context memberLower (WFTy.arrow data (type lower witness answer)) :=
  .abstraction (.abstraction (.abstraction (.application
    (.projection ((markerRecordTyping (.var _ 2 _ (.there (.there .here)))
      (.var _ 0 _ .here) (unusedFunctionTyping _ _ _)).subsumption
        (.trans bound .interLeft))) (.var _ 1 _ (.there .here)))))

def memberUpperDirect : Term :=
  .abs (.abs (.app
    (.proj (markerRecord (.var 1) unusedFunction (.abs (.var 1))) "upper")
      (.record "Unit" .nil)))

theorem memberUpperDirectTyping {s : SubtypingContext} (context : TypingContext s.typeDepth)
    {data witness lower upper answer : WFTy s.typeDepth}
    (bound : Subtype s (preciseMember data witness answer) (memberView lower upper answer)) :
    HasType s context memberUpperDirect (WFTy.arrow data (WFTy.arrow witness upper)) :=
  .abstraction (.abstraction (.application
    (.projection ((markerRecordTyping (.var _ 1 _ (.there .here))
      (unusedFunctionTyping _ _ _) (.abstraction (.var _ 1 _ (.there .here))))
        |>.subsumption (.trans bound .interRight)))
    ((HasType.record .nil).subsumption .leTop)))

def memberUpper : Term :=
  .abs (.abs (.abs (.app (.var 0) (.app (.app memberUpperDirect (.var 2)) (.var 1)))))

theorem memberUpperTyping {s : SubtypingContext} (context : TypingContext s.typeDepth)
    {data witness lower upper answer : WFTy s.typeDepth}
    (bound : Subtype s (preciseMember data witness answer) (memberView lower upper answer)) :
    HasType s context memberUpper (WFTy.arrow data (type witness upper answer)) :=
  .abstraction (.abstraction (.abstraction (.application (.var _ 0 _ .here)
    (.application (.application (memberUpperDirectTyping _ bound)
      (.var _ 2 _ (.there (.there .here)))) (.var _ 1 _ (.there .here))))))

theorem memberLowerSteps {payload value continuation : Term}
    (hd : Value payload) (hv : Value value) (hk : Value continuation) :
    Steps (.app (.app (.app memberLower payload) value) continuation)
      (.app continuation value) := by
  refine .trans (.appHead _ (.appHead _ (.appBeta _ _ hd)))
    (.trans (.appHead _ (.appBeta _ _ hv)) (.trans (.appBeta _ _ hk) ?_))
  change Steps (.app (.proj (markerRecord _ continuation unusedFunction) "lower")
    ((value.lift 1).substAt 0 continuation)) _
  refine .trans (.appHead _ (.proj
    (.record _ _ (.cons ?_ (.cons hk (.cons (.abs _) .nil)))) (.there .here))) ?_
  · exact (((hd.renameWith _).renameWith _).substWith _).substWith _
  · simpa only [Term.lift_substAt_cancel] using (Steps.refl (term := .app continuation value))

theorem memberUpperDirectSteps {payload value : Term} (hd : Value payload) (hv : Value value) :
    Steps (.app (.app memberUpperDirect payload) value) value := by
  refine .trans (.appHead _ (.appBeta _ _ hd)) (.trans (.appBeta _ _ hv) ?_)
  change Steps (.app (.proj (markerRecord _ unusedFunction (.abs (value.lift 1))) "upper")
    (.record "Unit" .nil)) _
  refine .trans (.appHead _ (.proj
    (.record _ _ (.cons ?_ (.cons (.abs _) (.cons (.abs _) .nil))))
    (.there (.there .here)))) (.trans (.appBeta _ _ (.record _ _ .nil)) ?_)
  · exact (hd.renameWith _).substWith _
  · simpa only [Term.lift_substAt_cancel] using (Steps.refl (term := value))

theorem memberUpperSteps {payload value continuation : Term}
    (hd : Value payload) (hv : Value value) (hk : Value continuation) :
    Steps (.app (.app (.app memberUpper payload) value) continuation)
      (.app continuation value) := by
  refine .trans (.appHead _ (.appHead _ (.appBeta _ _ hd)))
    (.trans (.appHead _ (.appBeta _ _ hv)) (.trans (.appBeta _ _ hk) ?_))
  change Steps (.app continuation (.app (.app memberUpperDirect _)
    ((value.lift 1).substAt 0 continuation))) _
  rw [Term.lift_substAt_cancel]
  exact (memberUpperDirectSteps
    ((((hd.renameWith _).renameWith _).substWith _).substWith _) hv).appArg hk

/-- Compose the two member conversions while retaining one witness. The bounds
may have been obtained from different views of the same abstract type. -/
def throughMember (payload value continuation : Term) : Term :=
  .app (.app (.app memberLower payload) value)
    (.abs (.app (continuation.lift 1)
      (.app (.app memberUpperDirect (payload.lift 1)) (.var 0))))

theorem throughMemberTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {payload value continuation : Term}
    {data witness lower upper otherLower otherUpper answer : WFTy s.typeDepth}
    (lowerBound : Subtype s (preciseMember data witness answer)
      (memberView lower otherUpper answer))
    (upperBound : Subtype s (preciseMember data witness answer)
      (memberView otherLower upper answer))
    (hd : HasType s context payload data) (hv : HasType s context value lower)
    (hk : HasType s context continuation (WFTy.arrow upper answer)) :
    HasType s context (throughMember payload value continuation) answer :=
  .application (.application (.application (memberLowerTyping _ lowerBound) hd) hv)
    (.abstraction (.application (hk.weakenFront witness)
      (.application (.application (memberUpperDirectTyping _ upperBound)
        (hd.weakenFront witness)) (.var _ 0 _ .here))))

theorem throughMemberSteps {payload value continuation : Term}
    (hd : Value payload) (hv : Value value) (hk : Value continuation) :
    Steps (throughMember payload value continuation) (.app continuation value) := by
  refine (memberLowerSteps hd hv (.abs _)).trans' (.trans (.appBeta _ _ hv) ?_)
  change Steps (.app ((continuation.lift 1).substAt 0 value)
    (.app (.app memberUpperDirect ((payload.lift 1).substAt 0 value)) value)) _
  simpa only [Term.lift_substAt_cancel] using (memberUpperDirectSteps hd hv).appArg hk

end CDotFCCT.CTML.Coercion
