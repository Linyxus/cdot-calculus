import CDotFCCT.CTML.NativeFieldSharing
import CDotFCCT.CTML.MixedCarrierBounds
import CDotFCCT.CTML.MixedAssumptions
import CDotFCCT.CTML.MixedTypeWeakening
import CDotFCCT.CTML.MixedInterfaceWeakening

/-!
# Recursive field sharing for arbitrary mixed-target payloads

The native producer's runtime, interface and recursive equation are reused exactly.
Its stored payload may now itself use ghost inversion and any supported recursive
scope. The constructor still generates both hidden witnesses and both equation
proofs; it does not ask the caller for a carrier bound or recursive witness.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore CTMLCore.Syntax

/-- Native packing evidence is also valid with a fixed ghost-label policy. -/
def InterfaceInstance.ofNative {ghost : FieldName → Bool} {s : SubtypingContext}
    {interface : Interface s.typeDepth} {type : WFTy s.typeDepth}
    (inst : Interface.Instance s interface type) :
    InterfaceInstance ghost s interface type :=
  match inst with
  | .payload type => .payload type
  | .guard evidence rest => .guard (.native evidence) (ofNative rest)
  | .bind witness rest => .bind witness (ofNative rest)

end CDotFCCT.CTML.Mixed

namespace CDotFCCT.CTML.MixedFieldSharing

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation Mixed

export NativeFieldSharing (objectType body interface object interface_weaken)

/-- Both ordinary field labels guard the existing recursive record equation. -/
def definition {n : Nat} (member answer : WFTy n) : Mixed.Definition carrierPolicy n :=
  ⟨(NativeFieldSharing.definition member answer).body, by
    change Mixed.GuardedAt carrierPolicy 0
      (Ty.joint .intersection (.record "head" _) (.record "next" _))
    exact ⟨True.intro, True.intro⟩⟩

theorem definition_native {n : Nat} (member answer : WFTy n) :
    (definition member answer).native = NativeFieldSharing.definition member answer := rfl

theorem objectTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {payload : Term} {member answer : WFTy s.typeDepth}
    (typing : Mixed.HasType carrierPolicy s context payload member) :
    Mixed.HasType carrierPolicy ((definition member answer).native.openContext s) context.bindType
      ((object payload).liftTy 1) (objectType (definition member answer).native.name) := by
  refine .fixpoint (.abstraction (.abstraction (.subsumption (.record
    (fieldTypes := [("head", Coercion.observation member.weaken answer.weaken),
      ("next", Coercion.observation
        (objectType (definition member answer).native.name) answer.weaken)])
    (.cons (.abstraction (.application (.native (.var _ 0 _ .here)) ?_))
      (.cons (.abstraction (.application (.native (.var _ 0 _ .here))
        (.native (.var _ 2 _ (.there (.there .here)))))) .nil))) ?_)))
  · have lifted := ((typing.weakenType.weakenAssumption
      (WFConstraint.constr (definition member answer).native.name
        (definition member answer).native.body)).weakenAssumption
        (WFConstraint.constr (definition member answer).native.body
          (definition member answer).native.name))
    have selfLifted := lifted.weakenFront (objectType (definition member answer).native.name)
    have allLifted := (selfLifted.weakenFront WFTy.top).weakenFront
      (WFTy.arrow member.weaken answer.weaken)
    change Mixed.HasType carrierPolicy ((definition member answer).native.openContext s) _
      ((payload.lift 3).liftTy 1) member.weaken
    rw [← Term.liftTy_liftAt_comm payload 0 3 1]
    have shift : (((payload.liftTy 1).lift 1).lift 1).lift 1 =
        (payload.liftTy 1).lift 3 := by
      simp only [Term.lift, Term.liftAt, Term.renameWith_renameWith, Nat.zero_le, ite_true]
    rw [shift] at allLifted
    exact allLifted
  · exact .native ((Subtype.leInter (.trans .interLeft .interRight) .interRight).trans
      ((definition member answer).native.fold s))

/-- The constructor chooses both hidden witnesses and proves both recursive guards.
 Its only input derivation is the existing mixed typing of its stored member value. -/
theorem packTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {payload : Term} {member answer : WFTy s.typeDepth}
    (typing : Mixed.HasType carrierPolicy s context payload member) :
    Mixed.HasType carrierPolicy s context (pack (object payload))
      ((interface answer).package answer) := by
  refine .recursive (definition member answer) ?_
  rw [RecursivePackage.pack_liftTypes, (interface answer).package_weaken, interface_weaken]
  exact Mixed.interfacePackTyping
    (Mixed.InterfaceInstance.ofNative (NativeFieldSharing.interfaceInstance
      (s := (definition member answer).native.openContext s)
      member.weaken (definition member answer).native.name answer.weaken
      ((definition member answer).native.unfold s) ((definition member answer).native.fold s)))
    (objectTyping typing)

end CDotFCCT.CTML.MixedFieldSharing
