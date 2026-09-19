import CTMLCore.Declarative.ExpansiveConcrete
import CTMLCore.Declarative.Lattice

/-!
# Record rules needed by the DOT translation

DOT's `rcdIntro` retypes a path from a typing of its projection. This is admissible
in CTML Core, including projections typed using subsumption and intersection
introduction. No new target typing or subtyping rule is required.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation

private theorem concreteProjectionInverse {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {term : Term} {type : WFTy s.typeDepth}
    (h : ExpansiveConcrete s context term type) :
    ∀ {record : Term} {field : FieldName}, term = .proj record field →
      HasType s context record (WFTy.record field type) := by
  induction h with
  | intersection _ _ ihLeft ihRight =>
      exact fun equal =>
        (HasType.intersection (ihLeft equal) (ihRight equal)).subsumption
          (.recordDistribution .intersection)
  | projection hRecord =>
      exact fun equal => Term.proj.inj equal |>.1 ▸ (Term.proj.inj equal |>.2 ▸ hRecord)
  | application | record | ascription | ifThen | ifElse | fixpoint =>
      exact fun equal => nomatch equal

/-- The target counterpart of DOT's path record introduction, in any context. -/
theorem projectionInverse {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {record : Term} {field : FieldName}
    {type : WFTy s.typeDepth} (h : HasType s context (.proj record field) type) :
    HasType s context record (WFTy.record field type) := by
  obtain ⟨concrete, hConcrete, hSub⟩ := h.toExpansiveConcrete
    (fun h => match h with | .value value => nomatch value)
  exact (concreteProjectionInverse hConcrete rfl).subsumption (.record hSub)

end CDotFCCT.CTML
