# cDOT Lean port

This directory contains a Lean 4 port of the Coq development in `../cdot`.
The project is pinned to Lean 4.32.0 and mathlib 4.32.0.

## Build

```sh
cd lean
lake update
lake build
```

## Porting policy

- The Coq syntax and inference rules remain the specification.
- The Lean development does not use `sorry` or custom axioms.
- A module is marked complete only after its declarations and required proofs
  have been translated and accepted by `lake build`.

## Correspondence and status

| Coq module | Lean module | Status |
| --- | --- | --- |
| `Definitions.v` | `CDot/Definitions.lean` | Syntax, opening, free variables, path replacement, environments, record/inert types, typing, subtyping, and store typing ported |
| `Sequences.v` | `CDot/Sequences.lean` | Core finite/infinite sequence theory and determinism lemmas ported |
| `Binding.v` | `CDot/Binding.lean` | Core opening/substitution commutation, freshness, environment, definition lookup, and path-comparability lemmas ported |
| `Weakening.v` | `CDot/Weakening.lean` | Weakening for typing and subtyping ported |
| `Subenvironments.v` | `CDot/Subenvironments.lean` | Subenvironment relation and binding inversion ported |
| `Narrowing.v` | `CDot/Narrowing.lean` | Mutual narrowing theorem ported |
| `RecordAndInertTypes.v` | `CDot/RecordAndInertTypes.lean` | Core record/inert opening and context invariants ported |
| `Replacement.v` | `CDot/Replacement.lean` | Core replacement algebra ported |
| `PreciseFlow.v` | `CDot/PreciseFlow.lean` | Precise path flow and value typing judgments ported |
| `PreciseTyping.v` | `CDot/PreciseTyping.lean` | Second/third-level judgments and core decomposition lemmas ported; advanced inert-context lemmas pending |
| `TightTyping.v` | `CDot/TightTyping.lean` | Tight judgments and tight-to-general translation ported |
| `InvertibleTyping.v` | `CDot/InvertibleTyping.lean` | Invertible path/value judgments and core decomposition ported; canonical-form lemmas pending |
| `ReplacementTyping.v` | `CDot/ReplacementTyping.lean` | Replacement path/value judgments and intersection decomposition ported; closure lemmas pending |
| `InvertibleSubtyping.v` | `CDot/InvertibleSubtyping.lean` | Semantic judgment and semantic-to-tight translation ported; transitivity/tight-to-semantic pending |
| `Substitution.v` | `CDot/Substitution.lean` | Structural substitution invariants ported; mutual typing substitution theorem pending |
| `GADTRules.v` | `CDot/GADTRules.lean` | Derived singleton replacement rules ported; inversion theorems pending |
| `Lookup.v` | `CDot/Lookup.lean` | Lookup semantics, irreducibility, and determinism ported |
| `Reduction.v` | `CDot/Reduction.lean` | Complete reduction and normal-form definitions ported |
| `GeneralToTight.v`, `CanonicalForms.v`, `Safety.v` | — | Pending |

The final acceptance criterion is a proof of the counterparts of `safety` and
`extended_safety` from `cdot/Safety.v`, with no `sorry` declarations.
