# cDOT Lean port

This directory contains a Lean 4 port of the Coq development in `../cdot`.
The project is pinned to Lean 4.34.0 and Mathlib 4.34.0.
It also loads the FCCT library from the Git submodule at `../external/ctml/fcct/lean`.

## Build

```sh
git submodule update --init external/ctml
cd lean
lake exe cache get Mathlib.Data.Finset.Basic Mathlib.Tactic
lake build CDot FCCT
```

The checked-in Lake manifest pins the dependencies; `lake update` is only needed
when changing those pins. Fetch the Mathlib cache before building to avoid
compiling it from source.

## FCCT connection

FCCT is a local Lake dependency whose source is pinned by the parent Git
submodule entry. A future `CDotFCCT` library can import both `CDot` and `FCCT`
without copying either calculus. Keep the translation and its correspondence
proofs in this repository; changes to FCCT itself belong in the submodule.

See [the review](../notes/fcct-review.md) for the baseline comparison and the implemented
Z primitive, including its safety and nontermination proofs. The independent FCCT audit can
also run from this project:

```sh
lake env lean ../notes/fcct/Audit.lean
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
| `Narrowing.v` | `CDot/Narrowing.lean` | Typing and subtyping narrowing ported |
| `RecordAndInertTypes.v` | `CDot/RecordAndInertTypes.lean` | Core record/inert opening, context invariants, and record-member uniqueness ported |
| `Replacement.v` | `CDot/Replacement.lean` | Replacement algebra, opening composition, insertion, field elimination, and substitution ported |
| `PreciseFlow.v` | `CDot/PreciseFlow.lean` | Precise path flow and value typing judgments ported |
| `PreciseTyping.v` | `CDot/PreciseTyping.lean` | Second/third-level precise typing, decomposition, singleton inversion, strengthening, and context well-formedness ported |
| `TightTyping.v` | `CDot/TightTyping.lean` | Tight judgments and tight-to-general translation ported |
| `InvertibleTyping.v` | `CDot/InvertibleTyping.lean` | Invertible path/value judgments and function, record, selection, lambda, and object inversion ported |
| `ReplacementTyping.v` | `CDot/ReplacementTyping.lean` | Replacement typing, closure under typed replacement, path selection, and function/object shape recovery ported |
| `InvertibleSubtyping.v` | `CDot/InvertibleSubtyping.lean` | Semantic subtyping, semantic-to-tight translation, inversion, and transitivity infrastructure ported |
| `Substitution.v` | `CDot/Substitution.lean` | Opening/substitution invariants and mutual substitution for typing, definition typing, and subtyping ported |
| `GADTRules.v` | `CDot/GADTRules.lean` | Derived singleton replacement and inversion rules ported |
| `Lookup.v` | `CDot/Lookup.lean` | Lookup semantics, irreducibility, and determinism ported |
| `Reduction.v` | `CDot/Reduction.lean` | Complete reduction and normal-form definitions ported |
| `GeneralToTight.v` | `CDot/GeneralToTight.lean` | General-to-tight conversion and precise canonical-type extraction ported |
| `CanonicalForms.v` | `CDot/CanonicalForms.lean` | Lookup preservation, finite alias resolution, and function/object/tag canonical forms ported |
| `Safety.v` | `CDot/Safety.lean` | Progress, preservation, finite-reduction safety, path safety, and extended soundness ported |

## Soundness theorems

The migration's final acceptance criterion is satisfied by the following
declarations in `CDot/Safety.lean`:

- `progress`
- `preservation` and `preservationStar`
- `safety`
- `pathSafety`
- `extendedSafety`

The complete project builds without `sorry`, `admit`, or custom `axiom`
declarations.
