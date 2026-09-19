# cDOT Lean port

This directory contains a Lean 4 port of the Coq development in `../cdot`.
The project is pinned to Lean 4.34.0 and Mathlib 4.34.0.
The core-DOT translation targets CTML Core with native records, intersections,
unions, Z, and scoped recursive type declarations, loaded from
`../external/ctml/lean/CTMLCore` across the Git submodule boundary. The original
FCCT library at `../external/ctml/fcct/lean` remains available for the baseline review.

## Build

```sh
git submodule update --init external/ctml
cd lean
lake exe cache get Mathlib.Data.Finset.Basic Mathlib.Tactic
lake build CDot CDotFCCT CTMLCore FCCT
```

The checked-in Lake manifest pins the dependencies; `lake update` is only needed
when changing those pins. Fetch the Mathlib cache before building to avoid
compiling it from source.

## CTML Core connection

`import CDotFCCT.CTML` loads the ongoing translation and its checked CTML components.
Records and projections use native CTML syntax. Existential packages and computations
use continuations; their record payloads remain native. Object evaluation uses the Z
primitive. Recursive
witnesses use `CTMLCore.Recursive.HasType` and its proved operational safety theorem.
Native recursion admits record guards, including simultaneous equations such as
`A = {next : B}, B = {back : Unit ∪ A}` with no arrows in either equation.

The full typing-preserving translation is unfinished. The existing runtime pass
accepts the complete chosen core-DOT judgment, while the typing translation currently
covers an opened fragment, a type-only object constructor pass with generated recursive
alias witnesses, and concrete examples. The bounded constructor case also compiles
`let x = new … in x` at requested member bounds, checking them against its generated
witnesses with CTML's constraint solver. Both cases return target typing proofs for
the exact runtime compiler output. Unsupported cases fail explicitly, and the
bounded case preserves fuel exhaustion. The full-source member analysis computes
scoped witness names, with
proofs of coverage for recorded references, binder freshness, and target weakening;
its alias pass generates scoped native witness equations and guarded coercion
derivations, including field extensions. General member-bound generation and
discharge through opaque paths remain unfinished. See the
[translation status](../notes/fcct-translation.md) for precise coverage.

The `CTML.Mixed` target proves operational safety with ordinary record-guarded
recursion and inversion restricted to designated ghost fields. Its fixed field-label
policy separates those roles; arbitrary constraints and universals remain available.
The original shared-witness regression uses exactly its original two context guards.
Checked scalar and mutual record-recursive programs reduce to Unit, including a
constraint-abstracted cast using ghost inversion. The default runtime-label allocation
is proved disjoint from all carrier slots. Pure ghost cycles remain unguarded.

The actual `CarrierTranslation.compileSubtyping` now produces mixed derivations for
bounds, selections, intersections, variable paths, singleton transport and replacement.
Every relevant path gets a complete row of member and payload witnesses, including
members never directly selected. `compileVariable` types the exact `TermCPS.compile`
output for supported variable derivations. Generated packages bind all member and
payload witnesses; packing uses the producer's existing types. Whole-package identity
coercions and the closed package example reducing to Unit use the same mixed judgment.
Unsupported source cases still fail explicitly.

`CarrierConstructorCompilation` also derives mixed typing for the exact output of
both existing type-only constructor passes, retaining their generated alias interfaces
and native proofs. Its compatibility rule solves their existing simultaneous function
equations alongside the target's scalar and simultaneous record equations.
`TermCPSObjectTyping` proves the mixed object step from field/package induction hypotheses,
deriving its ordinary-label condition from the actual compiled fields. Mixed term
weakening permits packing arbitrary typed payloads without changing the runtime syntax.
`NativeFieldSharing.packTyping` generates a package sharing one member witness across
`head` and recursive `next`. These constructor lemmas do not yet supply the general
source-field invariant or unify alias interfaces with carrier interfaces. General
paths, constructors, dependent calls and recursive opening remain unfinished.

The earlier `CTML.Transparent` model and its recursive-package examples remain checked
experiments. Their arrow-only guard is not a requirement of the intended target.

`import CDotFCCT.Baseline` loads the earlier minimal-FCCT experiments. The compatibility
umbrella `import CDotFCCT` loads both. The implemented target calculi are local Lake
dependencies from the pinned submodule. Translation proofs and the isolated
`Transparent` and `Mixed` prototypes belong here; adopted changes to the target calculi belong
in that submodule.

See [the review](../notes/fcct-review.md) for the baseline comparison and the implemented
Z primitive, including its safety and nontermination proofs. The independent FCCT audit can
also run from this project:

```sh
lake env lean ../notes/fcct/Audit.lean
lake env lean ../notes/fcct/TranslationAudit.lean
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
