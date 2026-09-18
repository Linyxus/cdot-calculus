# FCCT review and cDOT connection

Review date: 2026-09-18.

The existing development is a suitable **call-by-value FCCT safety baseline**. Its
subtyping matches the supplied paper, its two restrictions on typing are explicit,
and its progress and preservation proofs build without additional axioms. It is
not a mechanization of the paper's original call-by-name system or of all the
paper's results.

The target for the cDOT connection is **FCCT extended with a primitive
CBV fixpoint Z**. This addresses the termination mismatch without requiring the
source calculus to exclude recursion. The extension is now implemented and its
safety proofs checked; a cDOT translation remains future work.
Both projects have been upgraded to Lean 4.34.0, and the cDOT Lake project loads
FCCT as a local dependency across the submodule boundary.

## Sources and reproducibility

- Original paper: *First-Class Constrained Types: Elaboration, Type Inference,
  Approximation, and a Characterization of Termination*, by Chun Kit Lam, Florent
  Ferrari, and Lionel Parreaux. Reviewed the supplied source rooted at
  `/Users/parreaux/work/Research/papers/first-class-polym/constrained-types-paper-new/paper.tex`.
  Its containing repository was at `be49d848d8175a8e7819cefe5282f8be7992cdae`;
  the core rule files and soundness/termination sections were unchanged locally.
- Reviewed mechanization: [CTML upstream](https://github.com/maximemulder/ctml), commit
  `8bd1529f58875d7be1db26626c9f9bb4e0904449`, under `fcct/lean/`.
  The companion note is under `fcct/latex/`. The upstream branch
  `lean-context-join` was checked to contain that exact commit.
- Imported baseline: the [fcct-with-fixpoint branch on LPTK/ctml](https://github.com/LPTK/ctml/tree/fcct-with-fixpoint),
  initially at commit `b7df420` (Lean 4.34.0 upgrade), which changed only the
  toolchain, deprecated lemma names, and version documentation. The branch now
  extends this baseline with the Z primitive described below, at commit
  `7a9be5a`; the parent repository's submodule entry pins that extension revision.
- Local source checkout: `/Users/parreaux/work/Research/papers/ctml/fcct`.
  This is a directory within the CTML Git repository, not a separate repository.
  Accordingly, [external/ctml](../external/ctml) pins CTML as a submodule; the FCCT
  library is [external/ctml/fcct/lean](../external/ctml/fcct/lean).
  The source checkout's modified generated PDF was not imported.
- cDOT specification: [Coq definitions](../cdot/Definitions.v) and the
  [Lean definitions](../lean/CDot/Definitions.lean), with the
  [store-based reduction relation](../lean/CDot/Reduction.lean).

The rule comparison and proof review concentrate on the declarative calculus,
binding, subtyping inversion, simplification, and syntactic safety. The paper's
elaboration, inference, approximation, and intersection discussion were used to
establish scope and implications for the encoding. This is not a line-by-line
verification of those unmechanized algorithms and their proofs.

From the cDOT repository root:

```sh
git submodule update --init external/ctml
cd external/ctml/fcct/lean
lake build
lake env lean ../../../../notes/fcct/Audit.lean
```

Both projects now use **Lean 4.34.0**, the
[latest stable Lean release](https://github.com/leanprover/lean4/releases/tag/v4.34.0)
as checked on the review date. cDOT uses the
[matching Mathlib release](https://github.com/leanprover-community/mathlib4/releases/tag/v4.34.0),
pinned at `5ed2965256430c3649e86755f9576b54eca72435`; FCCT still depends only on Lean core.

The original baselines used Lean 4.32.0 for cDOT and 4.33.0 for FCCT. An attempted
FCCT build on 4.32.0 failed in `FCCT/Inversion.lean:819`, at `rw [List.map_map]`
in `Subtype.closeWith`, because of a dependent-type transparency mismatch.
Upgrading both projects resolves that build boundary. The FCCT toolchain upgrade needed only updates
to deprecated `if_*` lemma names, plus its toolchain and version documentation;
its calculus and theorem statements were not changed.

To build both libraries together from the cDOT repository root:

```sh
git submodule update --init external/ctml
cd lean
lake exe cache get Mathlib.Data.Finset.Basic Mathlib.Tactic
lake build CDot FCCT
lake env lean ../notes/fcct/Audit.lean
```

The cache command retrieves the imported Mathlib modules and their dependency
closure. It supplied all 3,076 requested files for this upgrade; Mathlib's
mathematical library was not rebuilt from source. Building the cache downloader
itself is a small, separate prerequisite.

Validation performed:

- A fresh archive of the committed FCCT sources built successfully on 4.33.0
  (21 Lake jobs), independently of existing build artifacts.
- The imported submodule was built and the independent audit was checked there.
- `lake build CDot FCCT` passes on Lean 4.34.0, and one Lean file importing
  **both** full libraries checks successfully. cDOT's progress, preservation,
  safety, and extended safety also depend only on the standard three axioms.
  The cDOT build retains non-fatal style and unused-section-variable warnings.
- Source scanning found no `sorry`, `admit`, custom `axiom`, `unsafe`,
  `implemented_by`, `extern`, `partial`, `native_decide`, or `sorryAx` occurrences
  in the project's Lean source files.
- The audit prints the axioms of the main inversion, substitution,
  simplification, and safety theorems. Only `propext`, `Quot.sound`, and, for
  some theorems, `Classical.choice` occur. Evaluation determinism is axiom-free.
- The audit also proves a counterexample to a uniform reading of the paper's
  prefix-removal lemma. That proof uses only `propext` and `Quot.sound`.

## Connecting the Lean projects

Git and Lake have separate responsibilities: the submodule pins the exact FCCT
source revision, and this local dependency in `lean/lakefile.toml` makes its
library available to Lean:

```toml
[[require]]
name = "fcct"
path = "../external/ctml/fcct/lean"
```

Put the translation in a separate `CDotFCCT` library in this repository's `lean/`
project. Its modules can import `CDot.Definitions` and `FCCT.Typing`, and later
their metatheory. Neither base calculus needs to import the other. This retains
one Mathlib dependency/cache while giving the bridge access to both namespaces.

The bridge should contain type/context/term translations or translation
relations, typing and subtyping preservation, and an operational correspondence
theorem. The operational theorem should relate cDOT store-and-term
configurations to FCCT terms, with a sequence of target steps accounting for
CPS and other administrative reductions. It should distinguish a simulation
that permits zero steps from the stronger progress condition needed to preserve
divergence.

Changes to the FCCT calculus, including the planned Z primitive, belong in the
submodule. Commit and publish those changes in CTML or a fork before sharing a
parent revision that points to them. The parent repository records the new
gitlink; the translation remains here and is checked against that exact version.

## Definition comparison

The relevant paper files are `sections/language.tex`, `figures/decl-typing.tex`,
`figures/subtyping.tex`, and `sections/aux-defs.tex`. The active syntax figure is
embedded in `sections/language.tex`; `figures/syntax.tex` is an older, uninputted
figure and should not be used as the specification.

| Feature | Paper | Mechanization | Assessment |
| --- | --- | --- | --- |
| Types | Variables, Bool, arrows, universals, constrained types | Same constructors in `Syntax.Ty` | Matches |
| Terms | Variables, lambda, application, true/false | Same constructors in `Syntax.Term` | Matches |
| Constraints | Arbitrary subtyping assumptions, including inconsistent ones | `WFConstraint`, assumed without a consistency test | Matches |
| Contexts | Named, mixed typing context with freshness convention | Separate term context and type-depth/constraint context; de Bruijn indices | Standard representation change |
| Well-formedness | Explicit premises | `WFTy n` and `WFConstraint n` carry scope proofs | Scope requirements retained intrinsically |
| Subtyping | Hypothesis, transitivity, function variance, three forall rules, three constraint rules; base reflexivity | Same rules, with general reflexivity primitive | General reflexivity is admissible in the paper |
| Universal introduction in subtyping | Only a fresh, unused binder | `forallRight : T ≤ ∀. T.weaken` | Freshness enforced by construction |
| Universal elimination in subtyping | Instantiate with any well-formed type | `forallLeft`, with a `WFTy` argument | Impredicative instantiation retained |
| Constraint introduction in subtyping | Guard must be well-formed, not provable | `constrainedRight` takes a `WFConstraint` | Matches; no hidden consistency restriction |
| Constraint elimination | Guard must be derivable | `constrainedLeft` has a subtyping premise | Matches |
| Ordinary typing | Variable, Bool, lambda, application, subsumption | Same | Matches |
| Universal/constraint introduction in typing | Any term | Only `Nonexpansive` terms: values or variables | Intentional restriction |
| Evaluation | CBN beta and function-position congruence | Left-to-right CBV, with value arguments to beta and argument congruence | Intentional semantic change |
| Top level | Empty context and weak-head type | Safety at empty contexts and **any** closed type | Valid for the changed, restricted system |

`bindType` weakens existing assumptions and term-variable types, so a fresh
quantified variable cannot accidentally occur in an older binding. Type
substitution changes contexts and types, not terms: terms have no type
annotations. Function subtyping has the expected contravariant domain and
covariant codomain.

The value restriction on constraint introduction is necessary for this CBV
semantics. Let `c = Bool ≤ Bool → Bool`. With the paper's unrestricted rule,
`true false` can receive type `c ⇒ Bool` in the empty context. Consequently,

```text
(λz. λw. w) (true false)
```

has an ordinary arrow result type but is stuck under CBV. CBN ignores the
argument. The mechanization prevents this derivation because applications are
not nonexpansive. Variables are admitted because CBV beta substitutes values;
the term-substitution theorem correctly requires a nonexpansive replacement.

The additional restriction on universal introduction is documented as a proof
convenience. It really is a restriction, so the paper's unrestricted typing,
principality, completeness, and beta-expansion results cannot simply be reused
for this variant. The stronger safety conclusion at arbitrary types should not
be confused with a stronger typing system.

## Proof review and paper discrepancy

The mechanized chain is:

```text
substitution and assumption discharge
    → subtyping inversion / prefix removal
    → typing simplification
    → canonical forms
    → progress and preservation
    → safety along finite reduction sequences
```

`HasType.soundness` quantifies over **every** supplied finite `Steps` derivation
from a closed well-typed term. It retains the same type and establishes that the
reached term is a value or can step. It does not assert termination.

The crucial proof is genuinely different from the paper's rewriting sketch.
`Subtype.lands` transports a structurally defined predicate backwards along a
subtyping derivation. A constrained type records both a derivation of its guard
and the guard's transport property; the latter justifies the `S-Hyp` case.
Universals quantify over sound candidates rather than recursively invoking the
predicate on an arbitrarily larger instantiated type. The closed arrow and
prefix-removal results discharge the semantic environment/context conditions
using a sound trivial environment and the empty assumption list. No unproved
semantic condition remains in their public statements.

`HasType.simplifyAux` uses a size-indexed typing relation and keeps discharged
guards as grounded assumptions until the end. Type instantiation preserves that
size. This avoids relying on the paper's claim that replacing uses of a guard
with proofs decreases its global rewriting measure.

**The paper-to-Lean correspondence overstates Lemma C.10.** Here “C.10” is the
number used by the mechanization; the source is
`sections/syntactic-soundness.tex:488–550`, label `lem:discharge-useless`.
Its item (3), read literally, asks for one weak-head replacement `T₁` preserving
all judgments `τ ≤ T₂`. That uniform claim is false:

1. Take `τ = ∀α. α`. Universal elimination derives both `τ ≤ Bool` and
   `τ ≤ Bool → Bool`.
2. A closed weak-head type below `Bool` must be `Bool`.
3. `Bool` is not a subtype of `Bool → Bool`.

Thus no single weak-head `T₁` preserves both uses. This is checked in
[Audit.lean](fcct/Audit.lean), theorem `noUniformPrefixFreeReplacement`.

The Lean theorem `Subtype.instantiationOfPrefixFreeSupertype` instead fixes
**one target** `sup` and obtains an instantiation below that target. It removes
one universal layer; it does not promise that the resulting type is already
prefix-free or that it works for every other target. This is the appropriate
property for its simplification proof. Likewise, the guard-discharge theorem
does not claim the paper's literal bound on derivation depth.

This finding calls for tightening the correspondence documentation and the
paper lemma's quantifiers/measure, not rejecting the Lean safety theorem. No
blocking defect was found in the CBV definitions or the checked safety chain.
The review does not claim a mechanized equivalence with the named-variable
paper calculus.

## What is outside this mechanization

The FCCT library does not contain:

- the original unrestricted CBN typing/evaluation system;
- the System F elaboration, erasure, and simulation proofs;
- the paper's top-level CBN termination theorem;
- principal inference, its completeness, or the characterization of termination;
- the approximating/context-sensitive inference system;
- records, intersections, path-dependent types, existential syntax, object
  identity, pattern matching, or a cDOT translation.

The larger CTML submodule contains other developments, but those do not become
FCCT theorems merely by being present in the same repository.

## Implemented extension: a primitive Z

The initial termination mismatch is addressed by a primitive value `Z`, with the type scheme

```text
Z : ∀A. ∀B. ((A → B) → A → B) → A → B
```

and a reduction rule, for a value `f`,

```text
Z f  →  λx. f (λy. Z f y) x
```

Here `x` and `y` are fresh, with capture-avoiding lifting in de Bruijn syntax.
The eta-expanded recursive argument is a value, so CBV does not immediately
unfold it before invoking `f`. This is a primitive typed operation; it is not a
claim that the untyped Z combinator has this scheme in the existing FCCT.

For example, `f = λr. λx. r x` gives a closed diverging computation `Z f true`
at `Bool`, with `A = B = Bool`. Conversely, `Z (λr. λx. x) true` returns
`true`. Both are now proved in
[FixpointExamples.lean](../external/ctml/fcct/lean/FCCT/FixpointExamples.lean):
`terminatingSteps` gives the terminating reduction; `loopDoesNotTerminate`
rules out every reduction from the looping term to a value, using a five-step
cycle and determinism. `loopTyping` assigns that term `Bool`.

The **type syntax and subtyping relation are unchanged**. `Term.zfix`, `Value.zfix`,
`HasType.zfix`, and `Step.appZ` supply the constant and its rules. Scoping,
renaming, substitution, size-indexed typing, and typing simplification include
the new cases. `HasType.canonicalForm` now admits either an abstraction or `Z`.
Progress, preservation, soundness, and determinism are proved for the extension.
The landing-predicate proof is reused unchanged.

[Fixpoint.lean](../external/ctml/fcct/lean/FCCT/Fixpoint.lean) derives the
first-class universal type (`HasType.polyZ`) and types the delayed unfolding in
arbitrary contexts (`HasType.unfoldZ`). The latter supplies Preservation's new
case after simplification and arrow inversion. Additional examples check
argument evaluation and preservation through constraints and quantifiers.
All these files are included by `import FCCT`; the independent audit prints
their axiom dependencies alongside the existing safety chain.

Validation of the extension: standalone FCCT and combined `lake build CDot FCCT`
both pass on Lean 4.34.0. Mathlib reused its 3,076 cached files. The safety proofs
still use only `propext`, `Classical.choice`, and `Quot.sound`; determinism, the
terminating reduction, and the nontermination proof use no axioms. No `sorry`
placeholders or custom axioms are present.

The paper's termination theorem applies to its original closed, weak-head
program judgment, not to arbitrary guarded typings. In particular, it can type
a loop under undischarged impossible constraints. Adding Z intentionally
invalidates the top-level termination theorem and its characterization of
typability. The safety theorem is the property needed for the proposed target.

In DOT the corresponding source of recursion is the object **self binding**:
method bodies can refer to an object already assigned its declared interface.
For example, schematically:

```text
new (self : { loop : Top → Top }) {
  loop = λx : Top. self.loop x
}
```

Calling this method loops even though its interface contains no abstract type
member. Strong existentials alone do not account for this recursion. A Z
primitive supplies it independently of the existential encoding.

## CPS and existential direction

The universal and constraint rules retain the ingredients for a bounded weak
existential encoding. A candidate package with witness `A`, bounds `L ≤ A ≤ U`,
and payload `V(A)` has the continuation encoding

```text
ExistsBounded(L, U, V) =
  ∀R. (∀A. (L ≤ A) ⇒ (A ≤ U) ⇒ (V(A) → R)) → R
```

The result type `R` is outside `A`'s scope. A packer chooses a concrete witness,
proves its bounds, and passes the payload to the consumer. An unpacker supplies
a consumer checked under an abstract `A` and its bounds. Placing the universal
and constraint introductions around the consumer lambda respects the existing
CBV value restriction.

This is a proposed encoding, not a theorem established by this review. It
explains why moving the rest of a computation inside a continuation may turn
strong existential use into ordinary weak existential elimination. The paper's
discussion of encoding intersections in negative positions
(`sections/intersection.tex:27–40`) supports this direction, but is not itself
an encoding of cDOT intersections in arbitrary positions.

With Z and safety established, the first translation milestone should establish
packing/unpacking and a CPS typing lemma for a small fragment
with one abstract type member and its bounds. The remaining obligations include
maintaining witness identity across repeated path use and aliases, dependent
function results, records/intersections, object self binding, and cDOT's runtime
tags and case refinements. Reopening one package twice must not silently replace
one stable path type by two unrelated abstract types. These are separate proof
obligations beyond the availability of universals and recursion.
