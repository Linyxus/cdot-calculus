# Complemented pure ghost codes are closed under recursive equations

`lean/CDotFCCT/CTML/ComplementedGhostCodes.lean` establishes the semantic closure
needed by the complemented-code representation. It adds no typing or subtyping
rule and does not constrain runtime payloads.

`Complementary A` says that, for every term and index, A's negative observation is
equivalent to absence of its positive observation. `complementary_guard` and
`guards_complementary` connect this property to the existing guard
`Top <= A | ~A` used by `ComplementedProduct`.

Both-polarity downward closure plus complementation makes a candidate static:
all its observations equal those at index zero (`downward_static`). This does
not hold merely from downward closure of positive observations.

Negation, unions, intersections, and reflective ghost records preserve the
property. `solution_complementary` proves it for the existing finite simultaneous
pure carrier solver, including negative recursive references. The proof unfolds
the solved equations and inducts on finite term size: observing a ghost field
visits a strictly smaller term. It does not introduce an arrow guard.

The leaf requirement is occurrence-sensitive. `LeavesComplementary parameters e`
requires complementation only for outer types appearing in expression e, so an
unrelated runtime type in the same environment remains unrestricted.

The scope-friendly theorem is `solution_guard`. Its `LeavesComplemented` premises
require completeness only through the current index. Clipping outer observations
at that index gives globally complemented parameters; the solver's per-index
locality transfers the resulting guard back to the original parameters.
`interpretation_guard` applies this result to actual mixed type interpretations.

`ComplementedCarrierAssumptions.guard` strengthens the provenance result to any
environment validating the generated fold/unfold equations. It reads outer leaves
as their weakened types in that same environment, and requires their actual
completeness guards only through the current index. Structural induction on field
subterms then proves each recursive name complete. The proof does not assume the
environment was produced by the chosen solver; it is suitable for a future sound
subtyping derivation rule using equation evidence.

`negativeCycle_complementary` and `negativeCycle_static` check the nonvacuous pure
equation `P = {code: ~P}`. There are no outer leaves in this example, and the record
is its only recursion guard.

What remains separate is syntactic certification and compiler generation. The
new theorems justify completeness of solved pure ghost codes semantically; they
do not themselves add completeness guards to a scoped typing context or prove a
general native record-complement rule. Native runtime records need not be
complemented, and arbitrary constrained recursive ghost equations remain outside
the pure solver grammar.
