# Structural field views and opaque selected types

`CTML/CarrierFieldViews.lean` checks the part of a flattened carrier representation
that is already justified. A precise parent carrier assigns one shared witness
to each `(field, member)` coordinate. The child's carrier reuses the same witness
at its unprefixed member coordinate. For any target context, support lists, lower
bound `L`, and upper bound `U`, `flattened_member_iff` proves

```
precise(parent) <: memberView((a, A), L, U)
    iff
precise(child a) <: memberView(A, L, U).
```

Both sides are equivalent to `L <: witness(a, A) <: U`. The proof uses the existing
paired-slot reflection and covariance rules under `Mixed.carrierPolicy`. It adds
no assumptions, new target rules, or recursive ghost equations. The same result
applies when the shared witness is itself an arbitrary selected target type;
the member declaration surrounding that witness must be structurally visible.
This is the local entailment needed for both `newElim` and `rcdIntro` on that visible
member shape. It is not a complete field-type encoder.

## The smallest remaining shape problem

The same file includes checked core-DOT derivations in this context:

```
q : { X : Bottom .. Top } & { Y : Bottom .. { a : q.X } }
p : q.Y
```

`parentView` derives `p : {a : q.X}` using the upper bound of `q.Y`, without knowing
any constructor for `p`. `eliminated` then derives `p.a : q.X` with `newElim`;
`introduced` uses `rcdIntro` to recover the parent view. These are actual source
derivations, checked against the repository's source judgment. The example needs
no recursive source types or inconsistent bounds.

Write `P(p)` for the parent's flat precise carrier and `P(p.a)` for the child's
reindexed carrier. Encoding the field type must provide some target expression
`fieldView(a, X)` for the opaque scalar witness `X` representing `q.X`, with the
two translations establishing

```
P(p) <: fieldView(a, X)    implies    P(p.a) <: X
P(p.a) <: X               implies    P(p) <: fieldView(a, X).
```

The current `CarrierTranslation.TypeCode.selection` represents `q.X` by one
ordinary `WFTy` variable. The structural theorem reindexes a known member view;
it cannot inspect the unknown type later substituted for `X`. Ordinary type
substitution replaces variables but does not relabel the record labels inside
an unknown argument. This identifies the missing representation operation;
it is not a proof that no FCCT encoding can express it.

Giving each opaque witness independent copies `X_empty`, `X_a`, and so on does
not discharge the obligation: the forward rule still needs to transport
`P(p) <: X_a` into `P(p.a) <: X_empty`, and the converse needs the reverse
transport. A successful family-based encoding must generate this coherence
from the same source assumptions and witness choices. Adding those desired
inequalities as free target assumptions would bypass the source proof.

## Interaction with the runtime proof

The checked runtime anchor fixes the entire child's witness vector and supports
packing and unpacking that vector. An ordinary recursive runtime field can contain
the anchor while satisfying record guarding. For a constructor with known child
origin, the existing source child derivation can also widen its package to a
particular translated view. Those facts do not establish the generic opaque
parent-view transport above.

Putting the entire child carrier inside a reflective ghost slot represents
`{a : q.X}` directly, but equating such a child with its parent on a self-field
cycle can require a ghost-only recursive equation. The current sound recursion
rule rejects that equation. This is a limitation of that encoding choice, not a
failure of record-guarded runtime recursion. The next representation should be
tested against the displayed two implications, including an opaque `X`, before
extending the full derivation compiler.
