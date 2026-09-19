# Whole-child carrier equations

This is a representation audit, not a new recursive-type rule. The existing
mixed model rejects recursive equations guarded only by ghost records. A separate
experiment is investigating a narrower class of Boolean ghost-row equations.

## Notation and field transport

Use one finite support with distinct slot keys for the runtime payload, each
source type member, and each demanded child field. Each slot has the existing
negative and positive ghost labels. Write

```
P(D, W, C) = row(payload = D; member A = W_A; child a = C_a)
```

for the existing `CarrierLayout.precise` construction. Its row is a **union** of
labelled alternatives, with `¬V` in a slot's lower label and `V` in its upper
label. These ghost rows are not runtime object records. All labels here satisfy
`carrierPolicy`; actual runtime field labels remain ordinary.

Define the member and field views using the existing `MemberSlot.view`:

```
M_A(L,U) = memberSlot(A).view L U TopRest
F_a(T)   = childSlot(a).view Bottom T TopRest.
```

`CarrierFieldViews.whole_child_iff` now checks, for an arbitrary target context
and arbitrary opaque target type `X`,

```
P(D,W,C) <: F_a(X)    iff    C_a <: X.
```

The proof uses paired-slot inversion and variance. It does not inspect `X` or
introduce a constraint assumption. If `C_a` is the actual precise carrier of
`p.a`, this is exactly the shared carrier entailment needed by `newElim` and
`rcdIntro`. If `P` and `C_a` are recursive names, their generated fold/unfold
equations must connect those names to the displayed precise rows.

## Equations for the requested cases

The equalities below require both subtyping directions in the eventual scoped
target derivation. They are proposed equations; the checked mixed target does
not yet admit their ghost-only recursive parts.

| Source shape | Carrier or member equation | Classification |
| --- | --- | --- |
| Runtime field `a = self` | `P = P(D,W, child a = P)` | Pure ghost row in `P`, with `D` and unrelated members as parameters; includes both `¬P` and `P`. |
| Type member `A = {a : self.A}` | `W_A = F_a(W_A)` | Pure ghost row; recursive occurrence below the child's positive label. |
| Type member `A = {X : self.A .. self.A}` | `W_A = M_X(W_A,W_A)` | Pure ghost row; recursive occurrences have both polarities. |
| Opaque field type `{a : q.X}` | View `F_a(W_qX)` | No new equation is needed merely for the view; `W_qX` is an unchanged scalar witness. |

Other slots in each view contain `Top`. A whole carrier for the object also
contains the paired slot for `W_A`; therefore carrier and member equations may
form one finite simultaneous system. Source member bounds become signed row
components here, not embedded FCCT constraint expressions. The third equation
therefore does not place a recursive variable in a constraint endpoint.

For the opaque case, the missing flattened-coordinate relabeling operation
disappears: `C_a <: W_qX` uses the original witness. This does not by itself type
the runtime projection or allocate the child carrier. Those obligations still
need the compiler's runtime anchor and path-allocation invariant.

## Runtime self aliases couple two kinds of equations

Let `R` be the CPS answer type and write

```
Anchor(P,R) = continuation-encoded
                (exists fresh witnesses V. precise(V) <: P; payload(V)).

P = P(D,W, child a = P)
D = Unit -> row
row = { ordinary a : Anchor(P,R) }.
```

The first equation is a ghost-row equation. The last equation has an ordinary
record guard. The intermediate arrow is the existing runtime thunk convention;
record guarding is already sufficient for the recursion through the package.
Inside `Anchor`, the fixed carrier `P` occurs in a constraint endpoint, but that
occurrence is below the ordinary field in the equation for `row`. The package
also has its usual CPS arrow. This does not require accepting an occurrence in
a constraint endpoint protected only by ghost records.

Treating `D` as a parameter solves only the ghost part of this coupled system.
After solving the ghost equation, `D` still depends back on its solution through
the runtime package. Merely treating that dependency as an opaque constant would
leave the joint fixed-point obligation unproved.

## Requirements for a reusable solver

A parameterized pure-row solver could compose with the existing ordinary-record
fixed point if it supplies all of the following:

- A simultaneous solution for finitely many Boolean ghost-row equations, allowing
  unions, intersections, negation, fixed external candidates, and guarded recursive
  variables of either polarity. All requested type-member cycles fit this shape.
- Downward closure of its solutions when its parameters are downward closed.
- Locality in the parameters: agreement through index `n` implies agreement of
  solved carriers through `n`. Then an ordinary record surrounding an anchor
  makes the remaining runtime-row operator contractive in the step index.
- Both directions of each solved equation, with the existing ghost-row reflection
  laws. The current `whole_child_iff` can then be applied unchanged.

An alternative is one finite-system solver whose recursion decreases either the
step index at ordinary records/arrows or term size at ghost records. In either
approach, same-index recursive constraint endpoints must remain outside the
pure-row fragment: the inclusion test quantifies over arbitrary terms, so a
previous ghost-record observation does not supply a decreasing term-size bound
for that test. The exported equation guards themselves are not this forbidden
case; they are validated after the candidate solution has been constructed.

The four cases above do not establish a general compiler invariant. In particular,
the compiler must allocate a finite graph of demanded paths, keep aliases on the
same carrier nodes, preserve all demanded suffixes, and generate equations from
the source derivation. It must also handle unguarded aliases or Boolean cycles
not covered by the selected solver's grammar. A family of unconstrained carrier
names, or extra desired child bounds, would not satisfy these obligations.
