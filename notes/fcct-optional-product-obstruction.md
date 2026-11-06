# Optional products still lose a relation across observation gaps

`lean/CDotFCCT/CTML/OptionalProductObstruction.lean` tests a carrier with four
distinct ghost fields. Each component has both a positive and a negative slot:

```
Test(T) = UnitClass | {value: T}
P(A,C)  = {member+: Test(A)} & {member-: Test(~A)}
        & {child+:  Test(C)} & {child-:  Test(~C)}
```

All five field labels are reflective ghost labels. `interpret_product` identifies
this model with the existing native type syntax, without adding a rule or changing
the target interpretation. `default_positive` supplies a concrete record inhabitant
using Unit in every slot, including for the bad tuple below.

The target model keeps positive and negative observations independent. Consider
two constant, downward-closed candidates:

| Candidate | Positive observations | Negative observations |
|---|---|---|
| Gap | false | false |
| Top | true | false |

Both are consistent: neither accepts and rejects the same term. Both legal
diagonal assignments satisfy `Gap <= Gap` and `Top <= Top`. However:

```
P(Gap,Top) <= P(Top,Top) | P(Gap,Gap)
Top </= Gap
```

The first inclusion is `gap_crossed`, checked at every step index. Every positive
observation of the crossed product belongs to the Top diagonal. Every negative
observation of the Gap diagonal is also a negative observation of the crossed
product. The second inclusion fails already at index zero on `var 0`.

Consequently any fixed upper candidate accepting the two legal diagonal products
also accepts the illegal crossed product. `no_consistent_uniform_bound` rules out
`P(A,C) <= M iff C <= A`, even when quantified witnesses must be consistent and
downward closed. The result concerns every semantic candidate M, so choosing more
elaborate scalar type syntax cannot repair this particular representation.

The file also checks the proposed uniform existential directly:

```
Require(Q,T) = ~(Q => ~T)
Exists X.T  = ~Forall X.~T
M = Exists C. Exists B. Require(C <= B, P(B,C))
```

`interpret_relationBound` connects the concrete native syntax to its model.
`existential_counterexample` shows that M accepts `P(Gap,Top)` at every index.
The literal one-existential form with an already fixed external C is a different
claim; this obstruction does not rule it out. Retaining C as an external parameter
does not provide a fixed bound for an unknown subject's own child witness.

This is a representation obstruction, not an impossibility result for FCCT.
Gap is a legal environment/universal candidate; the file does not claim that Gap
is denoted by a closed source type. A compiler could establish a stronger invariant
on generated packages, or retain generated correlation evidence. Such an invariant
must be generated from source derivations and survive abstraction, recursion, and
multiple views. Merely excluding contradictory candidates is insufficient.
