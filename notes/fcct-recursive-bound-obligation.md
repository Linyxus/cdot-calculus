# First-class recursive bounds need a relation on the unknown self

`RecursiveCarrierBoundObstruction.lean` checks the actual source configuration

```
q : { X : Bottom .. μself.({ A : Bottom .. Top } & { a : self.A }) }
p : q.X
```

The recursive binder scopes over the entire intersection. `recursiveSubject`
uses the upper bound of `q.X`; `dependentField` opens that recursive type at `p`
and derives `p.a : p.A`. `recoveredView` reconstructs `p : { a : p.A }` with
`rcdIntro`. None of these source derivations chooses the witness for `p.A`.

At a known carrier tuple, the needed target condition is concrete: the child
carrier in slot `a` must lie below that tuple's own member `A`, and the field's
presence marker must be true. The issue is representing this relation when the
recursive type occurs as a first-class abstract member bound.

## Checked limit of the current labelled-union representation

`precise_mix` proves a structural property of the existing carrier layout. Given
two precise rows, choose independently for each component whether its complete
positive/negative pair comes from the first or second row. The resulting precise
row is a native subtype of the union of the original two rows. Consequently, any
single upper candidate accepting both original rows also accepts every such mix.
This does not depend on the upper candidate's syntax.

For the relation `child ≤ A`, both assignments `(A, child) = (Bottom, Bottom)` and
`(Top, Top)` satisfy the relation. Mixing the member from the first with the child
from the second gives `(Bottom, Top)`, which does not. The checked
`no_uniform_bound` theorem rules out characterizing this relation on all those
precise component tuples solely as `precise(tuple) ≤ M`, for any fixed semantic
candidate `M`. Payload and presence slots are unchanged in the concrete example.

This is a limit of the unchanged independent-component carrier representation
and its unary inclusion test. It is not an impossibility theorem for FCCT, for
correlated carrier layouts, or for encodings carrying additional membership
proofs or admissibility invariants.

## Checked predicate and dictionary prototype

The existing constraint syntax can encode truth of a bound:

```
Assert(Q) = neg (constrained Q Bottom)
```

`assertion_iff` proves semantically that `Top ≤ Assert(Q)` holds exactly when `Q`
holds, at every observation index. No new target rule is introduced.

The dictionary prototype universally binds payload, member `A`, presence, and
child witnesses. Its body is

```
[precise(tuple) ≤ X]
  (Assert(Top ≤ presence) & Assert(child ≤ A))
```

`dictionary_extract` uses only existing universal elimination, weakening, and
constraint elimination to derive `Top ≤ SAT(tuple)` from an encoded upper-bound
dictionary and the subject's membership. `dictionary_relation` checks that this
predicate entails the intended semantic relation for arbitrary `A`. It does not
construct a native `child ≤ A` subtyping derivation or rewrite the compiler.

The global dictionary is not yet a complete representation solution. If its
membership premise remains only `precise(tuple) ≤ X`, and one `X` admits both
diagonal tuples above, mixing also admits the crossed tuple. A dictionary that
soundly returns the relation for every admitted tuple would then be inconsistent.
This matters for exact source aliases of the recursive type, which must retain
independent abstract-member choices across values.

A derived assertion slot could correlate the components, but placing recursive
constraints in ghost carrier equations is outside the proved pure solver and
may reintroduce the constrained recursion obstruction. No such rule was added.
Correlated carrier products or explicit runtime coercion/membership evidence are
separate next directions; the local dictionary extraction theorem does not
establish their completeness.
