# Fixed witnesses for runtime fields

For a finite witness vector `W`, write `P(W)` for its precise carrier and `D(W)`
for its runtime payload component. The field computation uses the interface

```
Anchor(W, R) = ∃fresh W'. P(W') <: P(W). D(W')
```

where the existential is continuation encoded at answer `R`. The fixed `W`
belongs to the surrounding object scope. Reopening the field introduces names,
but its paired ghost slots prove each new component equivalent to the same
fixed component. Different views of a path therefore cannot choose independent
member witnesses.

`CarrierFieldInvariant.anchoredPackageSubtype` proves, for arbitrary finite
support and constraints, that this package can feed an ordinary continuation
of type `D(W) → R`. `fieldCallTyping` uses that entailment for an arbitrary parent
term: force the object thunk, project its ordinary runtime field, and invoke
the package. `aliasObjectTyping` constructs the package from a scoped child
variable at `D(W)`, choosing the actual `W` and proving the carrier guard by
reflexivity. `aliasObject_runtime` identifies this object with the literal
`TermCPS.value` output. These results do not assume a desired field-result bound.

A field view `{a:T}` additionally needs `P(W_a) <: ⟦T⟧`, where `W_a` is the same
fixed child vector in every view of `a`. One possible suspended interface carries
both `P(W') <: P(W_a)` and `P(W') <: ⟦T⟧`; the former establishes identity and
the latter supplies the particular view's bounds. The compiler must derive that
second guard from the source derivation, and arrange its scope at field use.
The checked anchor result alone does not provide a general `newElim` or
`rcdIntro` compiler, or fuse two differently constrained field computations.

## Record recursion versus recursive ghost carriers

A runtime self alias has a directly record-guarded equation:

```
row = { a : Anchor(W[row], R) }
D(W[row]) = $Unit → row
```

The remaining member entries of `W` are finite fixed witnesses. Occurrences of
`row` inside the package lie below the ordinary runtime field `a`; reflective
slots inside that package do not remove this guard. The Z-bound self value has
type `$Unit → row`, so the field can package it using these same witnesses.
There is no need to declare a recursive ghost carrier for this runtime cycle.

`SelfFieldAnchor.objectTyping` checks this construction with arbitrary finite
member witnesses. `packTyping` hides its solved row while exporting both defining
equations; `fieldCallTyping` proves that any value at this row's object type
returns the same fixed payload type through the field. Both the value and the
packaged computation are literally the corresponding `TermCPS` outputs.
`programSteps` executes the self-field projection to `$Unit`, and `programSafe`
uses the checked mixed safety theorem. None of these producer theorems requires
a caller-supplied recursive bound or field-result inequality.

The separate parent-view problem arises if the compiler puts the whole child
carrier inside another reflective slot and then equates a self child's carrier
with its parent's carrier. An equation such as `P = {ghostChild:P}` has only a
ghost guard. `wholeChildCycleNotGuarded` checks its rejection by the current sound
formation rule. This is a limitation of that parent-view representation, not a
blocker to runtime self construction.

## Remaining finite-support obligation

A flat vector of relative-path/member entries can avoid storing a recursively
defined whole child carrier. A finite source derivation mentions only finitely
many paths, but this observation alone is insufficient: the generated support
must also transport each demanded suffix through aliases and recursive self
unfoldings. Naively giving every child a complete copy of the parent's future
paths demands unbounded expansion for a self-field cycle. Quotienting those
paths to a finite alias graph avoids expansion of witness variables, but using
that graph to define whole-carrier ghost equations recreates the guard problem.

The next compiler obligation is a finite, derivation-directed allocation and
transport theorem for these path components, together with generated runtime
payload equations. Source membership in a field view must produce the child's
fixed bounds through this allocation. Such evidence must come from source
context assumptions, constructor equations, or translated source rules; it
cannot be accepted as an additional target premise. Arbitrary opaque field types
such as `{a:q.X}` are a useful hard test because their child constraint does not
reduce to a syntactically known list of member bounds.
