# Derived Boolean slots preserve cross-component bounds

`CarrierRelationSlots.lean` gives actual native and mixed subtyping derivations for
a correlated carrier, using the existing rules. The key equivalence is

```
Top <= C | ~C  implies  (C <= A iff Top <= ~C | A).
```

The forward direction is lattice monotonicity. The reverse uses distributivity
and non-contradiction derived from the supplied completeness guard. It does not
assume unrestricted complementation of runtime types.

The carrier retains the existing paired labelled-union layout, with three slots:
member `A`, child `C`, and a computed relation slot `~C | A`. A fixed view requires
the relation slot to be above Top. Existing ghost-row inversion recovers that
bound; `native_elim` turns it into `C <= A`. `characterizes` proves both directions
at the level of actual `InvertingSubtype` derivations, under the child-code
completeness premise. Both diagonal assignments are accepted and the crossed
`A=Bottom, C=Top` assignment is rejected.

The original mixing theorem does not apply to arbitrary choices of these three
slots: the relation slot is computed from the other two. It cannot be independently
selected from another tuple while retaining the same carrier definition.

Crucially, the derived slot uses only negation and union. `equationBody_guarded`
and `equationBody_compile` place exactly this representation in the existing pure
record-equation grammar, even when the member and child expressions contain
recursive references. No recursive constraint assertion or new inference rule is
introduced here.

The remaining task is generating and certifying completeness of source type
codes, and generating the necessary correlated slots from arbitrary source type
templates. The checked closure theorems in `ComplementedGhostCodes` and
`ComplementedCarrierAssumptions` establish semantic completeness of pure recursive
codes from their equations and occurring leaves. They have not yet been turned
into general syntactic code-completeness certificates accepted by the calculus.
Runtime payload identity is separately anchored by `SplitCodeRuntimeAnchor`;
the runtime type has no completeness requirement.
