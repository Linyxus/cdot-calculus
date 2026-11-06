# Complemented ghost witnesses repair the optional-product bound

`lean/CDotFCCT/CTML/ComplementedProduct.lean` proves a positive result for the
optional paired product investigated in `fcct-optional-product-obstruction.md`.
Its additional restriction is an existing FCCT constraint:

```
Complete(A) = Top <= A | ~A
```

For both-polarity subtyping, the guard requires every term to have a positive or
negative A observation and forbids having both. It is an admissibility restriction
on ghost type-code witnesses; it is not a new complement rule for runtime types.

The uniform scalar bound is:

```
M = Exists C. Exists B.
      Require(Complete(B),
        Require(Complete(C), Require(C <= B, P(B,C))))
```

`Exists X.T = ~Forall X.~T` and `Require(Q,T) = ~(Q => ~T)` use the existing target
syntax. `interpret_boundTy` proves that the concrete closed `WFTy` has exactly this
interpretation, with prefix closure of universally quantified candidates intact.

The main theorem `characterizes` is:

```
Downward A -> Downward C -> Complete(A) -> Complete(C) ->
  (P(A,C) <= M iff C <= A)
```

It holds at every step index, with each assumption restricted to the current
prefix where appropriate. `guarded_type_characterizes` instantiates the theorem
for actual interpreted types and their concrete completeness guards.

The difficult reflection direction uses a record that puts the *same arbitrary
term* in the member-negative slot and the child-positive slot. If the product is
accepted by M, some existential B and C must accept those two observations. Their
subtype relation then makes the term positive in B as well as negative in B,
contradicting B's completeness guard. Totality of the original witnesses turns
this exclusion into both directions of the target inclusion relation.

This removes the previous gap counterexample for this restricted representation.
It is a semantic feasibility theorem, not yet a compiler or a native subtyping
derivation for arbitrary generated codes. A compiler still needs to generate and
preserve the completeness guards for its ghost codes, keep runtime payloads outside
the restriction, and connect the representation to source recursive type views.
No typing rule, recursive solver, or model was changed in this prototype.
