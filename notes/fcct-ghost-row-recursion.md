# Pure ghost recursion can use finite term structure

`CTML/MixedGhostRowRecursion.lean` gives a checked semantic solution of

```
P = L ∪ {ghostMinus : ¬P} ∪ {ghostPlus : P}
```

for an arbitrary independent candidate `L`. This representative has both positive
and negative recursive occurrences, as precise carrier rows do. It uses the
existing `TransparentRecord.record` semantics, including negative observations;
it does not replace that semantics or add a typing rule.

The solver computes both observation polarities by mutual structural recursion
on native `Term` and `TermFields`. A ghost field inspects its stored term, which
is a proper subterm, at the same step index. The negative slot swaps the two
polarities. Missing fields contribute no positive observation and a vacuous
negative observation. `solution_fixedPoint` proves the complete equation for
both polarities.

`solution_downward` preserves downward closure of `L`. Consequently the variable
interpretation's `prefixClosure` is equal to the solved candidate.
`interpretation_equation` proves the equation for the actual `Mixed.interpret`
of a well-scoped type body. Its two labels must be marked ghost; the independent
leaf is weakened underneath the new recursive name, so that name cannot occur
inside the leaf's constraints or other syntax.

The solver is local in its parameter: equality of `L` at index `n` gives equality
of the solution at that same index (`solution_congr`), and therefore it preserves
prefix agreement. This supports ordinary record feedback without treating a
ghost field as a step-index guard. `solution_contractive` proves that composing
the solver with a genuinely step-contractive leaf operator remains contractive.
`coupled_equation` then solves

```
P = L(P) ∪ {ghostMinus : ¬P} ∪ {ghostPlus : P}
```

using the existing indexed fixed point outside the structural ghost solver.
`coupled_downward` supplies downward closure when every `L(P)` is downward.
Thus the outer step index and the inner finite record structure can cooperate.

`CarrierEquationSyntax.lean` also defines the finite pure equation grammar: outer
well-scoped types, recursive references, negation, unions/intersections and ghost
records. Formation requires every recursive reference to occur below a record.
Its compilation lemmas preserve the existing precise carriers and member views,
including whole-child cycles and recursive bounds with both polarities. A direct
alias is explicitly unguarded; alias elimination is a separate obligation.

The scalar result does not yet establish a simultaneous solver for this grammar
or a new scoped recursive declaration rule. Those extensions still need binding
and safety integration. In
particular, a recursive constraint can inspect inclusion on arbitrary terms at
the same index; its observations need not decrease term size. The structural
argument gives no permission to admit the constrained Curry cycle. Recursive
constraints remain outside the pure ghost fragment; feedback through ordinary
records must separately satisfy the existing contractiveness condition.
