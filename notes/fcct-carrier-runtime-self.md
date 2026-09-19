# A solved whole-child self-field graph

`CarrierRuntimeSelf.lean` instantiates the coupled solver with the graph that
previously prevented the whole-child carrier representation from being used for
`{ a = self }`:

```
P = precise(payload = D, child = P, fixed member witnesses)
D = Unit → R
R = { a : interface(payload, P).package(answer) }
```

The combined block contains the carrier name `P` first and the ordinary runtime
row name `R` second. `D` is the arrow expression `Unit → R`, rather than a third
recursive name. The child slot occurs in both variance positions of the precise
carrier. The pure structural solver handles this negative carrier recursion;
the ordinary record at the outermost constructor of `R` guards the feedback
through the field package's universals and constraints. No arrow guard on the
runtime row is required.

The checked constructor uses the exact existing `TermCPS` output for the bound
self-field object. When it packs the self field, its chosen witness vector stores
`P` in the child slot and `D` in the payload slot. The generated carrier fold
equation proves `precise(witnesses) ≤ P`. The caller supplies no target bound or
recursive equation. The outer continuation package exports both solved names
and all four fold/unfold constraints.

`fieldCallTyping` handles any parent term typed at `D` in this generated scope.
Unfolding `R` gives the field package anchored to `P`; unfolding `P` identifies its
fresh package witnesses with the fixed witness vector, so the continuation
receives `D` again. `wholeChildView` records the exact whole-child equation when
the child slot belongs to the support.

The closed regression uses distinct payload and child labels, both present in
the support. It typechecks, executes to `Unit`, and satisfies the common mixed
safety theorem. The execution is unchanged from the earlier scalar-row example.

This removes the recursive carrier/runtime feedback obstruction for the actual
self-field graph. It is still a constructor theorem with fixed finite member
witnesses, not the complete source typing-derivation compiler. `compiledSelfTyping`
relates the literal runtime output to this canonical graph type; it does not
translate arbitrary source annotations. Generating witness
supports and member equations from arbitrary source derivations, handling general
paths and opaque member selections uniformly, and connecting all source rules
remain separate compiler work. Pure recursion inside carrier constraints remains
outside the structural equation grammar.
