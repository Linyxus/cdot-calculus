# Finite code-completeness certificates

`lean/CDotFCCT/CTML/CodeCompleteness.lean` packages the pure-equation completeness
theorem as finite syntax, ready for later integration into mixed subtyping.

`CodeCompleteness.Schema ghost depth size` contains a guarded pure carrier system
and `size` arbitrary ambient `WFTy depth` names. `instantiate names expression`
maps references to those names and leaves outer types in the same ambient scope.
Names need not be consecutive variables or freshly bound types.

The schema computes two equation guards per name, completeness guards for all
occurring leaves, and the conclusion `Top <= name | ~name`. Its requirements are
a finite list of native `WFConstraint`s. `Schema.sound` proves that any environment
validating that list validates the conclusion. Neither the schema nor the theorem
accepts an arbitrary semantic entailment as evidence.

`CarrierEquationSyntax` now imports the base transparent carrier layout and mixed
row model directly, rather than importing `MixedCarrierLayout`. The underlying
layout constants are unchanged. This removes its dependency on `MixedInversion`,
allowing that judgment to consume the certificate module in a later step.

The certificate is theorem infrastructure, not a new subtyping rule yet. A future
rule must supply derivations of the computed requirements, and its soundness
proof can then use `Schema.sound`. Binding transport lives separately in
`CodeCompletenessBinding.lean`. No runtime payload is required to be complemented.

The binding module maps ambient names and leaves together, preserving the finite
reference indices and record guards. `Schema.requirements_liftAt` and
`Schema.requirements_substAtDepth` identify every transformed requirement with
the image of an original one; the corresponding `conclusion` lemmas do the same
for the result. This is ready for the future mixed-subtyping weakening and
substitution cases. Those calculus cases have not been introduced in this commit.
