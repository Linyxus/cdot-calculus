# DOT to CTML: current checkpoint

Read this first when continuing. The full derivation-to-derivation translation is still open.
The detailed inventory and older experiments are in [fcct-translation.md](fcct-translation.md).

## Working requirements

- Target native CTML records, unions/intersections, arbitrary constraints, Z and RECORD-guarded
  recursion. Arrow-only experimental guards do not replace the target requirement.
- Use bounded parallel subagents with disjoint file ownership; integrate centrally.
- Use Lean 4.34.0 and the existing Mathlib cache. Commit green milestones as Codex, submodule first.
- No `sorry` or custom axioms in checked milestones.

## Latest checked result

Native `Recursive.HasType` now supports simultaneous record equations in addition to the existing
scalar record guards and arrow groups. `RecursiveRecordSystemExamples` constructs and projects a
finite value under `A = {next : B}, B = {back : Unit ∪ A}`; no arrow occurs in either body.
Weakening, substitution, constraint transport, progress and indexed safety cover the new rule.

The root `CTML.Mixed` model fixes a policy `ghost : FieldName → Bool`:

- Ordinary record fields are recursion guards, including over arbitrary constraint syntax.
- Ghost fields reflect component subtyping, but do not themselves guard recursion.
- `Mixed.HasType.safe` covers all native term forms, constraints, universals, Z, scalar guarded
  definitions, simultaneous ordinary-record groups and existing recursive function groups.
- `MixedSharedWitness` derives both contradictory bounds of the original source regression from
  EXACTLY its two original context guards, using the same member witness.
- `MixedExamples` checks closed scalar and mutual record-recursive programs reducing to Unit;
  the scalar program uses a constraint-abstracted ghost-inversion cast.
- `MixedFieldNames` proves the default runtime allocation disjoint from all ghost carrier slots.
  The runtime names are nonempty strings of `f`; the carrier names contain only `m`.

The actual partial carrier compiler now produces `Mixed` derivations. Its layout, source inputs,
computed types and runtime terms are unchanged. `compileSubtyping` handles shared bounds,
intersections, selections and singleton transport; `compileVariable` types its exact CPS output.
Generated packing/opening scopes and whole-package coercions use the same mixed judgment.
Both automatic type-only object passes also produce mixed proofs for their existing output and
alias interfaces. No new target evidence is required from compiler callers.

The older `Transparent` model remains checked prior work. Its arrow-only rule is not a limitation
on DOT or on native CTML recursion. The mixed relation remains in the root bridge; it has not
replaced the native submodule judgment.

`TermCPSObjectTyping` generates a record-guarded self equation from field types and proves the exact
runtime constructor step in the mixed target from field/package induction hypotheses. It derives
ordinary labels from the actual compiled fields under `programEnv`. Mixed term weakening also
allows packing arbitrary typed payloads without changing the runtime syntax.
`NativeFieldSharing.packTyping` takes
only a payload typing and builds a package sharing its member witness across `head` and recursive
`next`, generating recursive witnesses and bounds. Neither is a full source-object compiler yet.

## Next proof work

1. Connect native source-field compilation to one shared carrier/payload invariant through
   recursive self, aliases and dependent calls. Reopening independent packages loses identity.
2. Establish that generated recursive equations satisfy the mixed guard. Pure ghost cycles are
   still unguarded; the simultaneous mixed rule currently accepts only outer ordinary records.
3. Unify the type-only constructor interfaces and carrier interfaces, finish all `Core.Typing`
   rules, then prove general source/target operational correspondence.

No general translation or impossibility theorem is claimed. Operational target safety is proved;
syntactic preservation for scoped recursion remains a separate unfinished theorem.

## Verification

From `lean/`, using cached dependencies:

```sh
lake build CDot CDotFCCT FCCT CTMLCore -q --log-level=error
lake env lean ../notes/fcct/Audit.lean
lake env lean ../notes/fcct/TranslationAudit.lean
```
