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
  definitions and simultaneous groups whose outer field labels are all ordinary.
- `MixedSharedWitness` derives both contradictory bounds of the original source regression from
  EXACTLY its two original context guards, using the same member witness.
- `MixedExamples` checks closed scalar and mutual record-recursive programs reducing to Unit;
  the scalar program uses a constraint-abstracted ghost-inversion cast.
- `MixedFieldNames` proves the default runtime allocation disjoint from all ghost carrier slots.
  The runtime names are nonempty strings of `f`; the carrier names contain only `m`.

The older `Transparent` model and partial carrier compiler remain checked prior work. Do not read
their arrow-only rule as a limitation on DOT or on native CTML recursion. The new mixed relation
is still isolated in the root bridge; it has not replaced the native submodule judgment.

`TermCPSObjectTyping` generates a record-guarded self equation from field types and proves the exact
runtime constructor step from field induction hypotheses. `NativeFieldSharing.packTyping` takes
only a payload typing and builds a package sharing its member witness across `head` and recursive
`next`, generating recursive witnesses and bounds. Neither is a full source-object compiler yet.

## Next proof work

1. Transport the existing carrier derivations/packages to the mixed relation. Generated carrier
   labels are proved ghost labels and the default runtime allocation is proved disjoint; retain
   these facts when generating the common type and term environments.
2. Connect native source-field compilation to one shared carrier/payload invariant through
   recursive self, aliases and dependent calls. Reopening independent packages loses identity.
3. Establish that generated recursive equations satisfy the mixed guard. Pure ghost cycles are
   still unguarded; the simultaneous mixed rule currently accepts only outer ordinary records.
4. Unify the type-only constructor interfaces and carrier interfaces, finish all `Core.Typing`
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
