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
- Ghost fields reflect component subtyping. Pure carrier equations may recurse beneath them
  by decreasing finite term structure; they do not guard arbitrary recursive constraints.
- `Mixed.HasType.safe` covers all native term forms, constraints, universals, Z, scalar guarded
  definitions, simultaneous ordinary-record groups, existing recursive function groups and
  finite pure carrier systems.
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
`MixedFieldSharing.packTyping` takes an arbitrary mixed payload typing and builds a package sharing
its member witness across `head` and recursive `next`, generating witnesses and bounds. Mixed type
weakening and native-evidence assumption transport cover every recursive scope form. Mixed
subtyping also supports type substitution. `MixedFieldSharingExamples` checks an actual source
object with `head = existing variable; next = self`, its exact compiled package, and a closed
client that follows `next`, reads both heads at one hidden member type and returns Unit.

`CarrierFieldInvariant` anchors a field's existential package at a fixed outer witness vector.
Opening proves equality of fresh and fixed components; the package can return the original
payload type directly. `CarrierAliasCompilation.compile` uses the variable compiler to generate
these witnesses for a source object with one field aliasing an existing variable. Its proof types
the exact CPS output with no caller-supplied target evidence. `CarrierAliasExamples` checks an
actual source derivation and a closed target client returning the original child value.
This pass exposes the native anchored payload; it does not yet encode the enclosing source type.
Its `compileProjected` additionally checks `let x = new {a = child} in x.a` against the child's
source binding type and returns that original variable's standard carrier package. Source/result
agreement is checked by the compiler; the actual core-DOT regression generates its target proof.
See [the field invariant](fcct-field-invariant.md) for the representation and remaining obligations.

`SelfFieldAnchor` solves `row = {a : Anchor(W[row], R)}` with an ordinary RECORD as the outer
constructor, exports the row and both equations, and types and executes a self-field call. Its object
and computation are definitionally the exact runtime compiler output. No recursive ghost equation
or caller-supplied field bound is needed for this runtime cycle.

`CarrierFieldViews` proves two-way flattened transport for visible member shapes and whole-child
slot transport for arbitrary opaque types. The [field-view note](fcct-field-views.md) gives the
checked source `{a:q.X}` test and the [equation audit](fcct-carrier-equations.md) identifies the
coupled ghost-carrier/runtime-row system a general whole-child encoding must solve.

`MixedGhostRowRecursion` solves the representative pure equation
`P = L ∪ {minus : ¬P} ∪ {plus : P}` by structural recursion on finite record terms.
The solution is downward closed and local at each observation index, satisfies the
actual mixed type interpretation, and composes with separately guarded runtime feedback.
`CarrierEquationSyntax` defines finite pure systems and compiles their rows, member views
and whole-child cycles to the existing carrier syntax. Both polarities are allowed under
ghost records; independent outer leaves may contain the full target syntax.
`CarrierEquationModel` now solves every finite system in that grammar, with downward closure
and per-index parameter locality. `CarrierEquationInterpretation` validates its compiled
equations and outer assumptions. `HasType.recursiveCarrierSystem` closes the scope; safety,
term/type weakening and assumption transport cover the new rule.
`CarrierEquationAliases.normalizeChecked` computes guarded systems from raw equations with
direct aliases, including chains and pure alias cycles. Its solution-transfer theorem recovers
every original equation; unguarded negative cycles are rejected.
`CarrierAliasScopes` derives both original bounds using native subtyping in the normalized
scope. `CarrierEquationExamples` packages whole-child and recursive member equations with
usable fold/unfold coercions, proves their closed safety and scope consistency, and checks
opaque field-view transport inside the solved cyclic whole-child scope.
See [the solver note](fcct-ghost-row-recursion.md).

## Next proof work

1. Derive the anchored runtime field invariant from general source field views, including opaque
   selections such as `{a:q.X}`, and preserve it across aliases and dependent calls.
2. Solve the generated whole-child carrier equations together with runtime payload equations.
   Both finite pure carrier systems and runtime record systems now have sound scoped rules.
   Their mutual coupling must be integrated, using the carrier solver's parameter locality.
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
