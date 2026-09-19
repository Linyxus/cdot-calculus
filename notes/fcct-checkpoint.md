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
  finite pure carrier systems, including their mutual coupling with runtime rows.
- `MixedSharedWitness` derives both contradictory bounds of the original source regression from
  EXACTLY its two original context guards, using the same member witness.
- `MixedExamples` checks closed scalar and mutual record-recursive programs reducing to Unit;
  the scalar program uses a constraint-abstracted ghost-inversion cast.
- `MixedFieldNames` proves the default runtime allocation disjoint from all ghost carrier slots.
  The runtime names are nonempty strings of `f`; the carrier names contain only `m`.

The actual partial carrier compiler produces `Mixed` derivations. Its generated slots distinguish
payloads, type members, field presence and child carriers. `compileSubtyping` handles shared bounds,
field covariance, intersections, selections and singleton transport, including beneath field
types; `compileVariable` types its exact CPS output. A field view includes a presence constraint
in addition to its child upper bound, and an absent field cannot acquire a Top field view.
Generated packing/opening scopes and whole-package coercions use the same mixed judgment.
Both automatic type-only object passes also produce mixed proofs for their existing output and
alias interfaces. No new target evidence is required from compiler callers.

`CarrierPathGraph` now generates a finite pure equation system for demanded paths, closed under
prefixes. The compiler uses its solved child equations for actual `Core.newElim` and `rcdIntro`
derivations. `PathPresence` retains each edge's source-derived presence evidence through aliases.
`ContextCode` still has one guard per source binding; `Allocation.equations` is a separate prefix
whose satisfiability and non-collapse are proved. Nested `p.a.b.A` selection and alias-based field
introduction compile automatically. Runtime variable packaging remains exact; a general runtime
projection pass is still missing.

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

`CarrierRuntimeEquations` now solves finite runtime and pure carrier blocks together. The
runtime bodies may be intersections or other mixed guarded syntax; arbitrary constraints
beneath ordinary records are allowed. The carrier solver's parameter locality establishes
contractiveness of the outer runtime solution. Both blocks satisfy exact equations in one
environment, and `HasType.recursiveCarrierRuntime` closes their scope with safety and all
existing weakening/assumption-transport theorems.

`CarrierRuntimeSelf` instantiates the previously open whole-child self graph:
`P = precise(D, child=P, members)`, `D = Unit→R`, `R = {a: Anchor(P)}`. Its exact runtime
object, exported existential package and arbitrary-parent field call are typed solely from
the generated equations. A closed client executes to Unit. The remaining source allocation
work is described in [the self-graph note](fcct-carrier-runtime-self.md).
`CarrierRuntimeSelfSource.compile` now recognizes the single self-alias source constructor,
checks its requested source result, computes its standard slots and coupled system, and returns
a certificate for the exact `TermCPS.compile` output. A real `Core.newIntro` example is checked.
Its output interface is the solved self schema; it is not yet a general recursive `TypeCode`.
See [the source-entry note](fcct-self-source-entry.md).

`CarrierFieldPresence` proves generation and elimination of conditional runtime bounds.
Present fields require their actual payload shape; absent fields discharge the conditional
bound under `Top ≤ Bottom`. A finite graph interface must carry these invariants through
successive child openings. No unconditional runtime shape is inferred from child bounds.

`CarrierRuntimeInterface` provides one shared existential telescope for a finite demanded graph.
Its generated guards retain child equations and conditional runtime shapes. Packing/opening is
typed, and `twoStep` recovers successive field shapes and final witnesses from the actual exported
guard list plus explicit source presence proofs. Producers must still generate those invariants;
this generic interface is not a completed source runtime compiler.

`RecursiveCarrierBoundObstruction` checks a separate first-class issue. The source can derive
`p.a : p.A` when `p : q.X` and `q.X` is bounded above by
`μself.({A:Bottom..Top} & {a:self.A})`. A uniform scalar bound on the current independent-component
union carrier cannot characterize the needed relation `child ≤ A`: any bound admitting the two
diagonal component assignments also admits their invalid mixture. This is proved for arbitrary
semantic upper candidates, not just one attempted syntax. It limits this representation, not
FCCT in general. Constraint assertions and local universal-dictionary extraction are checked, but
the unchanged membership test cannot support a complete such dictionary. Correlated carriers and
explicit runtime coercion evidence are being investigated. See
[the recursive-bound obligation](fcct-recursive-bound-obligation.md).

## Next proof work

1. Resolve first-class recursive bounds without losing relationships between an unknown object's
   own components. A finite graph for named paths does not by itself solve this issue.
2. Derive the anchored runtime field invariant from general source field views, including opaque
   selections such as `{a:q.X}`, and preserve it across aliases and dependent calls.
3. Generate the finite coupled carrier/runtime graphs from arbitrary source definitions and
   path demands. The solver and self-field graph are checked; general source allocation and
   interface alignment remain. Field presence must be represented separately from child
   upper bounds so an abstract field view also justifies runtime projection.
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
