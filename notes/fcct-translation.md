# Core DOT to CTML Core: implementation status

The translation target is **CTML Core with Z and scoped recursive type declarations**.
Records, projections, intersections, and unions use CTML's native syntax.
Record-guarded recursion is a requirement of this target, not an optional relaxation.
The current checkpoint is summarized in [fcct-checkpoint.md](fcct-checkpoint.md).
Existential packages and computations use continuations; record payloads remain native.
The earlier minimal-FCCT bridge
modules remain as baseline experiments; the compiler produces CTML terms.

There is a proof-producing translation of an **opened fragment**, multi-witness
package and dependent-function rules, and a runtime CPS pass that is total on the
full core-DOT input judgment. The runtime pass handles self references and nested
objects; its coverage and native field properties are proved.
The type-only object constructor also has an executable, partial typing pass:
it generates recursive witnesses from source declarations and types the exact
runtime compiler output, including declarations with unguarded alias cycles.
**There is still no typing-preserving translation of arbitrary core DOT derivations.**
The missing translation must construct a target term and a
`CTML.Mixed.HasType carrierPolicy` derivation from every `Core.Typing` input.
The native fragment also retains its `CTMLCore.Recursive.HasType` proofs.
`TermCPS.compile` is the current runtime pass; a derivation-directed elaborator
may also need to insert explicit coercions. There are no placeholder axioms or
`sorry` proofs standing in for the general theorem.
CTML Core's progress, preservation, and determinism proofs now cover Z. The scoped
recursive extension has its own explicit `Recursive.HasType` judgment. Its progress,
term and type weakening and substitution, and constraint transport proofs check.
An indexed value interpretation now validates every native subtyping rule and both
directions of guarded recursive equations, retaining function behavior and field contents.
The typing fundamental lemma now covers both Core and the recursive extension.
`Recursive.HasType.safe` proves that every finitely reachable term is a value or can step.
This establishes operational safety; syntactic preservation for the extension remains open.
The native extension now includes simultaneous record equations with no function guard.
The separate `Mixed` model proves safety when ordinary record fields guard recursion
and designated ghost fields support component inversion. It preserves arbitrary
constraints and validates the original shared-bound regression. The earlier
`Transparent` model's arrow-only guard is not a requirement of the intended target.

The chosen source scope is core DOT: functions, recursive objects, records,
intersections, abstract type members and their bounds. Runtime tag tests and the
cDOT-specific inversion rules are outside this first translation.

## Checked components

The bridge is a separate Lake library in the cDOT project. Import `CDotFCCT.CTML`
for the native CTML target; the earlier minimal-FCCT experiments have a separate
`CDotFCCT.Baseline` entry point. `CDotFCCT` remains a compatibility umbrella for both.
FCCT and CTML Core are
local dependencies from `external/ctml/fcct/lean` and
`external/ctml/lean/CTMLCore`, across the Git submodule boundary. The root project's
Mathlib 4.34 pins agree with CTML Core and CTML Full's standalone manifests. The
builds reuse the root cache; in this checkout the standalone projects' shared
dependency directory links to the same cached packages.

| Module | Checked interface |
| --- | --- |
| [Existentials](../lean/CDotFCCT/Existentials.lean) | `packTyping`, `packCBVTyping`, `consumerTyping`, `unpackTyping`; any finite list of FCCT constraints, including bounds |
| [PackageSubtyping](../lean/CDotFCCT/PackageSubtyping.lean) | `existsCPSSubtype` for guard entailment/payload widening; `boundedSubtype` for contravariant lower and covariant upper bounds |
| [Intersections](../lean/CDotFCCT/Intersections.lean) | Common-subtype packages, introduction from one witness, and both projections by FCCT subtyping |
| [RecursiveWitnesses](../lean/CDotFCCT/RecursiveWitnesses.lean) | `recursiveEquationSatisfies` constructs a witness of `X = P(X) → Q(X)`; `packRecursive` packages a typed payload |
| [RecursiveMembers](../lean/CDotFCCT/RecursiveMembers.lean) | An actual closed `CDot.Typed` derivation with `A = self.A → self.A`, its selected-type equations, a target witness/package, and a typed abstract client reducing to `true` |
| [Examples](../lean/CDotFCCT/Examples.lean) | Bounded packaging/elimination, two function interfaces backed by one polymorphic intersection witness, and checked execution |
| [CTML package rules](../lean/CDotFCCT/CTML/Existentials.lean) | The same constrained CPS package discipline over CTML Core's native types and terms |
| [CTML records](../lean/CDotFCCT/CTML/Records.lean) | `projectionInverse` derives DOT's record-introduction rule using CTML intersection introduction and record distribution |
| [Recursive CTML records](../lean/CDotFCCT/CTML/RecursiveRecords.lean) | The same record-introduction rule through any nesting of scoped recursive declarations, in `Recursive.HasType` |
| [Open types](../lean/CDotFCCT/OpenTypes.lean) | Data-valued subtyping derivations, source erasure, target payload-subtyping translation, and member-package variance |
| [Open typing](../lean/CDotFCCT/OpenTyping.lean) | Data-valued path/application derivations, source erasure, target typing translation, and CPS consumer construction |
| [Static compilation](../lean/CDotFCCT/StaticCompilation.lean) | Executable partial syntax pass for pure clients of one static record package; unsupported constructs return `none` |
| [Record compilation](../lean/CDotFCCT/RecordCompilation.lean) | A closed DOT object with a type member and two related fields, exact compiler-output equality, generated consumer typing, closed target typing, and reduction |
| [Dependent functions](../lean/CDotFCCT/CTML/DependentFunctions.lean) | Constraint-polymorphic dependent abstraction and application, including CPS results |
| [Dependent compilation](../lean/CDotFCCT/DependentCompilation.lean) | A function returning `x.A → x.A`, instantiated using the caller's existing witness; checked source, compiler output, target typing, and reduction |
| [Recursive compilation](../lean/CDotFCCT/RecursiveCompilation.lean) | `A = self.A → self.A`, a native record, witness packing, and a client that applies a field to itself; checked source, compiler output, recursive target typing, and reduction |
| [Full core input](../lean/CDotFCCT/CoreDerivation.lean) | Data-valued versions of every chosen core typing, definition, and subtyping rule, including singletons and nested objects; erasure checks against cDOT's judgments |
| [Member uses](../lean/CDotFCCT/MemberUses.lean) | Total traversal of the full core derivation, collecting shared member keys, free selections in types, source bound proofs, and scoped singleton equalities |
| [Witness scopes](../lean/CDotFCCT/WitnessScopes.lean) | Every recorded reference has a well-scoped target variable; distinct keys have distinct variables; entering a fresh binder weakens outer witnesses without reallocating them |
| [Scope validity](../lean/CDotFCCT/MemberScopeSafety.lean) | Fresh binder identities and unique scope addresses throughout every full core derivation, with no extra freshness premise at the root |
| [Member analysis regressions](../lean/CDotFCCT/MemberUseExamples.lean) | Opaque bounds, nested fields, references without selection rules, independent cofinite binders, dependent results retaining outer witnesses, and hypothetical singleton equalities |
| [Alias constraints](../lean/CDotFCCT/AliasConstraints.lean) | Generates scoped witness equations from recorded source singleton proofs, proves coverage of supported field extensions, and constructs native guarded coercion derivations |
| [Alias constraint execution](../lean/CDotFCCT/AliasConstraintExamples.lean) | A real source member-replacement derivation generates a universal constrained coercion; a closed client discharges both guards and preserves the value inside a native record |
| [Runtime CPS](../lean/CDotFCCT/TermCPS.lean) | `compile` computes target syntax from any core typing derivation; `computation_total` proves coverage, including runtime self and nested objects |
| [Native field properties](../lean/CDotFCCT/TermCPSRecords.lean) | Every field is suspended; the returned record is a value; distinct source fields are retained with an injective label allocation |
| [Object execution](../lean/CDotFCCT/TermCPSExecution.lean) | Every compiled core object can be forced to a native record value in four target steps, with field names preserved and field bodies suspended |
| [Field-call execution](../lean/CDotFCCT/TermCPSLookup.lean) | For any core-typed object and existing source field, native lookup selects the compiled field body with its delayed self and caller continuation substituted |
| [Finite field names](../lean/CDotFCCT/FieldNames.lean) | A deterministic string allocation injective on finite source support, without assuming the whole signature is countable |
| [Interfaces](../lean/CDotFCCT/CTML/Interfaces.lean) | Any finite telescope of shared witnesses and cross-member constraints, with native packing and opening proofs |
| [Quantified interfaces](../lean/CDotFCCT/CTML/QuantifiedInterfaces.lean) | Parameter and result types share one instantiation of the full witness telescope |
| [Interface subtyping](../lean/CDotFCCT/CTML/InterfaceSubtyping.lean) | Guard entailment, payload subtyping, and addition or removal of witnesses construct actual package-subtyping proofs |
| [Interface intersections](../lean/CDotFCCT/CTML/InterfaceIntersections.lean) | Merges aligned views under shared binders and proves both package projections |
| [Recursive interfaces](../lean/CDotFCCT/CTML/RecursiveInterfaces.lean) | The same packing, opening and dependent-application rules with payloads and clients in `Recursive.HasType` |
| [Witness-sharing regression](../lean/CDotFCCT/SharedWitnessRegression.lean) | A checked source derivation showing why independently translating an abstract member's upper bounds loses sharing, plus target packing instances with no common witness |
| [Package-fusion obstruction](../lean/CDotFCCT/SharedWitnessFusion.lean) | At every answer type, native subtyping cannot merge the two independent package views into one shared witness, including under native record fields; a conversion returning the original package cannot do so either, even with scoped recursive types and Z |
| [CPS coercions](../lean/CDotFCCT/CTML/Coercions.lean) | Native-record conversions recover lower and upper member bounds as typed terms; reduction proofs show that they pass the original value to the continuation |
| [Shared-bound coercions](../lean/CDotFCCT/SharedWitnessCoercions.lean) | The same witness serves views reached through an opaque type; an inhabited precise row cannot satisfy the regression's contradictory closed bounds; native subtyping inversion remains underivable |
| [Coercion refinement](../lean/CDotFCCT/CTML/CoercionRefinement.lean) | An upper-bound conversion retains the input's existing type by native intersection introduction; a lower-bound conversion does so when its marker answer is the selected witness |
| [Constraint-abstracted selection](../lean/CDotFCCT/CTML/Selections.lean) | A lower bound constructs a universal CPS observation over one carrier; an existing precise witness and another upper view consume it, with checked execution |
| [Selection example](../lean/CDotFCCT/SelectionExamples.lean) | All selector guards are discharged in the empty context, and the program returns the original identity function |
| [Observation refinement](../lean/CDotFCCT/CTML/ObservationViews.lean) | Adding a selected-type observation preserves intersections, universals, and constrained CPS views at a fixed answer type, for both native and recursive typing; execution preserves the observed value |
| [Observation sequencing](../lean/CDotFCCT/CTML/ObservationBind.lean) | One CPS bind retains arbitrary intersections, universals, and constrained views ending at the same answer, including complete existential packages; flattening removes an extra CPS layer without choosing new witnesses, with native and recursive typing and exact execution proofs |
| [Whole-interface sequencing](../lean/CDotFCCT/CTML/InterfaceBind.lean) | `bindAnswerView` opens one full witness telescope over a constraint-polymorphic client; `repackerTyping` constructs repacking without a supplied instance, reusing its own witnesses and guards, and `repackReturns` preserves the payload |
| [Negative member witnesses](../lean/CDotFCCT/CTML/NegativeWitnesses.lean) | A witness with a checked native equivalence to an answer view admits a lower-bound conversion retaining its old negative view, without equating the answer and witness; any recursive package interface constructs such a witness |
| [Abstract negative selections](../lean/CDotFCCT/CTML/NegativeSelections.lean) | Constraint abstraction over a package consumer constructs a negative selected view before a witness is chosen; elimination recovers an existing package witness, including an opaque recursive name, and composes different bounds of the same carrier |
| [Package witness scopes](../lean/CDotFCCT/CTML/PackageWitnesses.lean) | Binds an opaque member and its consumer with both native representation equations; packing discharges those equations, opening reconstructs the evidence, and recursive packages supply instances |
| [Negative native fields](../lean/CDotFCCT/CTML/NegativeRecords.lean) | Strengthens a field to an existing opaque negative witness or an abstract negative selector, retains the complete old row and its opaque supertypes, and preserves the selected field computation |
| [Recursive negative witness](../lean/CDotFCCT/NegativeWitnessExamples.lean) | A closed target check for `A = CPS(A → A, Unit)` retains `∀B. CPS(B → B, Unit)` while constructing an abstract selector and recovering `A`; self-application, the original polymorphic client, and conversion through different bounds all typecheck and reduce to Unit |
| [Exported recursive witness](../lean/CDotFCCT/PackageWitnessExamples.lean) | Packages the recursive name and its consumer, opens them in an abstract client, constructs the negative representation from package guards, and checks a native-record program reducing to Unit |
| [Mutually recursive witnesses](../lean/CDotFCCT/CTML/MutualPackageWitnesses.lean) | Constructs one scope for any finite group of recursive package equations, with native fold/unfold proofs; the simultaneous closing rule is covered by weakening, substitution, constraint transport, progress, and operational safety |
| [Exporting recursive groups](../lean/CDotFCCT/CTML/RecursivePackages.lean) | Given a payload derivation inside a simultaneous recursive scope, constructs one closed existential package, instantiating all witnesses and discharging all defining equations automatically |
| [Mutual witness example](../lean/CDotFCCT/MutualWitnessExamples.lean) | An actual core-DOT derivation with self and cross references in two members; closed target programs construct those witness shapes with Z, use native fields and cross-member calls, and reduce to Unit, including after exporting and reopening the shared package. This is a representation check, not the general compiler |
| [Recursive alias solver](../lean/CDotFCCT/CTML/RecursiveAliases.lean) | Computes guarded witnesses for any finite system of arrows, bare aliases and intersections; proves both directions of every input equation by native subtyping and exports those original equations through one existential telescope |
| [Source alias elaboration](../lean/CDotFCCT/RecursiveAliasTranslation.lean) | Resolves actual source member labels and self references, including under nondependent arrow binders, and computes the equation system with a record of each successful source elaboration |
| [Type-only object compilation](../lean/CDotFCCT/TypeOnlyCompilation.lean) | Takes an actual `Core.Typing` derivation, checks that its definitions are supported type declarations, generates witnesses and guards, and constructs `Recursive.HasType` for the exact `TermCPS.compile` output; unsupported cases return `none` |
| [Compiled alias cycles](../lean/CDotFCCT/RecursiveAliasExamples.lean) | The constructor pass compiles a checked source object with `A = A & (A → A)`, `B = C`, and `C = B`; an abstract client opens the original equations and forces the compiled object to a native record, with typing, safety, and reduction proofs |
| [Checked constraint discharge](../lean/CDotFCCT/CTML/DischargeSearch.lean) | Reuses CTML's solver rules, retries alternatives after cyclic lookups, and accepts only proofs that introduce neither names nor assumptions; previously proved hints are removed by constraint transport |
| [Bounded object compilation](../lean/CDotFCCT/BoundedObjectCompilation.lean) | Compiles a source derivation for `let x = new … in x` at a requested recursive member interface, generating witnesses and proving every exported bound before returning a typing derivation for the exact runtime output |
| [Compiled bounded views](../lean/CDotFCCT/BoundedObjectExamples.lean) | Checks distinct bounds on the same member, recursive aliases, the complete generated consumer type, and a closed client that reduces to the native object record |
| [Experimental carrier compiler](../lean/CDotFCCT/CarrierTranslation.lean) | Consumes actual core subtyping derivations, generates complete scoped witness rows and context guards, and derives shared bounds through selections, intersections and singleton transport; unsupported rules fail explicitly |
| [Compiled carrier regressions](../lean/CDotFCCT/CarrierCompilationExamples.lean) | Automatically compiles the shared-witness counterexample, abstract bounds reached through an alias, and member variance to universally quantified constraint abstractions in the experimental target |
| [Carrier runtime variables](../lean/CDotFCCT/CarrierRuntime.lean) | Generates the payload context, witness layout, guards and typing derivation for the exact runtime CPS output of supported source variable typings, with witnesses in an opened environment |
| [Carrier payload execution](../lean/CDotFCCT/CarrierRuntimeExamples.lean) | Checks a source variable reached through an alias, and a closed existential package whose carrier exposes a native record field that is called and returns Unit |
| [Generated carrier packages](../lean/CDotFCCT/CTML/MixedCarrierPackages.lean) | Binds every member and payload witness, proves that the exported interface is independent of their concrete assignments, generates packing instances, and transports whole packages along proved carrier bounds |
| [Generated carrier scopes](../lean/CDotFCCT/CTML/MixedCarrierOpening.lean) | Computes the continuation's fresh types and guarded context and proves its equivalence to telescope elimination; the requested view and answer retain their outer references |
| [Carrier recursive scopes](../lean/CDotFCCT/CTML/MixedSystems.lean) | Solves the existing simultaneous recursive function equations in the mixed model alongside record guards; validates their equations and closing rule |
| [Carrier constructor bridge](../lean/CDotFCCT/CarrierConstructorCompilation.lean) | Derives mixed typing for the exact output and existing interfaces of both automatic type-only object passes; unifying those interfaces with carrier views remains unfinished |
| [Native object typing step](../lean/CDotFCCT/TermCPSObjectTyping.lean) | Generates a record-guarded self equation and types the exact CPS object output in both native and mixed judgments from field/package induction hypotheses; actual compiled fields establish ordinary labels |
| [Mixed structural packing](../lean/CDotFCCT/CTML/MixedInterfaceWeakening.lean) | Term weakening covers all recursive scope forms and allows packaging arbitrary mixed payload typings using the original runtime pack syntax |
| [Native recursive field sharing](../lean/CDotFCCT/CTML/NativeFieldSharing.lean) | Constructs a package sharing one member witness across `head` and recursive `next`; the payload typing generates both witnesses and recursive bounds |
| [Mixed record safety](../lean/CDotFCCT/CTML/MixedSafety.lean) | Proves operational safety with ordinary record guards, ghost-component inversion, arbitrary constraints, Z, and simultaneous ordinary-record or function equations |
| [Mixed shared bounds](../lean/CDotFCCT/CTML/MixedSharedWitness.lean) | Derives both bounds on the original shared witness from exactly the original two context guards, under a policy permitting direct ordinary-record recursion |
| [Mixed execution](../lean/CDotFCCT/CTML/MixedExamples.lean) | A ghost-inverting cast of a directly recursive record and a mutual-record program typecheck and reduce to Unit |
| [Recursive carrier execution](../lean/CDotFCCT/CarrierRecursiveExamples.lean) | A native record contains a Z-defined function with two mutually recursive types; one client opens its equations and calls through both arrows, while another returns the record through the generic carrier package |
| [Repeated observation example](../lean/CDotFCCT/ObservationExamples.lean) | Two refinements retain an earlier selector and two original views, with `Unit` as answer and `Top → Top` as witness; all guards are discharged and execution checks |
| [Native observation records](../lean/CDotFCCT/CTML/ObservationRecords.lean) | A complete native row of suspended observations can gain a selector view at one field while retaining the original row and any opaque supertype; the stronger row supports repeated refinements |
| [Repeated field example](../lean/CDotFCCT/ObservationRecordExamples.lean) | Two successive field refinements retain both selectors and their original observations; all guards are discharged and both field clients reduce to `Unit` |
| [Recursive inversion obstruction](../external/ctml/lean/CTMLCore/CTMLCore/Declarative/RecursiveInversionObstruction.lean) | A separate hypothetical extension with record-subtyping inversion types `Unit Unit` through a guarded recursive constraint cycle; the actual target rejects it |

## Opened records and the current compiler boundary

`OpenCore.Subtyping.translate` and `OpenCore.Typing.translate` recurse over explicit
source-rule derivation data. Their `source` theorems check those derivations against
the repository's `CDot.Subtyp` and `CDot.Typed`; the target proofs are constructed
using CTML Core's existing judgments. This avoids eliminating `CDot.Typed : Prop`
to compute syntax. There is not yet an elaborator for arbitrary `CDot.Typed` proofs.

The covered typing rules are variable lookup, field projection, record introduction,
path intersection, application and subsumption. Subtyping covers extrema, reflexivity,
transitivity, intersections, field covariance, member variance, nondependent arrows,
and selections from the explicitly opened bounds. This is a smaller fragment than
the requested full core DOT scope; in particular, dependent function introduction,
general object creation, recursive type opening and singleton transport are absent.

`Witnesses.get` is keyed by the whole stable source path and member label, so all
occurrences use the same target type. Member declarations erase to `Top` **in the
opened payload**, while their bounds remain in `boundsContext` and are abstracted
by `Typing.consumerAt`. Its result-type equality requires the answer to be outside
the hidden witness's scope. This is not a standalone translation of a sealed object type:
the whole record needs one enclosing existential package. Giving each declaration
its own package and intersecting those packages with record types would conflate
function-shaped packages with record-shaped payloads and lose witness sharing.

The caller of the opened-fragment source theorem supplies `SourceBounds`: actual
DOT typings for the listed member interfaces. The target consumer assumes their
translated constraints. General object translation must construct witnesses and
discharge those assumptions; the theorem does not establish that for arbitrary
source contexts or object definitions.

`RecordCompilation` closes this boundary for a concrete program. Its object has
`A = Top → Top`, a `value` field at that type, and `id : self.A → self.A`. The client
retypes `value` using the lower bound, combines record views using `rcdIntro` and
`andIntro`, applies `id`, and uses the upper bound. The consumer proof is generated
by `Typing.consumerAt`. The concrete record discharges both guards by reflexivity.
`compilation` proves that the executable pass produces exactly `targetProgram`,
and `targetProgramSteps` proves that it evaluates to the stored identity function,
at the translated result type `Top → Top`.
The object's constructor proof is specific to this example; general constructor
preservation for `StaticCompilation.program` is not yet claimed.

At a fixed answer type `R`, the package representation is:

```text
ExistsCPS(guards, V, R) = (∀A. guards(A) ⇒ V(A) → R) → R
```

`R` lies outside `A`'s scope. Packing proves every instantiated guard; the consumer
may assume them. Constraint and universal introduction apply to the consumer
lambda, respecting the CBV value restriction. `pack value = λk. k value` delays its
payload; `packCBV term` instead evaluates the payload before returning the package.
A compiler must choose the appropriate form to preserve source evaluation order.

The original minimal-FCCT `CDotFCCT.intersectionIntro` requires a single witness below both component types.
It does **not** derive a common witness from two arbitrary target typings. That is
an obligation of that encoding, not an assumption we can omit. The CTML-backed
opened-payload translation instead uses its primitive intersection introduction,
so it does not require this additional common-subtype witness.

## Generating witnesses for alias cycles

`CTML.RecursiveAliases` accepts finite equation systems whose outer structure is
arrows, references, and intersections. Arrow domains may contain arbitrary native
types, including recursive references inside fields, universals, and constraints.
For each member it follows the bare alias edges and collects all reachable arrow
domains. Their union is the domain of its generated recursive arrow, with `Bottom`
for an empty collection. Native arrow-domain distribution then proves both
directions of the original, unnormalized equation.

For example, `A = A & (((A → A) → R) → R)` obtains the same guarded witness as its
structural arrow component, while `B = C; C = B` can assign both names `Bottom → R`.
The solver proves these choices satisfy the equations. It does not add unguarded
recursive types to CTML or assume arbitrary recursive equations are consistent.
Reachability currently enumerates finite edge-closed vertex sets, so this is an
executable reference algorithm with exponential worst-case cost.

`RecursiveAliasTranslation.type` constructs these equations from actual source
types. It supports extrema, intersections, fields, selections of members of the
same self object, and arrows without dependence on their argument. Crossing an
arrow binder shifts self's index; a selected argument member is rejected rather
than confused with self. Fields and functions retain native payload types inside
negative continuation wrappers. This is a declaration elaborator, not yet the
general source type translation.

`TypeOnlyCompilation.compile` connects it to real source typing derivations for
objects containing only type definitions. It collects those definitions, invokes
the declaration elaborator, generates every recursive witness and both guards of
every alias, and derives typing for **the exact term from `TermCPS.compile`**.
Its output records the source-to-equation computation and target typing proof.
The runtime payload is the existing native object thunk; no target payload proof
is supplied by the caller. The result interface exports the original alias
equations, so its client need not know the graph-normalized implementation.

`RecursiveAliasExamples` checks a source object containing both a self-intersection
cycle and a two-member pure alias cycle. The generated target package opens in a
closed client that forces the object and reduces to the empty native `DOT` record.
This constructor case does not implement term fields, nested member binders,
singletons, general dependent results, or sharing through opaque bounds.

`BoundedObjectCompilation.compile` extends that constructor case to a source
derivation for `let x = new … in x` at a requested recursive interface. The source
can open the object's recursive type, weaken its bounds, combine views, and close
the result again. The compiler reads that result's member declarations and uses
one generated name for every occurrence of a label, including occurrences in
different conjuncts. It checks all requested lower and upper constraints in the
generated recursive scope. Only after those proofs succeed does it close the
common existential telescope. The actual runtime output retains the let's
administrative lambda; its target typing proof covers that exact term.

The discharger reuses CTML's existing solver rules and their soundness proofs.
The original solver can report success while deferring a cyclic goal as a fresh
assumption. The constructor adapter rejects any residual assumptions or fresh
names. Its search treats a revisited lookup as a failed attempt, allowing another
bound to be tried. It can use already-proved equations as hints, then removes
those hints from the resulting proof. `failed` does not establish underivability,
and `fuelOut` is reported separately. No solver completeness is assumed.

`BoundedObjectExamples` compiles the alias-cycle object with two views of `A`,
one with `Bottom..Top` and one with its defining bounds, plus bounds on `B` and
`C`. It checks the generated consumer type and shared name, closes all guards,
and proves that a closed client returns the native `DOT` record. This remains
a type-only constructor case; opaque-path sharing and general term fields still
need the full compiler invariant.

## Native CTML recursion

`Term.fix f` evaluates its functional and unfolds into a lambda that delays the
recursive call. The first-class `Term.zfix = λf. fix f` has type
`∀A B. ((A → B) → A → B) → A → B`. Core's existing safety theorem has been extended
to this primitive. The executable inference algorithm currently returns `failed`
for `fix`; the declarative typing rule is supported.

Recursive types use scoped declarations, `type α = F(α) in ...`, represented by
`RecursiveType` and the `Recursive.HasType.recursive` rule. The body is a native
CTML type. Opening it binds a fresh name and supplies both `α ≤ F(α)` and
`F(α) ≤ α` as native subtyping assumptions. The context and result outside the
declaration are weakened under that name, so it cannot escape. Existential
packaging can hide it and export the appropriate bounds to a consumer.

This is a named equirecursive presentation, not a standalone `Ty.mu` constructor.
The checker requires each recursive occurrence to lie under an arrow or record
constructor, allowing negative occurrences and native record/union/intersection
carriers. It rejects an unguarded recursive variable. No coinductive subtyping
rule or arbitrary equation-discharge axiom has been added.

`RecursiveSystem` addresses simultaneous package witnesses. It binds a finite group
of names with equations `Aᵢ = Pᵢ(A₁, …, Aₖ) → Qᵢ(A₁, …, Aₖ)`. The parameters and
results may contain native records, arbitrary constraints, and negative cross references.
`IndexedSystems.indexedOperator_contractive` checks the whole vector at once, and
`indexedValidates` validates every defining equation together with the weakened outer
assumptions. `MutualPackageWitnesses` specializes this construction to arbitrary CPS
interfaces and produces each component's `PackageWitness` from the native equations.
The checked source example defines
`A = {left : self.A} & {right : self.B}` and `B = self.A → self.B`.
`Recursive.HasType.recursiveSystem` now closes the entire shared scope. Its premise
weakens the outside term context, term annotations, and result under all fresh names.
Type and term weakening/substitution, constraint transport, canonical forms, progress,
and the indexed fundamental lemma cover this rule. `IndexedBlocks` checks annotation
closing and transports value substitutions under the finite group of names.
The example constructs both package values with Z, passes them through native `left`
and `right` fields, calls a function from the second package with the first package,
and reduces to `Unit`. Its closed typing uses `recursiveSystem`, and its operational
safety follows from the same general target theorem.

`RecursivePackage.packTyping` goes further: for any finite system and native payload
type, it generates one existential telescope around all names and both directions
of every equation. Its only typing premise checks the payload inside the recursive
scope. `bindBlock_open` instantiates each universal with the name already in that
scope, and `consumerSubtype` discharges the equation guards. The names are then
hidden by the simultaneous recursive rule. The mutual example also exports its
package and opens it in a separately typed consumer, using only the abstract names
and exported equations; that complete program still reduces to `Unit`.
General source-constructor translation still has to compute the systems, translate
their source payloads, and derive the required source-interface coercions.

`RecursiveType.validates` proves that a valid kind environment extends to one
validating these equations. `RecursiveCanonical.lean` uses this interpretation to
prove canonical forms through recursive declarations; `RecursiveProgress.lean`
then proves `Recursive.HasType.progress`. The latter is generalized to arbitrary
kind-valid subtyping contexts, so its recursive case can open the defining equations.
This kind-based theorem establishes one-step progress. Safety of all reducts is now
proved separately by the indexed fundamental lemma below. Syntactic preservation
remains separate from the proved native `HasType.soundness` theorem for CTML plus Z.

The `Indexed*` modules supply the richer interpretation used by the recursive
safety argument. A type denotes positive and negative observations indexed by an
evaluation budget. Arrow behavior and record contents use strictly smaller indices;
universals quantify over arbitrary indexed candidates, and constrained types and
guards range over the current finite prefix. Negation exchanges the two predicates.
No positivity restriction on recursive occurrences is imposed.

`Subtype.indexed` validates all current Core subtyping rules in this model, including
both function distribution rules and record union/intersection distribution.
`RecursiveType.indexedOperator_contractive` connects the existing syntactic
guardedness check to a constructive fixed-point operator; its unique solution
validates the recursive name/body equation. `RecursiveType.indexedValidates`
extends any valid outer context with both defining assumptions. Weakening,
substitution, and downward closure of observations are proved. As a concrete check,
`IndexedExamples.noUnitField` rules out refining the recursive Node's function-valued
`next` field to a Unit record; the outer-kind model alone cannot distinguish those
field types.

`IndexedFundamental.lean` proves `HasType.indexed` and `Recursive.HasType.indexed`:
every typed subject, closed under a well-related value substitution, satisfies the
computation interpretation at every finite budget. The Z case uses strong induction
on that budget and the actual delayed unfolding, without requiring termination.
Native record construction, projection, ascription, and class tests are covered.
Annotation closing under a fresh type binder preserves the subject, so the universal
and recursive-declaration cases use arbitrary semantic candidates and the guarded
fixed point respectively. `Recursive.HasType.safe` concludes that every finite
execution ends in a value or a term that can step. No recursive consistency axiom
or placeholder is used. This does not assert syntactic preservation.

`CTMLCore.RecursiveExamples` constructs `Node = {next : Top → Node}` using Z and
proves that the constructor evaluates to a native record. `RecursiveCompilation`
closes the original negative recursive-member example with a checked source DOT
derivation and a generated CTML record package; its client reduces to an ordinary
identity function. The source object's self reference occurs in types.

`TermCPS` now also compiles runtime self references. An object becomes
`fix (λself. λunit. record fields)`. A field holds a suspended CPS computation, and
projection forces the object followed by that field. This accommodates path aliases
and nested objects without eagerly evaluating an unused field. The general source
typing preservation and operational correspondence of this pass remain unfinished.

`TermCPSLookup` now relates source definition lookup to field invocation in the
actual compiler output. `compiled_object_field_call` accepts any core typing of
an object and a source `Defs.Has` proof for its selected field. It constructs the
compiled object and field body, then proves their target reduction to that body
with the delayed self thunk and caller continuation substituted. Outer free
variables are retained. The theorem covers path aliases and nested objects as
field right-hand sides, and derives distinct source fields from the object typing,
including subsumption. Label allocation must be injective on the object's labels,
as provided by the existing finite-support allocation.
`objectSelf_eq_delayedFix` identifies that self thunk with the native Z primitive's
delayed recursive function. `self_force_record_exact` and `self_force_field_call`
show that recursive self access returns the same compiled record and selected field,
with one additional administrative beta step. The remaining operational correspondence
must relate the field substitution expression to source path opening and store lookup.

`Recursive.HasType.weakenAt` proves term-context weakening through all constructors,
including recursive declarations. The interface rules can therefore package and
consume recursively typed payloads in arbitrary surrounding term contexts.
`Recursive.HasType.mapAssumptions` and `dischargeAssumption` also transport and
discharge bounds underneath recursive declarations, retaining both directions of
each scoped equation.
`RecursiveTypeWeakening.lean` preserves typing when a fresh type variable is inserted,
including the guardedness of every local definition. `RecursiveSubstitution.lean`
proves term substitution with a recursively typed nonexpansive argument, even into
a body whose derivation was native CTML. It also proves that unfolding Z preserves
recursive typing. `RecursiveTypeSubstitution.lean` proves type substitution through
all constructors, preserving guardedness of local definitions and transporting
both directions of their equations. The full value-inversion lemmas and preservation
remain open.

`CTML.recursiveProjectionInverse` derives DOT's path record-introduction rule in
`Recursive.HasType`: a typing of `record.field : T` yields a typing of
`record : {field : T}`. The proof transports recursive scopes through the rule
and combines intersection premises using native record distribution. It does not
assume recursive preservation; the value-inversion lemmas needed for that theorem
remain separate obligations.

Unrestricted record-*subtyping* inversion cannot simply be added to the current recursive
target. `RecursiveInversionObstruction.lean` checks the equation
`X = {a : [{a : Top} ≤ X] ⇒ Bottom}`, which passes the existing guardedness check.
In a separate hypothetical extension, assuming its guard and inverting the record gives
`Top ≤ Bottom`; abstracting that conditional derivation establishes the guard itself.
The resulting closed derivation types the stuck application `Unit Unit`.
`extensionNotSafe` verifies that failure, while `nativeRejectsStuck` uses the actual target's
safety theorem to reject the same term. No inversion rule was added to CTML Core.
This rules out that particular shortcut for obtaining native constraints from the coercions;
it is not an impossibility result for the requested DOT encoding.

### The earlier all-fields-transparent experiment

This experiment made every record field reflective, forcing its stronger recursion
guard. It is retained as checked prior work; the intended target must permit
record guards. The mixed model below separates those roles instead.

`CTML/TransparentSafety.lean` proves operational safety for a separate experimental
judgment, `CTML.Transparent.HasType`. It uses the existing native term syntax and
evaluator, including records, projection, and Z. Its subtyping relation admits
native Core derivations with proved premises, same-field record inversion,
component inversion for labelled unions, cut, and inversion inside universal and
constraint abstractions. The current compiler target remains unchanged.

The model in `TransparentRecords.lean` retains both positive and negative field
observations at the current index. Negative observations also hold of terms
without the selected field. In this model, inclusion between two same-field
record candidates reflects inclusion between their payloads, including through
an opaque intermediate type. Both record distribution rules, negation, arbitrary
constraints, and impredicative universals are validated by the new interpretation.
Binding and substitution laws are proved against that interpretation as well.

This requires a stricter recursion rule. A record wrapper no longer guards its
payload; every recursive occurrence must pass through an arrow. `ArrowGuarded.lean`
and `TransparentRecursion.lean` prove contractiveness and both defining equations
for such recursive types. This admits `{next : Top → X}` and negative occurrences
such as `{consume : X → Top}`, but rejects the exact constraint cycle above.
`Definition.validates` preserves context validity when a definition is opened,
and `Definition.noCollapse` excludes `Top ≤ Bottom` in its closed defining scope.

`CDotFCCT.CTML.Transparent.HasType.safe` proves that every finitely reachable term
is a value or can step. Its fundamental lemma covers every rule
of the experimental typing judgment. This is an operational safety theorem;
it does not assert syntactic preservation. `TransparentSystems.lean` now also
validates the native `RecursiveSystem` formation rule in this model: all components
have an outer function arrow, with arbitrary mutual references beneath it.
`System.validates` proves the equations together, `System.noCollapse` proves
consistency of a closed defining scope, and `Typing.recursiveSystem` closes the
entire block. The corresponding `HasType` rule is included in the safety theorem.

`TransparentExamples.lean` checks a polymorphic identity cast whose only bound is
`{member : A} ≤ {member : B}`. A closed instance discharges that bound and returns
its original value. A second program uses Z to construct a native recursive record,
with checked typing, safety, and four reduction steps to a record value. The file
also checks rejection of the old recursive-constraint counterexample.

`TransparentRows.lean` additionally defines a ghost carrier as a union of labelled
record types. On a singleton record at label `a`, both observations of the union
reduce to those of its `a` component. Thus `row_inverse` reflects component
subtyping without requiring any component to be inhabited. Labels can be repeated
because each label is associated with one type by the row's assignment function.
The experimental subtyping relation's `rowInverse` rule is validated by this
theorem, and the typing safety theorem covers the enlarged relation. This does
not assert component inversion for arbitrary runtime record intersections.

`CarrierBounds.lean` stores each member witness in a positive upper slot and a
negative lower slot in the same carrier. `MemberSlot.lowerBound` and `upperBound`
recover ordinary subtyping facts through an opaque intermediate type, while
`variance` checks contravariant lower bounds and covariant upper bounds. Other
carrier components may be arbitrary. `InvertingSubtype.nativeWith` permits
native Core reasoning under a finite collection of already proved bounds;
`rowMono` uses it to compose component derivations.

`CarrierLayout.lean` computes paired slots from a finite list of source member
labels. It works for any label type with decidable equality, without requiring
a global injection into strings. `name_injective` separates labels and polarities;
`components_at` proves lookup of the generated witness and its negation, and
`precise_eq_slot` exposes either member of the generated complete row for the
bound-extraction lemmas. All views share the fixed label allocation.

`CarrierSharedWitness.lean` exercises the original `SharedWitnessRegression`.
The target slots and complete precise rows are generated from the finite member
support. There are only two assumed guards: the precise carrier of `q` is below its
declared intersection, and the precise carrier of `p` is below `q.X`. The proofs
derive both upper views of `q.X`, then derive `Top ≤ p.A ≤ Bottom` using the same
`p.A` witness. The resulting guarded identity is typed under universal and
constraint abstractions, and its operational safety is checked. No valid model
environment can discharge both context guards for this inconsistent source
context. The individual member bounds are not separately assumed.

`CarrierTranslation.compileSubtyping` now takes an actual `Core.Subtyping`
derivation and generates the layout, guards and target proof. Its `TypeCode`
certificates cover Top, Bottom, selections, member declarations, intersections
and named singletons. `ContextCode` records one guard for each source binding;
the compiler follows source lookup and subtyping premises rather than assuming
the requested member bounds. Its mutual traversal handles `var`, `sub`,
`andIntro`, `self` and `sngl` for paths, and Top/Bottom/reflexivity, transitivity,
intersection rules, member variance and both bound-selection rules for subtyping.
The two singleton replacement rules use `TypeCode.transport`, which checks
replacement through selections, named singleton types, intersections and member
bounds. `CarrierLayout.precise_bounds` derives equality of both paths' member
witnesses from the one singleton relation, and `precise_symmetric` recovers its
reverse direction. Replacement therefore introduces no additional assumptions,
including in contravariant lower bounds. Extensions beyond the alias's endpoints,
field rules, recursive opening and the other unsupported cases return `none`.
A source context with unsupported binding types also fails explicitly.

Allocation uses the finite cross product of relevant scoped paths and slots: one
slot for the runtime payload type, plus every source member label. The slot kinds
are disjoint before conversion to native field labels. This includes a member
such as `q.A` when the source only reaches its
bounds through `p : q.type`: allocating only directly selected members would
incorrectly specialize the missing witness to a default type. Context bindings
and singleton encodings require complete rows. `Layout.ofEvents_complete` proves
coverage of each registered path, and `completeAt_member` ensures that every
component used in such a row has an allocated witness.

`CarrierCompilationExamples.lean` runs this compiler on the original
shared-witness source derivation. It generates six witness variables, covering
both member labels and the payload type at both paths, and exactly two context
guards. It then checks the
derived collapse under those guards and a closed identity type that abstracts
all the witnesses and guards. A second source regression transports an abstract
member through a singleton alias and checks allocation of the unselected owner
member. Both directions of direct replacement compile inside a contravariant
bound nested under an intersection, with only the three source-context guards.
Another example checks member variance. These examples supply no target bound
proofs. `CompiledSubtyping.closedTyping` checks the generated universal and
constraint abstractions for every successful result.

The payload slot is paired in the same way as member slots. `runtimeView` places
an upper bound on it, while `payloadBound` recovers a usable bound on the actual
payload type. `memberView_intro` and `runtimeView_intro` construct carrier views
from known member bounds and a payload typing bound. No carrier component must
itself be inhabited by a runtime record.

`CarrierRuntime.lean` adds `CarrierTranslation.compileVariable`, which takes an
actual `Core.Typing` derivation whose term is a variable, generates its carrier
environment and follows the supported
path typing rules. It produces a typing derivation for the exact variable case of
`TermCPS.compile`, rather than replacing the program with a constant term. The
target term context assigns each variable the payload type in that variable's
carrier; the result is passed to the CPS consumer together with the established
carrier guard. `CompiledVariable.runtime_eq` checks the syntax equality and
`CompiledVariable.typing` checks the target derivation. The result interface now
binds fresh copies of every member witness and of the payload type. Its requested
view may still mention the source environment's existing witnesses, as needed
for path-dependent result types. The input environment is open; this pass does
not yet implement general term constructors.

`CTML/CarrierPackages.lean` generates the schema for arbitrary finite member
support. Writing `W` for the member witnesses, `D` for the payload type, `C` for
the requested carrier view, and `R` for the answer, the schema is:

```text
(∀ W, D. [precise(W, D) ≤ C] ⇒ D → R) → R
```

`telescope_substAt` checks capture-avoiding substitution through the generated
binders. `telescope_congr` proves that rebinding all supported components removes
every dependence on their initial concrete assignments. `packingInstance`
instantiates the telescope with the producer's existing types and uses its
already-derived carrier bound to discharge the sole guard. The compiler supplies
this evidence itself; callers of `compileVariable` still supply only a source
typing derivation. `packageSubtype` lifts a carrier bound to a bound between whole
packages. `CompiledSubtyping.closedPackageTyping` uses it to produce a closed
identity coercion, with witness and context constraint abstractions generated
from the source derivation. The singleton-replacement regression checks this
package-level coercion as well as its earlier ghost-bound coercion.

`CTML/MixedInterfaces.lean` extends the existing existential telescope lemmas
to the record-guarded mixed typing judgment. Its packing instances can use carrier-derived
bounds, its consumers introduce the same type and constraint abstractions, and its
CBV packing rule evaluates the original payload before making the package.
`CTML/MixedCarrierOpening.lean` computes the corresponding continuation scope:
fresh component types, weakened outer assumptions and term context, the carrier
guard and one payload binding. `openComponents_iff` identifies checking this scope
with the existing `InterfaceOpened` premise. Its scope lemmas prove that the
requested view and answer are weakened across exactly the new witness block.
`CarrierRuntimeExamples.lean` checks the source variable compiler on the alias
regression. It also uses the generated packing instance and opening scope for a
closed target package hiding a member witness and a native record's payload type.
The consumer initially sees only that abstract
payload type; its carrier guard exposes the record's `run` field. The complete
program has a safety proof and reduces to Unit in five native target steps.
This second example checks the runtime representation, not a general source-object
compiler.

`TransparentRecursivePackages.lean` connects simultaneous recursive scopes to
existential packaging in this target. It can export the defining equations or
only the requested proved guards. `packCarrierTyping` instead uses the generic
carrier schema and keeps the defining equations private; `CarrierBinding.lean`
proves that this schema commutes with weakening by the whole recursive block.
`CarrierRecursiveExamples.lean` checks a native record containing a Z-defined
function under `A = Unit → B` and `B = Unit → A`. An existential client opens both
equations and calls through both arrows, reducing to Unit in ten steps. A second
client uses the generic carrier interface and returns the constructed record in
four steps, while both recursive types and their defining equations remain hidden.

`CarrierConstructorCompilation.lean` now derives the mixed target's typing judgment for
the two existing automatic source constructor passes. Its `carrierTargetTyping`
theorems reuse the generated recursive systems and proved bounds, and cover the
exact `TermCPS.compile` output. Their alias interfaces are still distinct from
the carrier encoder's views; these theorems do not establish a uniform type
translation or general constructor compilation.

The general translation is still unfinished: arbitrary paths, constructors,
dependent calls and recursive opening remain, including connecting their source
scopes to the generated existential scopes. The mixed inversion rules remain
in the root bridge; the CTML Core dependency has not adopted them. The existing
constructor passes keep their native proofs alongside the mixed proofs.

### Record guards with reflective ghost fields

`CTML.Mixed` fixes one field-label policy throughout each derivation. Ordinary record
fields use the existing delayed interpretation, so a record constructor directly
guards recursive occurrences in any payload, including arbitrary constraint endpoints.
Ghost fields use the transparent interpretation and permit component inversion.
They propagate the guardedness obligation rather than serving as guards themselves.

`MixedSubtyping.subtype_sound` validates every native rule; `MixedInversion` adds
inversion only at designated ghost labels, including labelled carrier unions.
`MixedRecursion.Definition` constructs genuine fixed points for the corresponding
guarded syntax. The scoped equations and all native typing rules, including Z,
are covered by `Mixed.HasType.safe`. `MixedRecordSystems` additionally validates
simultaneous groups whose components each have an outer ordinary record field.
This rule is a sufficient formation rule; it does not yet accept every group in
which some ordinary field appears along each cycle. `MixedSystems` also validates
the existing simultaneous function equations generated by the type-only alias compiler;
this compatibility rule leaves ordinary records available as guards.

`MixedSharedWitness` reuses the exact carrier syntax, witnesses, and two context guards
of the original regression. It derives `Top ≤ p.A ≤ Bottom` without introducing
separate member-bound assumptions. The same policy permits `μX.{next:X}` and a
ghost wrapper around that record. `MixedExamples` checks a finite record at
`μX.{next:Unit ∪ X}`, casts it through a constraint abstracted over a ghost-field
bound, and projects Unit. A second program reuses the native mutual-record execution.
The old constrained record cycle is legal at an ordinary label, while consistency
rules out its previous inversion-based collapse.

This resolves the target-model conflict between useful record guards and ghost-bound
extraction. It does not yet prove the full source representation. `MixedFieldNames`
proves the default runtime-label allocation ordinary and disjoint from every generated
carrier name; `carrierPolicy_names` proves all carrier slots reflective. Custom
environments must retain that separation. The compiler must also ensure every recursive
carrier cycle reaches an ordinary record guard or another permitted guard. Cycles
entirely within ghost components remain unguarded. The actual partial carrier compiler,
its runtime variable pass, generated packages and whole-package coercions now produce
mixed proofs. The port preserves source inputs, witness allocation, computed types and
runtime syntax, without adding caller-supplied target evidence. Both existing type-only
constructor passes also produce mixed proofs through `carrierTargetTyping`; their alias
interfaces remain distinct from the general carrier interface.

The native constructor work remains usable independently of inversion.
`TermCPSObjectTyping` generates the self equation from arbitrary native field types
and proves typing of the exact CPS object syntax given the field induction hypotheses.
`NativeFieldSharing.packTyping` uses only a payload typing to generate a shared-member
package for a record with `head` and recursive `next`. Both witnesses and both
recursive bounds are constructed by that theorem. General source-field compilation
and source-to-interface alignment still have to supply the induction hypotheses.

## Shared views reached through bounds

The checked `SharedWitnessRegression` example uses:

```text
q : {X : Bottom .. {A : Top .. Top}} & {X : Bottom .. {A : Bottom .. Bottom}}
p : q.X
```

DOT derives `Top <: p.A <: Bottom`. Translating each upper view as an independent
weak existential permits the same target producer to choose `Top` for one view and
`Bottom` for the other. The file checks both packing instances and proves that no
single closed witness satisfies the combined bounds. Native intersections alone
do not equate those existential witnesses.

`Alignment` merges bounds and payload intersections when the common witness scope
is already known. The remaining general translation must establish that alignment
also through abstract bounds, aliases, and calls. The regression rejects one naive
construction; it does not prove that another encoding is impossible.

`ObservationBind` supplies composition at a fixed answer type. Its `AnswerView`
grammar includes arrows ending in that answer, intersections, universal quantification,
and arbitrary constraint abstraction. Both CPS results and complete existential packages
belong to this grammar. The single term `λk. input (λv. client v k)` sequences an input
without losing any of the client's views, in native and recursive typing. Its identity
specialization removes an extra CPS layer. The execution theorem reaches the client's
original computation and does not require that computation to terminate.

`InterfaceBind.bindAnswerView` extends this operation from an ordinary CPS input to
an entire existential interface. The client is checked under the same witness telescope
as the input, and the result stays outside that telescope. `repackerTyping` constructs
`λv. λk. k v` at the corresponding polymorphic consumer type for any interface: its
proof instantiates each bound type variable with itself and discharges each guard from
the current scope. No external packing instance is required. Existing `Interface.Map`
proofs can then change the exported view, and `repackReturns` preserves the payload.
These rules compose already-constructed interfaces; they neither construct an interface
from arbitrary `Core.Typing` input nor fuse independently chosen existential witnesses.

`SharedWitnessFusion` strengthens this regression using CTML's existing safety
theorem. The same `pack Unit` has both independent package types. Assigning it a
package type with one witness satisfying `Top ≤ A ≤ Bottom` would admit a typed
consumer that reduces to the stuck application `Unit Unit`. This argument works
at every answer type. Consequently, neither a native subtyping proof nor a typed
conversion returning the original package can fuse those independent views.

The issue also occurs below an ordinary field, without an outer abstract member:

```text
p : {child : {A : Top .. Top}} & {child : {A : Bottom .. Bottom}}
```

The checked source derivation obtains `Top <: p.child.A <: Bottom`. Meanwhile,
the native CTML record `Container {child = pack Unit}` inhabits the corresponding
two independently translated field types. `noFieldFusion` proves that subtyping
cannot turn those into a field containing a shared-witness package. Thus sound
constraint-inversion rules alone cannot repair this representation. The general
translation must retain witness sharing before it produces these independent
packages, or use a different representation. These results do not rule out a
general encoding with that stronger invariant.

### Explicit coercions through a precise native record

`CTML.Coercion` checks another approach to the bounds case. A precise member row
contains an arbitrary payload `D` and two administrative function fields:

```text
Precise(D, A, R) = DOT.Member {data : D, lower : A → R, upper : Top → A}
View(L, U, R)    = {lower : L → R} & {upper : Top → U}
```

Given `Precise(D,A,R) ≤ X` and `X ≤ View(L,U,R)`, the checked construction produces
a CPS conversion from `L` to `A` and a direct conversion from `A` to `U`. It rebuilds
a native marker record with the supplied continuation or value in the selected field,
applies the given subtyping constraint, and projects that field. An unused field can
contain a suspended Z loop. The execution theorems prove that this loop is never
called and that the conversions return the original value. Records themselves are
not Church-encoded.

`throughAbstractTyping` composes a lower-bound view and an upper-bound view of the
same opaque `X`, retaining one `A`. `noCommonPreciseRow` uses target soundness and
the exact execution proof to rule out the contradictory closed views from the
regression, at every answer type and with any inhabited payload type.

This is a checked representation experiment, not the general compiler invariant.
The compiler still has to construct precise rows and maintain their witness scopes.
In particular, a typed coercion is **not** a native `Subtype` derivation and cannot
silently discharge a package guard. `noNativeCollapse` verifies this distinction:
even under the two contradictory row-view assumptions, CTML's native subtyping
does not derive `Top ≤ Bottom`. Composition with general source subsumption and
intersection introduction therefore remains to be designed and proved.

`CoercionRefinement` checks part of the intersection obligation. The upper-bound
conversion has exactly the same syntax at the original type `E` and at the new
upper bound `U`, so CTML's intersection rule gives `E & U`. The lower-bound
conversion can similarly retain `E` when its row constraint is
`Precise(D,A,A) ≤ View(L,U,A)`: using the identity continuation gives a direct
conversion returning the original value, now typed at `E & A`.
This lower-bound premise is stronger than the fixed-answer premise above. There
is no general construction of this constraint from an arbitrary source typing
derivation yet; the refinement lemma does not establish that construction.

`NegativeWitnesses` supplies a different conversion at a fixed answer `R`. A
`NegativeWitness s R A` contains an `AnswerView R N` and actual native subtyping
proofs `A ≤ N` and `N ≤ A`. CPS existential packages supply this evidence directly.
`recursivePackageDefinition` constructs it for any interface containing self
references, using `A = (interface.consumer R) → R`; the outer arrow guards those
references, and the local recursive equation supplies both directions.
`lowerWitness` flattens the original lower-bound conversion using that evidence.
The same syntax retains any existing negative view, including an opaque one with
its own checked equivalence. Applying the result reduces to applying the input
computation; this is an eta expansion, not literal value identity.

`NegativeSelections` preserves that representation through constraint abstraction:

```text
Select⁻(D, C, R) = ∀K. [Precise(D, K → R, R) ≤ C] ⇒ K → R
```

The quantified variable is the package's consumer type. A lower-bound use constructs
the selector without choosing a consumer or providing an already-opened member witness.
This selector is itself an `AnswerView`, so refinement retains it alongside earlier
negative views. At elimination, `negativeSelectorInstance` selects the carrier's existing
consumer. `negativeSelectorWitness` also handles an opaque name `A` with actual native
proofs `A ≤ K → R` and `K → R ≤ A`; a recursive package supplies these via its equation.
The two views in `throughNegativeSelectorTyping` may have different lower and upper
bounds but use the same carrier and precise witness. Its execution theorem returns
to the input computation without requiring that computation to terminate.
This is a rule for witnesses equivalent to a package arrow, not a proof that every
abstract type variable or every quantified `AnswerView` has such an equivalence.

`PackageWitnesses.bindPackageWitness` makes this representation part of an actual
existential interface. It binds `K` and `A`, assumes `A ≤ K → R` and `K → R ≤ A`,
then opens the remaining interface with the same `A`. The additional consumer binder
is inserted behind the member, preserving its index in the rest of the interface.
`bindPackageWitnessInstance` instantiates both names and discharges both guards from
an actual `PackageWitness`; `PackageWitness.recursive` constructs one from a recursive
package's scoped equation. Conversely, `packageEvidence` reconstructs the representation
solely from the opened interface's assumptions. Native and recursive consumer rules
make those assumptions available over the full client. No extra representation premise
is required from a caller that has already opened this telescope.

The closed `PackageWitnessExamples` producer exports `A = CPS(A → A, Unit)` with
its consumer. Its payload is a native record containing a polymorphic value and an
operation accepting `A`. The client opens the interface, obtains the representation
from its guards, converts the value through the lower bound, and invokes that operation.
The checked reduction follows both native field projections and the original package
computation to Unit. This verifies construction and elimination of the representation
interface; source derivations must still generate the remaining interface and bounds.

`NegativeRecords.strengthenedTyping` applies this operation to native record fields.
The strengthened row is a native subtype of the old row, retaining its opaque
supertypes, and it exposes the chosen field at the already-opened witness `A`.
`strengthenedWitnesses` constructs the invariant needed for further refinements.
`strengthenedSelectionTyping` and `strengthenedSelectionWitnesses` do the same for an
abstract selector, before its consumer is selected; they reuse the same record term.
The execution theorem permits the original field projection to evaluate before
running the resulting field computation. The closed recursive example checks the
case `A = CPS(A → A, Unit)`, where `A` differs from the answer: a self-application
client and a client using the retained universal view both return Unit. Its carrier
has separate intersection components for the lower and upper bounds. A third client
uses the generic selector conversion through those two components and also returns Unit.
These are target representation and composition proofs. The full compiler still
has to generate the interfaces, carrier constraints, and negative-witness evidence
from the source; an arbitrary opaque type variable does not carry that evidence.

## Earlier minimal-FCCT recursive extension

The target constructor is `μX. P(X) → Q(X)`, represented by `WFTy.recArrow P Q`.
Both components bind `X`; negative occurrences are allowed. `Subtype.recUnfold`
and `Subtype.recFold` prove both directions of the unfolding equation. Thus
`D = μX. X → X` supplies `D ≤ D → D` and `D → D ≤ D`, discharging the direct
recursive-member example's two equality guards.

The constructor also accommodates a CPS function equation such as
`D = D → (D → R) → R`, by choosing the second component accordingly. The general
witness theorem works in open type contexts and with polymorphic/constrained
components. It has not been proved that every mutually recursive DOT type-member
graph can be reduced to these guarded equations.

This extension is not unrestricted `μX. T`: unguarded recursion is excluded, and
there is no coinductive subtyping rule. Term syntax/evaluation are unchanged.
Scoping, substitution, subtyping inversion, progress and preservation are checked
for the extension. `Landing.recursiveClosed` is proved for the two actual landing
predicates, so it adds no assumption to the public safety theorem.

## Constraint-abstracted selection experiment

`CTML/Selections.lean` tests a different representation for one selected member.
Here `D` is the payload type, `C` is a shared carrier, and `R` is the CPS answer:

```text
Sel(D, C, R) = ∀A. [PreciseMember(D, A, R) ≤ C] ⇒ (A → R) → R
```

The constraint is an ordinary FCCT-style constraint on native CTML records, using
the existing marker-row construction. It is not a fresh existential package for
each view. `selectLowerTyping` constructs this selector from
`C ≤ MemberView(L, U, R)`, a payload at `D`, and a value at `L`, without choosing
`A`. Later `selectorInstance` uses an existing witness `W` with
`PreciseMember(D, W, R) ≤ C`. `selectUpperTyping` then obtains an observation at an
upper bound, even if that bound was reached through another view of `C`.
`selectorCarrier` checks the contravariant transport induced by a carrier-subtyping
proof. All of these are derived native typing/subtyping rules.

`throughSelectorTyping` composes construction and observation across two views;
`throughSelectorSteps` proves that the resulting computation passes the original
value to its continuation. `SelectionExamples.programTyping` discharges every
guard in the empty context and `programSteps` returns the identity function.
Thus the checked construction is not relying on inconsistent assumptions or a
diverging cast in that example.

This is a candidate component, not the completed DOT translation. The compiler
does not yet use it. It still needs a carrier invariant for arbitrary paths,
multiple members, aliases, dependent calls, and constructors. The introduction
and elimination rules produce CPS coercions, not native subtyping proofs between
all source type translations; general member variance and intersection handling
therefore remain obligations.

`CTML/ObservationViews.lean` addresses retention of existing CPS views. An
`Observation R T` describes a type built from `(A → R) → R`, intersections,
universals, and constraint abstractions; `R` stays outside the introduced binders.
The term `mapLower payload observed` maps the member conversion over an observation.
The same syntax has an identity typing at every original result type, so
`Observation.retain` preserves the whole observation grammar. `mapLower_select`
additionally assigns the selector type when the carrier has the required lower
bound. Native intersection introduction combines those proofs in
`mapLower_refinement`. The corresponding recursive lemmas accept payloads and
observations typed using local recursive declarations.

`Returns.mapLower` proves that a coherent observation still passes its original
value to every value continuation, provided the marker payload and observed result
are values. This execution property is preserved under repeated refinements.
`ObservationExamples` exercises two such refinements: the second retains the
first selector's quantified and constrained type, as well as the two original
observations. Its answer is `Unit`, distinct from the witness `Top → Top`.

This retains intersections of observations; it does not fuse independently
chosen existential witnesses or derive a raw intersection payload. The general
compiler still needs to construct the carrier constraints from source derivations
and account for fields and dependent calls. These lemmas do not establish that
missing invariant.

`CTML/ObservationRecords.lean` lifts refinement into native record fields when the
complete row is available. Given the field names and a type for each suspended
observation, it rebuilds the same class and field layout with identity mappings on
the observations. `strengthenedTyping` assigns a row in which the selected field
has both its original observation type and the new selector type. `strengthenLe`
projects that row to the old row by ordinary native subtyping. Consequently,
`refinement` retains any opaque supertype justified by the old precise row. Both
native and recursive typing versions are checked.

`strengthenShapes` records that the new row still consists of observations, so
the construction can be repeated. `projectReturns` proves fieldwise execution:
whenever an original field passes a fixed value to its continuation, the rebuilt
field passes that same value. The new record is a value without forcing any field.
This is fieldwise preservation; the rebuilt record is not syntactically the old record.
`ObservationRecordExamples` applies the construction to two successive fields,
then consumes both selectors in the empty context, with checked reductions.

The general source translation must still construct these precise layouts and
carrier constraints. Supplying a layout and native bound proofs to these local
lemmas is not a translation of an arbitrary `Core.Typing` derivation.

## Scoped witness support

`MemberUses.typing` and `MemberUses.subtyping` traverse every constructor of the
full input judgment, choosing one fresh representative at each cofinite premise.
A member key records its owner's binding site, its complete field path, and its
label. Binding sites are derivation addresses: two unrelated binders do not become
the same owner because they happen to choose the same numeric source variable.
Type references are collected even when their derivation uses no selection rule.
Bound paths inside type syntax are considered when that source binder is opened;
this pass does not elaborate their existential interfaces.

The finite table is scoped. External owners have names at the root; entering a
binder introduces that owner's member block. `scopedWitness_bind_fresh` proves that
outer references change by exactly CTML type weakening, and `typing_scopes` proves
the traversal's binder freshness. Scoped singleton facts are retained with their
source proofs rather than used to merge unrelated outer witnesses. The checked
examples include both opaque bounds exposing `p.A`, both field views exposing
`p.child.A`, and function-local facts that must not escape to the parent scope.

`AliasConstraints.compile` adds a source-to-constraint phase. It considers the
singleton facts at one scope and the names already requested by the derivation.
For each common field extension with both endpoints present, it generates both
native witness inequalities and a constraint-abstracted identity coercion. Each
entry retains the source equality and checked source subtyping in both directions;
`generate_complete` proves that every such supported extension is included. The
pass checks the complete base field path, so an equality at `p.base` cannot also
identify `p.other`. Function-local facts generate guards only at that local scope.

The closed alias example instantiates the two witnesses with `Unit`, discharges
both generated inequalities by reflexivity, and runs the generated coercion into
a native record. It checks a use of the alias schema, not the whole source program.
The bounded type-only constructor now discharges its source-requested member
bounds using actual generated witnesses. Connecting scoped singleton equations
and native carrier constraints to general constructors remains unfinished.

## Remaining translation obligations

1. The target's operational safety is proved by `Recursive.HasType.safe`.
   A separate syntactic preservation proof for scoped recursive declarations would
   require further value-inversion results; the translation can use the safety theorem
   without that proof.
2. Connect the checked scoped witness allocation to package construction, recursive
   self references, function calls and aliases, proving that each name represents
   the source member consistently. Naming and scope weakening are implemented;
   opening a package afresh for each occurrence still loses semantic sharing.
3. Translate record definitions and recursive self bindings, constructing the
   package witnesses and their constraints. The type-only constructor pass now
   generates structural alias equations, including cycles, and discharges requested
   bounds for the return-self let case, but does not cover
   term fields or nested type binders. The earlier recursive-member and static-record
   examples do not provide a general object-translation theorem either.
4. Generalize the checked dependent-function compilation to arbitrary dependent
   results using that common witness environment, without hidden witnesses escaping.
5. Construct target terms and typing derivations for the full `Core.Typing` input
   judgment. The complete input datatype and total runtime pass do not supply this
   preservation theorem. If elaboration inserts explicit coercions into that pass,
   prove that their insertion respects source evaluation and shared witnesses.
6. Relate source store/path reduction to target reduction. The target package
   examples prove their own execution, not an operational correspondence for DOT.

None of these points proves that another encoding is impossible. They specify
the obligations still missing from this implementation.

## Validation

From `lean/`, with the existing Mathlib cache:

```sh
lake build CDot CDotFCCT FCCT CTMLCore -q --log-level=error
lake env lean ../notes/fcct/Audit.lean
lake env lean ../notes/fcct/TranslationAudit.lean
```

If setting up a fresh checkout, obtain the imported Mathlib cache first:
`lake exe cache get Mathlib.Data.Finset.Basic Mathlib.Tactic`.
The minimal FCCT library itself depends only on Lean core. cDOT, FCCT, CTML Core,
and CTML Full use Lean 4.34.0. Both CTML manifests use the same Mathlib 4.34.0 pins.
