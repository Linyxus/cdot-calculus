import CDotFCCT.OpenTyping
import CDotFCCT.RecordCompilation
import CDotFCCT.DependentCompilation
import CDotFCCT.RecursiveCompilation
import CDotFCCT.CoreDerivation
import CDotFCCT.MemberScopeSafety
import CDotFCCT.MemberUseExamples
import CDotFCCT.AliasConstraints
import CDotFCCT.AliasConstraintExamples
import CDotFCCT.TermCPSRecords
import CDotFCCT.TermCPSExecution
import CDotFCCT.TermCPSLookup
import CDotFCCT.FieldNames
import CDotFCCT.CTML.RecursiveInterfaces
import CDotFCCT.CTML.InterfaceIntersections
import CDotFCCT.SharedWitnessRegression
import CDotFCCT.SharedWitnessFusion
import CDotFCCT.SharedWitnessCoercions
import CDotFCCT.CTML.CoercionRefinement
import CDotFCCT.CTML.Selections
import CDotFCCT.SelectionExamples
import CDotFCCT.CTML.ObservationViews
import CDotFCCT.CTML.ObservationBind
import CDotFCCT.CTML.InterfaceBind
import CDotFCCT.CTML.NegativeWitnesses
import CDotFCCT.CTML.NegativeSelections
import CDotFCCT.CTML.PackageWitnesses
import CDotFCCT.CTML.MutualPackageWitnesses
import CDotFCCT.CTML.RecursivePackages
import CDotFCCT.CTML.NegativeRecords
import CDotFCCT.NegativeWitnessExamples
import CDotFCCT.PackageWitnessExamples
import CDotFCCT.MutualWitnessExamples
import CDotFCCT.RecursiveAliasTranslation
import CDotFCCT.TypeOnlyCompilation
import CDotFCCT.RecursiveAliasExamples
import CDotFCCT.BoundedObjectCompilation
import CDotFCCT.BoundedObjectExamples
import CDotFCCT.CTML.DischargeSearchExamples
import CDotFCCT.ObservationExamples
import CDotFCCT.CTML.ObservationRecords
import CDotFCCT.ObservationRecordExamples
import CDotFCCT.CTML.RecursiveRecords
import CDotFCCT.CTML.TransparentExamples
import CDotFCCT.CarrierSharedWitness
import CDotFCCT.CarrierCompilationExamples
import CDotFCCT.CarrierRuntimeExamples
import CDotFCCT.CarrierRecursiveExamples
import CDotFCCT.CarrierConstructorCompilation
import CDotFCCT.TermCPSObjectTyping
import CDotFCCT.CTML.NativeFieldSharing
import CDotFCCT.CTML.MixedExamples
import CDotFCCT.CTML.MixedSharedWitness
import CDotFCCT.CTML.MixedFieldNames
import CDotFCCT.CTML.MixedInterfaceWeakening
import CDotFCCT.CTML.MixedFieldSharing
import CDotFCCT.CarrierAliasExamples
import CDotFCCT.CTML.MixedFieldSharingExamples
import CDotFCCT.CTML.SelfFieldAnchor
import CDotFCCT.CTML.CarrierFieldViews
import CDotFCCT.CTML.MixedSubtypeSubstitution
import CDotFCCT.CTML.MixedGhostRowRecursion
import CDotFCCT.CTML.CarrierEquationSyntax
import CDotFCCT.CTML.CarrierEquationAliases
import CDotFCCT.CTML.CarrierAliasScopes
import CDotFCCT.CTML.CarrierEquationExamples
import CDotFCCT.CTML.CarrierRuntimeSelf
import CDotFCCT.CTML.CarrierFieldPresence
import CDotFCCT.CarrierRuntimeSelfSource

/-!
# The core-DOT to CTML Core bridge

This entry point imports the native-record target and its translation components.
It does not import the earlier minimal-FCCT encoding experiments. CTML Core supplies
records, intersections, unions, Z, and the scoped recursive declaration extension;
continuation encoding is used for existential witnesses and evaluation order.

The general typing-preserving translation is still under development. See
`notes/fcct-translation.md` for the checked components and remaining obligations.
The `Mixed` namespace proves safety with ordinary record guards and inversion only
for designated ghost fields. It validates the original shared-bound regression
and direct recursive-record programs under the same discipline. Its general source
compiler remains unfinished. `Transparent` is the earlier all-fields-transparent
experiment with arrow-only guards; that restriction is not the intended target.
The actual partial carrier compiler now checks subtyping and the runtime variable
case in `Mixed`, including generated existential packages and whole-package coercions.
The existing type-only constructor passes also produce checked mixed proofs through
`carrierTargetTyping`, reusing their generated equations and native bounds.
Their interfaces still need to be unified with the carrier encoding; the general
typing theorem is unfinished.
-/
