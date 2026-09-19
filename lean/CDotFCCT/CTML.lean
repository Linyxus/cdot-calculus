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

/-!
# The core-DOT to CTML Core bridge

This entry point imports the native-record target and its translation components.
It does not import the earlier minimal-FCCT encoding experiments. CTML Core supplies
records, intersections, unions, Z, and the scoped recursive declaration extension;
continuation encoding is used for existential witnesses and evaluation order.

The general typing-preserving translation is still under development. See
`notes/fcct-translation.md` for the checked components and remaining obligations.
The `Transparent` namespace is a separately checked experiment with record inversion
and stricter recursion guards. Its partial carrier compiler checks subtyping and
the runtime variable case in that judgment. The existing type-only constructor
passes also produce checked proofs in it through `carrierTargetTyping`.
Their interfaces still need to be unified with the carrier encoding; the general
typing theorem is unfinished.
-/
