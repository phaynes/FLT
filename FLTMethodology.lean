import FLTMethodology.Probes.AutomorphicInfrastructureAudit
import FLTMethodology.Probes.BrauerNesbittBoundary
import FLTMethodology.Probes.DivisionPolynomialCoprimeAudit
import FLTMethodology.Probes.ExistingContracts
import FLTMethodology.Probes.FreyTorsionRankAudit
import FLTMethodology.Probes.GLnActionAudit
import FLTMethodology.Probes.GLzeroAudit
import FLTMethodology.Probes.GaloisRepActionAudit
import FLTMethodology.Probes.GaloisRepresentationActionAudit
import FLTMethodology.Probes.GoodReductionBoundary
import FLTMethodology.Probes.HurwitzRatHatAudit
import FLTMethodology.Probes.LibraryMatches
import FLTMethodology.Probes.MLTSourceBoundary
import FLTMethodology.Probes.PGL2ClassificationAudit
import FLTMethodology.Probes.TateDeltaAnalyticBridge
import FLTMethodology.Probes.TateDeltaFormalRoute
import FLTMethodology.Probes.TateLocalFormBoundary
import FLTMethodology.Probes.TateReductionBridge
import FLTMethodology.Probes.TateSubstitutionBridge
import FLTMethodology.Probes.TateTorsionTransportAudit
import FLTMethodology.Probes.TorsionClassificationAudit
import FLTMethodology.Probes.WeilPairingBoundary
import FLTMethodology.Scaffold

/-!
The isolated FLT proof-methodology library.

Nothing in this umbrella is imported by `FLT` or `FermatsLastTheorem`. It exists so Lake's
`FLTMethodology.*` target has an explicit root and so all architecture probes can be built as one
reproducible gate.
-/
