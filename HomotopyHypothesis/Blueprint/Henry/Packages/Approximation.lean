import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.StdSimplexIsFinite
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.IsKanExtensionOfAnodyne
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.RealizationAnodyneDeformationRetract
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.RealizationIsPushout
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.ZeemanRelativeApproximation
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.ExistsDerivedSubdivision
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.SharpMkEqOfVertexMap
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.ExistsFoldedMappingCylinder
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.ExistsRelPrismSimplicialApproximation
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.KanExistsOfRelPrism

/-!
# Packages: relative simplicial approximation in Kan semi-simplicial sets

The steps of Rourke–Sanderson, *Δ-sets I*, Theorems 5.1 and 5.3 (finite cases), with Zeeman's
relative simplicial approximation theorem for finite simplicial complexes as the classical input.
They prove `isKan_exists_simplex_homotopicRel` (`Blueprint/Henry/KanSimplices.lean`): a map of a
simplex into the realization of a Kan semi-simplicial set with a combinatorial boundary is
homotopic, relative to the boundary, to the realization of a simplex with that boundary.

Route. Approximate (`exists_relPrism_simplicialApproximation`, RS Thm 5.1): after subdividing the
source (with a collar on `J`), the map becomes simplicial (possibly collapsing simplices), equal to
the given map on `J`. Then remove the collapses and the subdivision with the Kan condition
(`kan_exists_of_relPrism`, RS Thm 5.3): glue the prism of the subdivision to the relative mapping
cylinder of the simplicial map; the result collapses onto the target, so the identity of the
target extends over it, and restricting to the original end gives the simplex.
-/

/-! The declarations of this file that the development uses are in the modules `HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.*`, one declaration per module. -/
