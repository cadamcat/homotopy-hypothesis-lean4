import HomotopyHypothesis.Approximation.Topological.KanApproximation.Part1
import HomotopyHypothesis.Approximation.Topological.KanApproximation.Part2

/-!
# Removing collapses and subdivisions in a Kan target

Proof of Rourke–Sanderson, *Δ-sets I*, Thm. 5.3 for a given simplicial approximation
(`kan_exists_of_relPrism`). The relative mapping cylinder of the simplicial map
collapses onto the Kan target, so the identity of the target extends over it; this turns the
simplicial map on the subdivision into a semi-simplicial map. The prism of the subdivision collapses
onto the subdivided end, so that map extends over the prism; its restriction to the original end is
the required map. The homotopies come from the fact that a collapse realizes to a strong deformation
retraction, so that all retractions onto the collapsed end are homotopic relative to it.
-/

/-! This file is split into the modules `HomotopyHypothesis.Approximation.Topological.KanApproximation.Part*` so that the modules of the development form an acyclic import graph. -/
