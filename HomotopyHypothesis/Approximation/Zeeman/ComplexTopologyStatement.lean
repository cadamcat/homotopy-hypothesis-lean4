import Mathlib.Topology.Separation.Hausdorff
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.DistributionInjectivity
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
/-!
# The compact Hausdorff realization statement

For a finite simplicial complex, the vertex-distribution map identifies
its realization with a closed subspace of the space of vertex distributions.
-/

universe u

open CategoryTheory Topology

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The topological embedding statement for finite simplicial complexes. -/
def ComplexRealizationTopologyStatement : Prop :=
  ∀ (K : SemiSSet.{u}), K.IsFinite → K.IsSimplicialComplex →
    T2Space (realization.obj K) ∧ IsClosedEmbedding (vertexDistributionMap K).hom

end HomotopyHypothesis.Approximation.Zeeman
