import Mathlib.Geometry.Convex.ConvexSpace.Topology
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.ComplexTopologyStatement
import HomotopyHypothesis.Approximation.Zeeman.DistributionInjectivity
import HomotopyHypothesis.Approximation.Zeeman.RealizationTopology
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
/-!
# Compact Hausdorff topology of finite simplicial realizations

For finite simplicial complexes, barycentric vertex distributions embed the
realization as a closed subspace of a Hausdorff simplex of distributions.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Realization.ComplexTopology

/-- The realization of a finite simplicial complex is compact Hausdorff and embeds
as a closed subspace of its vertex-distribution simplex. -/
theorem complexRealizationTopologyStatement_proof :
    HomotopyHypothesis.Approximation.Zeeman.ComplexRealizationTopologyStatement := by
  intro K hK hS
  letI : Finite (K.obj (op (Henry.SemiSimplexCategory.mk 0))) := hK.1 0
  letI : T2Space (HomotopyHypothesis.Approximation.Zeeman.VertexDistributions K) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ
      (K.obj (op (Henry.SemiSimplexCategory.mk 0)))).t2Space
  have hcontinuous :
      Continuous (HomotopyHypothesis.Approximation.Zeeman.vertexDistributionMap K).hom :=
    (HomotopyHypothesis.Approximation.Zeeman.vertexDistributionMap K).hom.continuous
  letI : T2Space (Henry.SemiSSet.realization.obj K) :=
    T2Space.of_injective_continuous
      (HomotopyHypothesis.Approximation.Zeeman.vertexDistributionMap_injective hS) hcontinuous
  letI : CompactSpace (Henry.SemiSSet.realization.obj K) :=
    HomotopyHypothesis.Approximation.Zeeman.compactSpace_realization_of_isFinite hK
  exact ⟨inferInstance,
    hcontinuous.isClosedEmbedding
      (HomotopyHypothesis.Approximation.Zeeman.vertexDistributionMap_injective hS)⟩

example : HomotopyHypothesis.Approximation.Zeeman.ComplexRealizationTopologyStatement :=
  complexRealizationTopologyStatement_proof

#print axioms complexRealizationTopologyStatement_proof

end HomotopyHypothesis.Realization.ComplexTopology
