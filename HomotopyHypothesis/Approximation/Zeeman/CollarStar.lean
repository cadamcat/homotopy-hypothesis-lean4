import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.CollarMap
import HomotopyHypothesis.Approximation.Zeeman.CollarNeighborhood
import HomotopyHypothesis.Approximation.Zeeman.CollarVertices
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.SimplexSupport
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Retained vertex stars under the collar map

The collar map preserves every nonzero retained vertex coordinate. Thus
the open star of a retained vertex maps into its original open star.
-/

universe u v

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A map of probability distributions preserves nonzero weights at their images. -/
theorem stdSimplex_map_weights_ne_zero_of_ne_zero {A : Type u} {B : Type v}
    (f : A → B) (p : StdSimplex ℝ A) (i : A) (hi : p.weights i ≠ 0) :
    (StdSimplex.map f p).weights (f i) ≠ 0 := by
  classical
  rw [StdSimplex.weights_map]
  apply Finsupp.mem_support_iff.mp
  rw [Finsupp.support_mapDomain_of_nonneg p.nonneg]
  exact Finset.mem_image.mpr ⟨i, Finsupp.mem_support_iff.mpr hi, rfl⟩

/-- The collar map sends the open star of each retained vertex into its original star. -/
theorem relativeCollarMap_preserves_retained_star {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K)
    (v : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk 0)))
    (z : realization.obj (relativeDerived K L))
    (hz : ((vertexDistributionMap (relativeDerived K L)).hom z).weights
      ((relativeDerivedInclusion hK L).app (op (Henry.SemiSimplexCategory.mk 0)) v) ≠ 0) :
    ((vertexDistributionMap K).hom ((relativeCollarMap hK L).hom z)).weights v.val ≠ 0 := by
  obtain ⟨n, a, p, hp, rfl⟩ := exists_simplexChar_nonzero_rep z
  rw [vertexDistributionMap_simplex_apply, StdSimplex.weights_map] at hz
  obtain ⟨i, hi⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hz
  have hw := congrArg (fun b => b.val (0 : Fin 1)) hi
  change a.val i = Sum.inl (vertex v (0 : Fin 1)) at hw
  rw [vertex_zero] at hw
  have hv : relativeCollarVertex (a.val i) = v.val :=
    (congrArg relativeCollarVertex hw).trans (relativeCollarVertex_retained v)
  rw [relativeCollarMap_vertexDistribution_simplex, ← hv]
  exact stdSimplex_map_weights_ne_zero_of_ne_zero _ p i (hp i)

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollarMap_preserves_retained_star
