import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RetainedFull
import HomotopyHypothesis.Approximation.Zeeman.RetainedRealization
import HomotopyHypothesis.Approximation.Zeeman.SimplexSupport
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Full subcomplexes and vertex coordinates

A point belongs to the realization of a full subcomplex exactly when all
its nonzero vertex coordinates belong to that subcomplex. The union of
open vertex stars of a subcomplex is an open neighborhood of its realization.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Each original vertex coordinate is continuous on realization. -/
theorem continuous_vertexDistribution_weight (K : SemiSSet.{u})
    (v : K.obj (op (Henry.SemiSimplexCategory.mk 0))) :
    Continuous (fun z => ((vertexDistributionMap K).hom z).weights v) :=
  (StdSimplex.continuous_weights_apply ℝ v).comp (vertexDistributionMap K).hom.continuous

/-- Nonzero coordinates of a point in a subcomplex belong to that subcomplex. -/
theorem vertexDistribution_support_subset_of_mem_range {K : SemiSSet.{u}}
    (L : Subfunctor K) {z : realization.obj K}
    (hz : z ∈ Set.range (realization.map L.ι).hom)
    (v : K.obj (op (Henry.SemiSimplexCategory.mk 0)))
    (hv : ((vertexDistributionMap K).hom z).weights v ≠ 0) :
    v ∈ L.obj (op (Henry.SemiSimplexCategory.mk 0)) := by
  obtain ⟨w, rfl⟩ := hz
  obtain ⟨n, x, p, _, rfl⟩ := exists_simplexChar_nonzero_rep w
  have hinc := congrArg (fun e => e.hom (ULift.up p)) (simplexChar_postcomp x L.ι)
  change (realization.map L.ι).hom
      ((simplexChar (uliftYonedaEquiv.symm x)).hom (ULift.up p)) =
    (simplexChar (uliftYonedaEquiv.symm x.val)).hom (ULift.up p) at hinc
  rw [hinc, vertexDistributionMap_simplex_apply, StdSimplex.weights_map] at hv
  obtain ⟨i, hi⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hv
  exact hi ▸ L.map (vertexInclusion i).op x.property

/-- A full subcomplex contains a realization point supported on its vertices. -/
theorem mem_range_realization_of_vertexDistribution_support {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) (hL : IsFullSubcomplex L)
    (z : realization.obj K)
    (hz : ∀ v, ((vertexDistributionMap K).hom z).weights v ≠ 0 →
      v ∈ L.obj (op (Henry.SemiSimplexCategory.mk 0))) :
    z ∈ Set.range (realization.map L.ι).hom := by
  obtain ⟨n, x, p, hp, rfl⟩ := exists_simplexChar_nonzero_rep z
  have hx : x ∈ L.obj (op (Henry.SemiSimplexCategory.mk n)) := by
    apply hL n x
    intro i
    apply hz (vertex x i)
    rw [vertexDistributionMap_simplex_apply, StdSimplex.weights_map,
      Finsupp.mapDomain_apply_of_injective (vertex_injective hK x)]
    exact hp i
  refine ⟨(simplexChar (uliftYonedaEquiv.symm
    (⟨x, hx⟩ : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n))))).hom (ULift.up p), ?_⟩
  exact congrArg (fun e => e.hom (ULift.up p))
    (simplexChar_postcomp
      (⟨x, hx⟩ : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n))) L.ι)

/-- Membership in a full subcomplex is characterized by vertex-distribution support. -/
theorem mem_range_realization_iff_vertexDistribution_support {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) (hL : IsFullSubcomplex L)
    (z : realization.obj K) :
    z ∈ Set.range (realization.map L.ι).hom ↔
      ∀ v, ((vertexDistributionMap K).hom z).weights v ≠ 0 →
        v ∈ L.obj (op (Henry.SemiSimplexCategory.mk 0)) :=
  ⟨fun hz => vertexDistribution_support_subset_of_mem_range L hz,
    mem_range_realization_of_vertexDistribution_support hK L hL z⟩

/-- The union of the open stars of vertices of a subcomplex. -/
def subcomplexOpenStar {K : SemiSSet.{u}} (L : Subfunctor K) : Set (realization.obj K) :=
  {z | ∃ v : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk 0)),
    ((vertexDistributionMap K).hom z).weights v.val ≠ 0}

/-- A subcomplex's open star is open. -/
theorem isOpen_subcomplexOpenStar {K : SemiSSet.{u}} (L : Subfunctor K) :
    IsOpen (subcomplexOpenStar L) := by
  have hcoord (v : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk 0))) :
      IsOpen {z : realization.obj K | ((vertexDistributionMap K).hom z).weights v.val ≠ 0} :=
    isOpen_ne.preimage (continuous_vertexDistribution_weight K v.val)
  have h := isOpen_iUnion hcoord
  convert h using 1
  ext z
  simp only [subcomplexOpenStar, Set.mem_setOf_eq, Set.mem_iUnion]

/-- A subcomplex's realization is contained in its open star. -/
theorem range_realization_subset_subcomplexOpenStar {K : SemiSSet.{u}}
    (L : Subfunctor K) :
    Set.range (realization.map L.ι).hom ⊆ subcomplexOpenStar L := by
  intro z hz
  obtain ⟨v, hv⟩ := ((vertexDistributionMap K).hom z).support_weights_nonempty
  have hne := Finsupp.mem_support_iff.mp hv
  exact ⟨⟨v, vertexDistribution_support_subset_of_mem_range L hz v hne⟩, hne⟩

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.mem_range_realization_iff_vertexDistribution_support
#print axioms HomotopyHypothesis.Approximation.Zeeman.isOpen_subcomplexOpenStar
#print axioms HomotopyHypothesis.Approximation.Zeeman.range_realization_subset_subcomplexOpenStar
