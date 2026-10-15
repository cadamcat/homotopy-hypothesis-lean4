import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.DistributionInjectivity
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.LocalAffine
import HomotopyHypothesis.Approximation.Zeeman.Positions
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeRealization
import HomotopyHypothesis.Approximation.Zeeman.TriangularAffine
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Original vertex distributions of relative derived simplices

A relative subdivision vertex represents the uniform distribution on the
vertices of its source face. Extending these distributions affinely computes
the relative realization map in original vertex coordinates, independently
of the original carrier used for the computation.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The distribution on original vertices represented by a relative subdivision vertex. -/
noncomputable def relativeVertexDistribution {K : SemiSSet.{u}} {L : Subfunctor K}
    (v : RelativeVertex K L) : VertexDistributions K :=
  StdSimplex.map (vertex v.sourceSimplex.2)
    (StdSimplex.barycenter (K := ℝ) (M := Fin (v.sourceSimplex.1 + 1)))

/-- A relative vertex has the same original distribution in any carrier. -/
theorem relativeVertexPosition_distribution {K : SemiSSet.{u}} {L : Subfunctor K} {m : ℕ}
    (y : K.obj (op (Henry.SemiSimplexCategory.mk m))) (v : RelativeVertex K L)
    (hv : RelativeVertex.CarriedBy v y) :
    StdSimplex.map (vertex y) (relativeVertexPosition y v hv) =
      relativeVertexDistribution v := by
  let b := StdSimplex.barycenter (K := ℝ) (M := Fin (v.sourceSimplex.1 + 1))
  change StdSimplex.map (vertex y)
    (StdSimplex.map (carriedFaceMap y v hv).hom.toOrderHom b) =
      StdSimplex.map (vertex v.sourceSimplex.2) b
  refine (StdSimplex.map_comp b (carriedFaceMap y v hv).hom.toOrderHom
    (vertex y)).symm.trans (congrArg (fun f => StdSimplex.map f b) ?_)
  funext i
  exact (vertex_map (carriedFaceMap y v hv) y i).symm.trans
    (congrArg (fun z => vertex z i) (carriedFaceMap_spec y v hv))

/-- Affinely mix the original distributions of a relative derived tuple. -/
noncomputable def relativeDistributionAffineMap {K : SemiSSet.{u}} {L : Subfunctor K}
    {n : ℕ} (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) (VertexDistributions K) :=
  StdSimplex.affineMapMk (R := ℝ) (fun i => relativeVertexDistribution (a.val i))

/-- Computing the affine mixture in any original carrier gives the same distribution. -/
theorem relativeAffineMapInCarrier_distribution {K : SemiSSet.{u}} {L : Subfunctor K}
    {n : ℕ} (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (s : Simplex K) (hs : ∀ i, RelativeVertex.CarriedBy (a.val i) s.2) :
    (StdSimplex.affineMap (R := ℝ) (vertex s.2)).comp
      (relativeAffineMapInCarrier a s hs) = relativeDistributionAffineMap a := by
  apply StdSimplex.affineMap_ext
  intro i
  simp only [ConvexSpace.AffineMap.comp_apply, Function.comp_apply, StdSimplex.coe_affineMap,
    relativeAffineMapInCarrier, relativeDistributionAffineMap, StdSimplex.affineMapMk_single]
  exact relativeVertexPosition_distribution s.2 (a.val i) (hs i)

/-- The relative realization map computes the affine mixture of original vertex distributions. -/
theorem relativeRealizationMap_distribution_simplex_apply {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (t : StdSimplex ℝ (Fin (n + 1))) :
    (vertexDistributionMap K).hom ((relativeRealizationMap hK L).hom
      ((simplexChar (uliftYonedaEquiv.symm a)).hom (ULift.up t))) =
        relativeDistributionAffineMap a t := by
  let s := leastRelativeCarrier hK a
  have hlocal := congrArg (fun f => f.hom (ULift.up t)) (relativeRealizationMap_simplex hK a)
  exact (congrArg (vertexDistributionMap K).hom hlocal).trans
    ((vertexDistributionMap_simplex_apply s.2 (relativeLocalAffineMap hK a t)).trans
      (DFunLike.congr_fun (relativeAffineMapInCarrier_distribution a s
        (leastRelativeCarrier_spec hK a).1) t))

/-- Original vertex weights are weighted sums of the source-face barycentric weights. -/
theorem relativeRealizationMap_distribution_weights {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (t : StdSimplex ℝ (Fin (n + 1)))
    (w : K.obj (op (Henry.SemiSimplexCategory.mk 0))) :
    ((vertexDistributionMap K).hom ((relativeRealizationMap hK L).hom
      ((simplexChar (uliftYonedaEquiv.symm a)).hom (ULift.up t)))).weights w =
        ∑ i, t.weights i * (relativeVertexDistribution (a.val i)).weights w :=
  (congrArg (fun r => r.weights w)
    (relativeRealizationMap_distribution_simplex_apply hK a t)).trans
      (affineMapMk_weights_apply (fun i => relativeVertexDistribution (a.val i)) t w)

/-- The original support of a subdivision vertex is its source face's vertex support. -/
theorem relativeVertexDistribution_weights_ne_zero_iff {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} (v : RelativeVertex K L)
    (w : K.obj (op (Henry.SemiSimplexCategory.mk 0))) :
    (relativeVertexDistribution v).weights w ≠ 0 ↔
      w ∈ Set.range (vertex v.sourceSimplex.2) := by
  apply map_weights_ne_zero_iff _ (vertex_injective hK v.sourceSimplex.2)
  intro i
  rw [StdSimplex.weights_barycenter_apply, Fintype.card_fin]
  exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero v.sourceSimplex.1))

/-- A retained vertex represents the point distribution on its original vertex. -/
theorem relativeVertexDistribution_retained {K : SemiSSet.{u}} {L : Subfunctor K}
    (v : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk 0))) :
    relativeVertexDistribution (Sum.inl v : RelativeVertex K L) = StdSimplex.single v.val := by
  change StdSimplex.map (vertex v.val) (StdSimplex.barycenter (K := ℝ) (M := Fin 1)) = _
  rw [StdSimplex.barycenter_fin_one, StdSimplex.map_single, vertex_zero]

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeVertexPosition_distribution
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeRealizationMap_distribution_weights
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeVertexDistribution_weights_ne_zero_iff
