import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.CollarPreimage
import HomotopyHypothesis.Approximation.Zeeman.DistributionInjectivity
import HomotopyHypothesis.Approximation.Zeeman.Faces
import HomotopyHypothesis.Approximation.Zeeman.InducedSubdivision
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.LocalAffine
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeDistributions
import HomotopyHypothesis.Approximation.Zeeman.RelativeHomeomorphism
import HomotopyHypothesis.Approximation.Zeeman.RelativeRealization
import HomotopyHypothesis.Approximation.Zeeman.RelativeSupports
import HomotopyHypothesis.Approximation.Zeeman.RetainedRealization
import HomotopyHypothesis.Approximation.Zeeman.SimplexSupport
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Realization of an induced subdivision

A representative with nonzero barycentric weights belongs to a realized
subcomplex exactly when its simplex belongs to that subcomplex. Relative
derived representatives with nonzero weights likewise have nonzero weights
in their least original carrier. It follows that the induced subdivision
realizes to the preimage of the original subcomplex.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A nonzero simplex representative in a realized subcomplex has its simplex in that subcomplex. -/
theorem simplex_mem_of_nonzero_point_mem_realization {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (A : Subfunctor K) {n : ℕ}
    (a : K.obj (op (Henry.SemiSimplexCategory.mk n))) (p : StdSimplex ℝ (Fin (n + 1)))
    (hp : ∀ i, p.weights i ≠ 0)
    (hz : (simplexChar (uliftYonedaEquiv.symm a)).hom (ULift.up p) ∈
      Set.range (realization.map A.ι).hom) : a ∈ A.obj (op (Henry.SemiSimplexCategory.mk n)) := by
  obtain ⟨w, hw⟩ := hz
  obtain ⟨m, x, q, hq, rfl⟩ := exists_simplexChar_nonzero_rep w
  have hinc := congrArg (fun e => e.hom (ULift.up q)) (simplexChar_postcomp x A.ι)
  have hdist := congrArg (vertexDistributionMap K).hom (hinc.symm.trans hw)
  rw [vertexDistributionMap_simplex_apply, vertexDistributionMap_simplex_apply] at hdist
  change StdSimplex.map (vertex x.val) q = StdSimplex.map (vertex a) p at hdist
  have hsub : Set.range (vertex a) ⊆ Set.range (vertex x.val) := by
    rintro v ⟨i, rfl⟩
    apply (map_weights_ne_zero_iff (vertex x.val) (vertex_injective hK x.val) q hq _).mp
    rw [hdist]
    exact (map_weights_ne_zero_iff (vertex a) (vertex_injective hK a) p hp _).mpr ⟨i, rfl⟩
  obtain ⟨θ, hθ⟩ := exists_faceMap_of_vertex_range_subset hK a x.val hsub
  exact hθ ▸ A.map θ.op x.property

/-- The least-carrier coordinates of a nonzero derived representative are nonzero. -/
theorem relativeLocalAffineMap_weights_ne_zero {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (p : StdSimplex ℝ (Fin (n + 1))) (hp : ∀ i, p.weights i ≠ 0)
    (i : Fin ((leastRelativeCarrier hK a).1 + 1)) :
    (relativeLocalAffineMap hK a p).weights i ≠ 0 := by
  let s := leastRelativeCarrier hK a
  have he := DFunLike.congr_fun (relativeAffineMapInCarrier_distribution a s
    (leastRelativeCarrier_spec hK a).1) p
  change StdSimplex.map (vertex s.2) (relativeLocalAffineMap hK a p) =
    relativeDistributionAffineMap a p at he
  have hn := (relativeDistribution_weights_ne_zero_iff_carrier hK a p hp (vertex s.2 i)).mpr
    ⟨i, rfl⟩
  have hv := congrArg (fun q : VertexDistributions K => q.weights (vertex s.2 i)) he
  simp only [StdSimplex.weights_map,
    Finsupp.mapDomain_apply_of_injective (vertex_injective hK s.2)] at hv
  intro hz
  exact hn (hv.symm.trans hz)

/-- The induced subdivision realizes to the preimage of its original subcomplex. -/
theorem inducedRelativeSubdivision_range_eq_preimage {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L A : Subfunctor K) :
    Set.range (realization.map (inducedRelativeSubdivision hK L A).ι).hom =
      (relativeRealizationMap hK L).hom ⁻¹' Set.range (realization.map A.ι).hom := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨n, x, p, _, rfl⟩ := exists_simplexChar_nonzero_rep w
    have hinc := congrArg (fun e => e.hom (ULift.up p))
      (simplexChar_postcomp x (inducedRelativeSubdivision hK L A).ι)
    change (realization.map (inducedRelativeSubdivision hK L A).ι).hom
        ((simplexChar (uliftYonedaEquiv.symm x)).hom (ULift.up p)) =
      (simplexChar (uliftYonedaEquiv.symm x.val)).hom (ULift.up p) at hinc
    change (relativeRealizationMap hK L).hom _ ∈ Set.range (realization.map A.ι).hom
    rw [hinc]
    have hc := congrArg (fun e => e.hom (ULift.up p))
      (relativeRealizationMap_simplex hK x.val)
    change (relativeRealizationMap hK L).hom
        ((simplexChar (uliftYonedaEquiv.symm x.val)).hom (ULift.up p)) =
      (simplexChar (uliftYonedaEquiv.symm (leastRelativeCarrier hK x.val).2)).hom
        ((relativeLocalTopMap hK x.val).hom (ULift.up p)) at hc
    rw [hc]
    exact simplexChar_mem_range_realization A (leastRelativeCarrier hK x.val).2 x.property
      ((relativeLocalTopMap hK x.val).hom (ULift.up p))
  · intro hz
    obtain ⟨n, a, p, hp, rfl⟩ := exists_simplexChar_nonzero_rep z
    change (relativeRealizationMap hK L).hom
      ((simplexChar (uliftYonedaEquiv.symm a)).hom (ULift.up p)) ∈
        Set.range (realization.map A.ι).hom at hz
    have hc := congrArg (fun e => e.hom (ULift.up p)) (relativeRealizationMap_simplex hK a)
    have hza : (simplexChar (uliftYonedaEquiv.symm (leastRelativeCarrier hK a).2)).hom
        (ULift.up (relativeLocalAffineMap hK a p)) ∈ Set.range (realization.map A.ι).hom :=
      hc ▸ hz
    have ha : a ∈ (inducedRelativeSubdivision hK L A).obj
        (op (Henry.SemiSimplexCategory.mk n)) :=
      simplex_mem_of_nonzero_point_mem_realization hK A (leastRelativeCarrier hK a).2
        (relativeLocalAffineMap hK a p) (relativeLocalAffineMap_weights_ne_zero hK a p hp) hza
    exact simplexChar_mem_range_realization (inducedRelativeSubdivision hK L A) a ha (ULift.up p)

/-- The subdivision identification maps the induced realization onto the original subcomplex. -/
theorem inducedRelativeSubdivision_image_realization {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L A : Subfunctor K) :
    (relativeRealizationIso hK hKs L).hom.hom ''
        Set.range (realization.map (inducedRelativeSubdivision hKs L A).ι).hom =
      Set.range (realization.map A.ι).hom := by
  apply Set.Subset.antisymm
  · rintro z ⟨y, hy, rfl⟩
    exact (Set.ext_iff.mp (inducedRelativeSubdivision_range_eq_preimage hKs L A) y).mp hy
  · intro z hz
    obtain ⟨y, rfl⟩ := relativeRealizationMap_surjective hKs L z
    exact ⟨y, (Set.ext_iff.mp (inducedRelativeSubdivision_range_eq_preimage hKs L A) y).mpr hz, rfl⟩

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.simplex_mem_of_nonzero_point_mem_realization
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeLocalAffineMap_weights_ne_zero
#print axioms HomotopyHypothesis.Approximation.Zeeman.inducedRelativeSubdivision_range_eq_preimage
#print axioms HomotopyHypothesis.Approximation.Zeeman.inducedRelativeSubdivision_image_realization
