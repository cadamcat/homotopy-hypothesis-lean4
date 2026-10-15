import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Topology.CarrierHomotopy.CarrierHomotopy
import HomotopyHypothesis.Approximation.Zeeman.ExteriorIteration
import HomotopyHypothesis.Approximation.Zeeman.RealizationTopology
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.SubdivisionIteration
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Coordinate mesh and exterior star refinement

The power mesh bound becomes a distance bound in the finite original-vertex
coordinate space. These distances eventually fall below every positive
radius. Compactness and the coordinate embedding then give open-cover
refinement for the closed stars of vertices in the induced exterior.
-/

universe u v

open CategoryTheory Opposite Convexity Filter Topology

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The uniform dimension factor is nonnegative and strictly less than one. -/
theorem dimensionContraction_nonneg_lt_one (D : ℕ) :
    0 ≤ (D : ℝ) / ((D : ℝ) + 1) ∧ (D : ℝ) / ((D : ℝ) + 1) < 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg D) (by positivity)
  · apply (div_lt_iff₀ (by positivity)).mpr
    linarith

/-- Powers of the dimension factor tend to zero, including the zero-dimensional case. -/
theorem dimensionContraction_pow_tendsto (D : ℕ) :
    Tendsto (fun r : ℕ => ((D : ℝ) / ((D : ℝ) + 1)) ^ r) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one
    (dimensionContraction_nonneg_lt_one D).1 (dimensionContraction_nonneg_lt_one D).2

/-- After sufficiently many iterations, every subsequent factor is below a positive radius. -/
theorem dimensionContraction_pow_eventually_lt (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ r, R ≤ r → ((D : ℝ) / ((D : ℝ) + 1)) ^ r < ε := by
  exact Filter.eventually_atTop.mp
    ((dimensionContraction_pow_tendsto D).eventually (Iio_mem_nhds hε))

/-- The original-coordinate distance between two exterior simplex points has the power bound. -/
theorem iteratedInducedSubdivision_coordinate_dist {K : SemiSSet.{u}}
    [Fintype (K.obj (op (Henry.SemiSimplexCategory.mk 0)))]
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L A : Subfunctor K)
    (hAL : A ⊓ L = ⊥) (D : ℕ)
    (hD : ∀ n, D < n → IsEmpty (K.obj (op (Henry.SemiSimplexCategory.mk n))))
    (r n : ℕ) (q : (derivedSubdivisionIterate hK hKs L r).Y'.obj
      (op (Henry.SemiSimplexCategory.mk n)))
    (hq : ∃ i, vertex q i ∈ (iteratedInducedSubdivision hK hKs L A r).obj
      (op (Henry.SemiSimplexCategory.mk 0)))
    (x y : StdSimplex ℝ (Fin (n + 1))) :
    dist (Topology.CarrierHomotopy.coordEmb K ((derivedSubdivisionIterate hK hKs L r).h.hom.hom
      ((simplexChar (uliftYonedaEquiv.symm q)).hom (ULift.up x))))
      (Topology.CarrierHomotopy.coordEmb K ((derivedSubdivisionIterate hK hKs L r).h.hom.hom
        ((simplexChar (uliftYonedaEquiv.symm q)).hom (ULift.up y)))) ≤
          ((D : ℝ) / ((D : ℝ) + 1)) ^ r := by
  apply (dist_pi_le_iff (pow_nonneg (dimensionContraction_nonneg_lt_one D).1 r)).mpr
  intro w
  rw [Real.dist_eq]
  exact iteratedInducedSubdivision_vertexCoordinate_mesh hK hKs L A hAL D hD w r n q hq x y

/-- The exterior coordinate mesh eventually falls below every positive radius. -/
theorem exists_exterior_coordinate_mesh_lt {K : SemiSSet.{u}}
    [Fintype (K.obj (op (Henry.SemiSimplexCategory.mk 0)))]
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L A : Subfunctor K)
    (hAL : A ⊓ L = ⊥) (D : ℕ)
    (hD : ∀ n, D < n → IsEmpty (K.obj (op (Henry.SemiSimplexCategory.mk n))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ r, R ≤ r → ∀ n,
      ∀ q : (derivedSubdivisionIterate hK hKs L r).Y'.obj (op (Henry.SemiSimplexCategory.mk n)),
      (∃ i, vertex q i ∈ (iteratedInducedSubdivision hK hKs L A r).obj
        (op (Henry.SemiSimplexCategory.mk 0))) →
      ∀ x y : StdSimplex ℝ (Fin (n + 1)),
        dist (Topology.CarrierHomotopy.coordEmb K ((derivedSubdivisionIterate hK hKs L r).h.hom.hom
          ((simplexChar (uliftYonedaEquiv.symm q)).hom (ULift.up x))))
          (Topology.CarrierHomotopy.coordEmb K ((derivedSubdivisionIterate hK hKs L r).h.hom.hom
            ((simplexChar (uliftYonedaEquiv.symm q)).hom (ULift.up y)))) < ε := by
  obtain ⟨R, hR⟩ := dimensionContraction_pow_eventually_lt D ε hε
  exact ⟨R, fun r hr n q hq x y =>
    (iteratedInducedSubdivision_coordinate_dist hK hKs L A hAL D hD r n q hq x y).trans_lt
      (hR r hr)⟩

/-- Every open cover has a uniform coordinate radius on the compact realization. -/
theorem coordinate_openCover_radius {K : SemiSSet.{u}}
    [Fintype (K.obj (op (Henry.SemiSimplexCategory.mk 0)))]
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) {I : Type v}
    (U : I → Set (realization.obj K)) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ z : realization.obj K, ∃ i, z ∈ U i) :
    ∃ ε > 0, ∀ z : realization.obj K, ∃ i, ∀ w : realization.obj K,
      dist (Topology.CarrierHomotopy.coordEmb K w) (Topology.CarrierHomotopy.coordEmb K z) < ε → w ∈ U i := by
  classical
  let E := Topology.CarrierHomotopy.coordEmb K
  have hE := Topology.CarrierHomotopy.isEmbedding_coordEmb hK hKs
  have : CompactSpace (realization.obj K) := compactSpace_realization_of_isFinite hK
  have hc : IsCompact (Set.range E) := isCompact_range hE.continuous
  choose V hVo hVe using fun i => hE.isInducing.isOpen_iff.mp (hU i)
  have hcov : Set.range E ⊆ ⋃ i, V i := by
    rintro y ⟨z, rfl⟩
    obtain ⟨i, hi⟩ := hcover z
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    have hz : z ∈ E ⁻¹' V i := by rw [hVe i]; exact hi
    exact hz
  obtain ⟨ε, hε, hball⟩ := lebesgue_number_lemma_of_metric hc hVo hcov
  refine ⟨ε, hε, ?_⟩
  intro z
  obtain ⟨i, hi⟩ := hball (E z) ⟨z, rfl⟩
  refine ⟨i, ?_⟩
  intro w hw
  have hmem : w ∈ E ⁻¹' V i := hi hw
  rw [hVe i] at hmem
  exact hmem

/-- Closed stars of induced exterior vertices eventually refine any original open cover. -/
theorem exists_exterior_closedStar_cover_refinement {K : SemiSSet.{u}}
    [Fintype (K.obj (op (Henry.SemiSimplexCategory.mk 0)))]
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L A : Subfunctor K)
    (hAL : A ⊓ L = ⊥) (D : ℕ)
    (hD : ∀ n, D < n → IsEmpty (K.obj (op (Henry.SemiSimplexCategory.mk n))))
    {I : Type v} (U : I → Set (realization.obj K)) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ z : realization.obj K, ∃ i, z ∈ U i) :
    ∃ R : ℕ, ∀ r, R ≤ r →
      ∀ w : (derivedSubdivisionIterate hK hKs L r).Y'.obj (op (Henry.SemiSimplexCategory.mk 0)),
      w ∈ (iteratedInducedSubdivision hK hKs L A r).obj (op (Henry.SemiSimplexCategory.mk 0)) →
      ∃ i, ∀ n, ∀ q : (derivedSubdivisionIterate hK hKs L r).Y'.obj
        (op (Henry.SemiSimplexCategory.mk n)), ∀ j : Fin (n + 1), vertex q j = w →
        ∀ t : StdSimplex ℝ (Fin (n + 1)),
          (derivedSubdivisionIterate hK hKs L r).h.hom.hom
            ((simplexChar (uliftYonedaEquiv.symm q)).hom (ULift.up t)) ∈ U i := by
  obtain ⟨ε, hε, hrad⟩ := coordinate_openCover_radius hK hKs U hU hcover
  obtain ⟨R, hR⟩ := exists_exterior_coordinate_mesh_lt hK hKs L A hAL D hD ε hε
  refine ⟨R, ?_⟩
  intro r hr w hw
  let S := derivedSubdivisionIterate hK hKs L r
  let z := S.h.hom.hom ((simplexChar (uliftYonedaEquiv.symm w)).hom (simplexVertex (n := 0) 0))
  obtain ⟨i, hi⟩ := hrad z
  refine ⟨i, ?_⟩
  intro n q j hj t
  have hq : ∃ k, vertex q k ∈ (iteratedInducedSubdivision hK hKs L A r).obj
      (op (Henry.SemiSimplexCategory.mk 0)) := ⟨j, by rw [hj]; exact hw⟩
  have hd := hR r hr n q hq t (StdSimplex.single j)
  have hcenter : S.h.hom.hom ((simplexChar (uliftYonedaEquiv.symm q)).hom
      (ULift.up (StdSimplex.single j))) = z := by
    simpa only [hj, simplexVertex, z] using congrArg S.h.hom.hom (simplexChar_vertex q j).symm
  change (derivedSubdivisionIterate hK hKs L r).h.hom.hom
    ((simplexChar (uliftYonedaEquiv.symm q)).hom (ULift.up (StdSimplex.single j))) = z at hcenter
  have he := congrArg (fun a : realization.obj K =>
    dist (Topology.CarrierHomotopy.coordEmb K ((derivedSubdivisionIterate hK hKs L r).h.hom.hom
      ((simplexChar (uliftYonedaEquiv.symm q)).hom (ULift.up t))))
        (Topology.CarrierHomotopy.coordEmb K a)) hcenter
  exact hi _ (lt_of_eq_of_lt he.symm hd)

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.dimensionContraction_pow_tendsto
#print axioms HomotopyHypothesis.Approximation.Zeeman.coordinate_openCover_radius
#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_exterior_closedStar_cover_refinement
