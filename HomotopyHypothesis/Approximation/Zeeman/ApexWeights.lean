import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.Faces
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.LocalEmbedding
import HomotopyHypothesis.Approximation.Zeeman.Positions
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeDistributions
import HomotopyHypothesis.Approximation.Zeeman.RelativeSupports
import HomotopyHypothesis.Approximation.Zeeman.RetainedRealization
import HomotopyHypothesis.Approximation.Zeeman.TriangularAffine
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Recovering the exterior apex from original coordinates

The final exterior face is the least original carrier. Its barycentre
contributes a uniform amount to each carrier coordinate, and some carrier
vertex lies outside every earlier source. The minimum carrier coordinate
therefore recovers the coefficient of the final exterior vertex.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A retained tuple has its original simplex as least carrier. -/
theorem leastRelativeCarrier_retained {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    (L : Subfunctor K) {n : ℕ}
    (x : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n))) :
    leastRelativeCarrier hK
      ((relativeDerivedInclusion hK L).app (op (Henry.SemiSimplexCategory.mk n)) x) =
        ⟨n, x.val⟩ := by
  let a := (relativeDerivedInclusion hK L).app (op (Henry.SemiSimplexCategory.mk n)) x
  apply simplex_eq_of_vertex_range_eq_sigma hK
  apply Set.Subset.antisymm
  · exact (vertex_range_subset_iff_existsUnique_faceMap hK
      (leastRelativeCarrier hK a).2 x.val).mpr
        ((leastRelativeCarrier_spec hK a).2 ⟨n, x.val⟩ (retainedTuple_carried hK L x))
  · rintro w ⟨i, hi⟩
    apply (relativeTuple_source_support_iff_carrier hK a w).mp
    refine ⟨i, 0, ?_⟩
    change vertex (vertex x i).val (0 : Fin 1) = w
    exact (vertex_zero (vertex x i).val).trans hi

/-- The final exterior face of an admissible tuple is its least original carrier. -/
theorem leastRelativeCarrier_eq_of_last_exterior {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))})
    (hlast : a.val (Fin.last n) = .inr s) : leastRelativeCarrier hK a = s.val := by
  apply simplex_eq_of_vertex_range_eq_sigma hK
  apply Set.Subset.antisymm
  · exact (vertex_range_subset_iff_existsUnique_faceMap hK
      (leastRelativeCarrier hK a).2 s.val.2).mpr
        ((leastRelativeCarrier_spec hK a).2 s.val
          (relativeTuple_carried_of_last_exterior a s hlast))
  · intro w hw
    apply (relativeTuple_source_support_iff_carrier hK a w).mp
    refine ⟨Fin.last n, ?_⟩
    rw [hlast]
    exact hw

/-- An exterior barycentre has the uniform coordinate on every vertex of its source simplex. -/
theorem relativeVertexDistribution_exterior_weights {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K}
    (s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))})
    (w : K.obj (op (Henry.SemiSimplexCategory.mk 0))) (hw : w ∈ Set.range (vertex s.val.2)) :
    (relativeVertexDistribution (Sum.inr s : RelativeVertex K L)).weights w =
      ((s.val.1 + 1 : ℕ) : ℝ)⁻¹ := by
  obtain ⟨i, rfl⟩ := hw
  change (StdSimplex.map (vertex s.val.2)
    (StdSimplex.barycenter (K := ℝ) (M := Fin (s.val.1 + 1)))).weights
      (vertex s.val.2 i) = _
  rw [StdSimplex.weights_map,
    Finsupp.mapDomain_apply_of_injective (vertex_injective hK s.val.2),
    StdSimplex.weights_barycenter_apply, Fintype.card_fin]

/-- Every carrier coordinate is at least the uniform contribution of the exterior apex. -/
theorem apex_contribution_le_distribution {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (t : StdSimplex ℝ (Fin (n + 1)))
    (s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))})
    (hlast : a.val (Fin.last n) = .inr s)
    (w : K.obj (op (Henry.SemiSimplexCategory.mk 0))) (hw : w ∈ Set.range (vertex s.val.2)) :
    t.weights (Fin.last n) * ((s.val.1 + 1 : ℕ) : ℝ)⁻¹ ≤
      (relativeDistributionAffineMap a t).weights w := by
  classical
  have hle : t.weights (Fin.last n) *
      (relativeVertexDistribution (a.val (Fin.last n))).weights w ≤
        ∑ i, t.weights i * (relativeVertexDistribution (a.val i)).weights w :=
    Finset.single_le_sum (fun i _ => mul_nonneg (t.weights_nonneg i)
      ((relativeVertexDistribution (a.val i)).weights_nonneg w)) (Finset.mem_univ _)
  rw [hlast, relativeVertexDistribution_exterior_weights hK s w hw] at hle
  exact hle.trans_eq (affineMapMk_weights_apply
    (fun i => relativeVertexDistribution (a.val i)) t w).symm

/-- A new carrier vertex attains the exterior apex's uniform contribution. -/
theorem exists_distribution_eq_apex_contribution {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (t : StdSimplex ℝ (Fin (n + 1)))
    (s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))})
    (hlast : a.val (Fin.last n) = .inr s) :
    ∃ w : K.obj (op (Henry.SemiSimplexCategory.mk 0)),
      w ∈ Set.range (vertex s.val.2) ∧
        (relativeDistributionAffineMap a t).weights w =
          t.weights (Fin.last n) * ((s.val.1 + 1 : ℕ) : ℝ)⁻¹ := by
  classical
  obtain ⟨w, hw, hprev⟩ := relativeTuple_last_new_source_vertex hK a
  rw [hlast] at hw
  refine ⟨w, hw, ?_⟩
  change (StdSimplex.affineMapMk (R := ℝ)
    (fun i => relativeVertexDistribution (a.val i)) t).weights w = _
  rw [affineMapMk_weights_apply]
  have he : (∑ i, t.weights i * (relativeVertexDistribution (a.val i)).weights w) =
      t.weights (Fin.last n) *
        (relativeVertexDistribution (a.val (Fin.last n))).weights w := by
    apply Finset.sum_eq_single (Fin.last n)
    · intro i _ hi
      have hz : (relativeVertexDistribution (a.val i)).weights w = 0 := by
        by_contra hn
        exact hprev i (lt_of_le_of_ne (Fin.le_last i) hi)
          ((relativeVertexDistribution_weights_ne_zero_iff hK (a.val i) w).mp hn)
      rw [hz, mul_zero]
    · simp
  rw [he, hlast, relativeVertexDistribution_exterior_weights hK s w hw]

/-- Two equal mixtures with the same exterior apex have the same apex coefficient. -/
theorem apex_weight_eq_of_distribution_eq {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n m : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (b : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk m)))
    (t : StdSimplex ℝ (Fin (n + 1))) (p : StdSimplex ℝ (Fin (m + 1)))
    (s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))})
    (ha : a.val (Fin.last n) = .inr s) (hb : b.val (Fin.last m) = .inr s)
    (h : relativeDistributionAffineMap a t = relativeDistributionAffineMap b p) :
    t.weights (Fin.last n) = p.weights (Fin.last m) := by
  obtain ⟨w, hw, he⟩ := exists_distribution_eq_apex_contribution hK b p s hb
  have hle := apex_contribution_le_distribution hK a t s ha w hw
  rw [h, he] at hle
  obtain ⟨z, hz, he'⟩ := exists_distribution_eq_apex_contribution hK a t s ha
  have hge := apex_contribution_le_distribution hK b p s hb z hz
  rw [← h, he'] at hge
  exact mul_right_cancel₀
    (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero s.val.1))) (le_antisymm hle hge)

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.leastRelativeCarrier_eq_of_last_exterior
#print axioms HomotopyHypothesis.Approximation.Zeeman.apex_weight_eq_of_distribution_eq
