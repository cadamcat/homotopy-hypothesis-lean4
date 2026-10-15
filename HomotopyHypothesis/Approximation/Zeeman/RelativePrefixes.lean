import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.ApexWeights
import HomotopyHypothesis.Approximation.Zeeman.LocalEmbedding
import HomotopyHypothesis.Approximation.Zeeman.RelativeCones
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeDistributions
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
/-!
# Normalized prefixes of relative derived points

Removing the last coordinate of a simplex point and dividing the remaining
coordinates by their total mass gives its normalized prefix. Equal exterior
flag distributions have equal apex weights, so cancellation of their common
apex contributions identifies their normalized prefix distributions.
-/

universe u v

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A nonzero point of a positive-dimensional simplex assigns less than one to its last vertex. -/
theorem last_weight_lt_one_of_nonzero {n : ℕ} (t : StdSimplex ℝ (Fin (n + 2)))
    (ht : ∀ i, t.weights i ≠ 0) : t.weights (Fin.last (n + 1)) < 1 := by
  have hsum := t.total_of_fintype
  rw [Fin.sum_univ_castSucc] at hsum
  have hle : t.weights ((0 : Fin (n + 1)).castSucc) ≤ ∑ i : Fin (n + 1),
      t.weights i.castSucc :=
    Finset.single_le_sum (fun (i : Fin (n + 1)) _ => t.weights_nonneg i.castSucc)
      (Finset.mem_univ _)
  have hpos : 0 < t.weights ((0 : Fin (n + 1)).castSucc) :=
    lt_of_le_of_ne (t.weights_nonneg _) (Ne.symm (ht _))
  linarith

/-- Normalize the prefix of a point whose last coordinate is less than one. -/
noncomputable def normalizedPrefix {n : ℕ} (t : StdSimplex ℝ (Fin (n + 2)))
    (hc : t.weights (Fin.last (n + 1)) < 1) : StdSimplex ℝ (Fin (n + 1)) where
  weights := Finsupp.equivFunOnFinite.symm
    (fun i => t.weights i.castSucc / (1 - t.weights (Fin.last (n + 1))))
  nonneg := by
    intro i
    change 0 ≤ t.weights i.castSucc / (1 - t.weights (Fin.last (n + 1)))
    exact div_nonneg (t.weights_nonneg _) (sub_pos.mpr hc).le
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑ i : Fin (n + 1),
      t.weights i.castSucc / (1 - t.weights (Fin.last (n + 1)))) = 1
    rw [← Finset.sum_div]
    have hsum := t.total_of_fintype
    rw [Fin.sum_univ_castSucc] at hsum
    have he : (∑ i : Fin (n + 1), t.weights i.castSucc) =
        1 - t.weights (Fin.last (n + 1)) := by linarith
    rw [he, div_self (ne_of_gt (sub_pos.mpr hc))]

/-- The normalized prefix has the specified quotient coordinates. -/
theorem normalizedPrefix_weights {n : ℕ} (t : StdSimplex ℝ (Fin (n + 2)))
    (hc : t.weights (Fin.last (n + 1)) < 1) (i : Fin (n + 1)) :
    (normalizedPrefix t hc).weights i =
      t.weights i.castSucc / (1 - t.weights (Fin.last (n + 1))) := rfl

/-- Nonzero input coordinates remain nonzero in the normalized prefix. -/
theorem normalizedPrefix_weights_ne_zero {n : ℕ} (t : StdSimplex ℝ (Fin (n + 2)))
    (hc : t.weights (Fin.last (n + 1)) < 1) (ht : ∀ i, t.weights i ≠ 0) :
    ∀ i, (normalizedPrefix t hc).weights i ≠ 0 := by
  intro i
  exact div_ne_zero (ht i.castSucc) (ne_of_gt (sub_pos.mpr hc))

/-- A point is the convex combination of its last vertex and its normalized prefix. -/
theorem normalizedPrefix_decomposition {n : ℕ} (t : StdSimplex ℝ (Fin (n + 2)))
    (hc : t.weights (Fin.last (n + 1)) < 1) :
    t = convexCombPair (t.weights (Fin.last (n + 1)))
      (1 - t.weights (Fin.last (n + 1))) (t.weights_nonneg _)
      (sub_pos.mpr hc).le (by ring) (StdSimplex.single (Fin.last (n + 1)))
      (StdSimplex.map Fin.castSucc (normalizedPrefix t hc)) := by
  apply StdSimplex.ext
  apply Finsupp.ext
  intro i
  rw [StdSimplex.weights_convexCombPair]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  induction i using Fin.lastCases with
  | last =>
    have hn : Fin.last (n + 1) ∉ Set.range (Fin.castSucc : Fin (n + 1) → Fin (n + 2)) := by
      rintro ⟨j, hj⟩
      exact (Fin.castSucc_ne_last j) hj
    rw [StdSimplex.weights_map, Finsupp.mapDomain_of_notMem_range _ _ hn]
    simp
  | cast i =>
    rw [StdSimplex.weights_map,
      Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective (n + 1))]
    simp only [StdSimplex.weights_single, Finsupp.single_eq_of_ne (Fin.castSucc_ne_last i),
      mul_zero, zero_add, normalizedPrefix_weights]
    exact (mul_div_cancel₀ _ (ne_of_gt (sub_pos.mpr hc))).symm

/-- With positive mass on the second point, a convex pair of distributions cancels on the right. -/
theorem convexCombPair_right_cancel {M : Type v} (c : ℝ) (hc : 0 ≤ c) (hc' : c < 1)
    (x y z : StdSimplex ℝ M)
    (h : convexCombPair c (1 - c) hc (sub_pos.mpr hc').le (by ring) x y =
      convexCombPair c (1 - c) hc (sub_pos.mpr hc').le (by ring) x z) : y = z := by
  apply StdSimplex.ext
  apply Finsupp.ext
  intro w
  have he := congrArg (fun q : StdSimplex ℝ M => q.weights w) h
  simp only [StdSimplex.weights_convexCombPair, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul] at he
  exact (mul_right_inj' (ne_of_gt (sub_pos.mpr hc'))).mp (add_left_cancel he)

/-- The prefix face of a relative derived simplex. -/
def relativePrefix {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk (n + 1)))) :
    (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)) :=
  (relativeDerived K L).map (initialFace (Nat.le_succ n)).op a

/-- Splitting simplex weights splits the original distribution into its apex and prefix. -/
theorem relativeDistribution_prefix_split {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk (n + 1))))
    (t : StdSimplex ℝ (Fin (n + 2))) (hc : t.weights (Fin.last (n + 1)) < 1) :
    relativeDistributionAffineMap a t =
      convexCombPair (t.weights (Fin.last (n + 1)))
        (1 - t.weights (Fin.last (n + 1))) (t.weights_nonneg _) (sub_pos.mpr hc).le (by ring)
        (relativeVertexDistribution (a.val (Fin.last (n + 1))))
        (relativeDistributionAffineMap (relativePrefix a) (normalizedPrefix t hc)) := by
  conv_lhs => rw [normalizedPrefix_decomposition t hc]
  rw [(relativeDistributionAffineMap a).isAffineMap.map_convexCombPair]
  have hbase := DFunLike.congr_fun
    (relativeDistributionAffineMap_face a (initialFace (Nat.le_succ n)))
      (normalizedPrefix t hc)
  change relativeDistributionAffineMap a (StdSimplex.map Fin.castSucc (normalizedPrefix t hc)) =
    relativeDistributionAffineMap (relativePrefix a) (normalizedPrefix t hc) at hbase
  rw [hbase]
  simp only [relativeDistributionAffineMap, StdSimplex.affineMapMk_single]

/-- Equal exterior distributions have equal distributions on their normalized prefix faces. -/
theorem relativePrefix_distribution_eq {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n m : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk (n + 1))))
    (b : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk (m + 1))))
    (t : StdSimplex ℝ (Fin (n + 2))) (p : StdSimplex ℝ (Fin (m + 2)))
    (ht : ∀ i, t.weights i ≠ 0) (hp : ∀ i, p.weights i ≠ 0)
    (s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))})
    (ha : a.val (Fin.last (n + 1)) = .inr s)
    (hb : b.val (Fin.last (m + 1)) = .inr s)
    (h : relativeDistributionAffineMap a t = relativeDistributionAffineMap b p) :
    relativeDistributionAffineMap (relativePrefix a)
      (normalizedPrefix t (last_weight_lt_one_of_nonzero t ht)) =
        relativeDistributionAffineMap (relativePrefix b)
          (normalizedPrefix p (last_weight_lt_one_of_nonzero p hp)) := by
  have hct := last_weight_lt_one_of_nonzero t ht
  have hcp := last_weight_lt_one_of_nonzero p hp
  have hc := apex_weight_eq_of_distribution_eq hK a b t p s ha hb h
  rw [relativeDistribution_prefix_split a t hct, relativeDistribution_prefix_split b p hcp,
    ha, hb] at h
  apply StdSimplex.ext
  apply Finsupp.ext
  intro w
  have he := congrArg (fun q : VertexDistributions K => q.weights w) h
  simp only [StdSimplex.weights_convexCombPair, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, hc] at he
  exact (mul_right_inj' (ne_of_gt (sub_pos.mpr hcp))).mp (add_left_cancel he)

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.normalizedPrefix_decomposition
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativePrefix_distribution_eq
