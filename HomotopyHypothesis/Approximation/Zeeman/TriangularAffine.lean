import Mathlib.Data.Finset.Max
import HomotopyHypothesis.Approximation.Zeeman.LocalAffine
/-!
# Injectivity from triangular vertex coordinates

An affine map of a standard simplex is injective if every vertex has a
nonzero coordinate that vanishes on all preceding vertices. Evaluating at
the coordinate of the greatest differing input weight proves injectivity.
-/

universe u

open Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

/-- The coordinates of an affine simplex map are the weighted sums of its vertex coordinates. -/
theorem affineMapMk_weights_apply {n : ℕ} {M : Type u}
    (p : Fin (n + 1) → StdSimplex ℝ M) (x : StdSimplex ℝ (Fin (n + 1))) (q : M) :
    (StdSimplex.affineMapMk (R := ℝ) p x).weights q =
      ∑ i, x.weights i * (p i).weights q := by
  classical
  have h := (StdSimplex.isAffineMap_weights ℝ M).map_iConvexComb x p
  change (StdSimplex.affineMapMk (R := ℝ) p x).weights =
    x.iConvexComb (fun i => (p i).weights) at h
  rw [iConvexComb_eq_sum, Finsupp.sum_fintype _ _ (by simp)] at h
  simpa using congrArg (fun w : M →₀ ℝ => w q) h

/-- Triangular nonzero coordinates make the affine extension injective. -/
theorem affineMapMk_injective_of_triangular {n : ℕ} {M : Type u}
    (p : Fin (n + 1) → StdSimplex ℝ M)
    (ht : ∀ i, ∃ q : M, (p i).weights q ≠ 0 ∧ ∀ j, j < i → (p j).weights q = 0) :
    Function.Injective (StdSimplex.affineMapMk (R := ℝ) p) := by
  classical
  intro x y hxy
  by_contra hne
  have hex : ∃ i, x.weights i ≠ y.weights i := by
    by_contra hn
    push_neg at hn
    apply hne
    ext i
    exact hn i
  let s : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => x.weights i ≠ y.weights i)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, by simp [s, hi]⟩
  let i := s.max' hs
  have hi : x.weights i ≠ y.weights i :=
    (Finset.mem_filter.mp (s.max'_mem hs)).2
  obtain ⟨q, hq, hprev⟩ := ht i
  have hc : (∑ j, (x.weights j - y.weights j) * (p j).weights q) = 0 := by
    calc
      (∑ j, (x.weights j - y.weights j) * (p j).weights q) =
          (∑ j, x.weights j * (p j).weights q) -
            (∑ j, y.weights j * (p j).weights q) := by
              simp only [sub_mul, Finset.sum_sub_distrib]
      _ = 0 := by
        rw [← affineMapMk_weights_apply p x q, ← affineMapMk_weights_apply p y q,
          hxy, sub_self]
  have hz (j : Fin (n + 1)) (hji : j ≠ i) :
      (x.weights j - y.weights j) * (p j).weights q = 0 := by
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [hprev j hj, mul_zero]
    · have hjxy : x.weights j = y.weights j := by
        by_contra hjne
        have hjs : j ∈ s := by simp [s, hjne]
        have hle : j ≤ i := s.le_max' j hjs
        exact (not_lt_of_ge hle) hj
      rw [hjxy, sub_self, zero_mul]
  have he : (∑ j, (x.weights j - y.weights j) * (p j).weights q) =
      (x.weights i - y.weights i) * (p i).weights q :=
    Finset.sum_eq_single i (fun j _ hji => hz j hji) (by simp)
  rw [he] at hc
  exact hi (sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_right hq))

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.affineMapMk_weights_apply
#print axioms HomotopyHypothesis.Approximation.Zeeman.affineMapMk_injective_of_triangular
