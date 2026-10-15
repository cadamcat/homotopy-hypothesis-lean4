import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Topology.Category.TopCat.Sphere
import HomotopyHypothesis.Realization.Boundary.RealizationGeometry
/-!
# The standard simplex as a disk

The standard simplex is identified with the closed coordinate simplex, then with a disk by radial
rescaling of its convex interior.
-/

universe u

open CategoryTheory Limits
open Convexity
open HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Realization.Boundary

/-- The full-dimensional coordinate model of a closed simplex. -/
abbrev ClosedCoordSimplex (n : ℕ) :=
  {x : Fin n → ℝ // (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- Drop the last barycentric coordinate of a standard simplex. -/
noncomputable def stdSimplexCoordsEquiv (n : ℕ) :
    StdSimplex ℝ (Fin (n + 1)) ≃ ClosedCoordSimplex n where
  toFun s := by
    let g : Fin n → ℝ := fun i => s.weights (Fin.castSucc i)
    refine ⟨g, ?_⟩
    constructor
    · intro i
      exact s.weights_nonneg (Fin.castSucc i)
    · have hsum : (∑ i : Fin n, s.weights i.castSucc) + s.weights (Fin.last n) = 1 := by
        simpa only [Fin.sum_univ_castSucc] using s.total_of_fintype
      change (∑ i : Fin n, s.weights i.castSucc) ≤ 1
      linarith [s.weights_nonneg (Fin.last n)]
  invFun x := by
    let f : Fin (n + 1) → ℝ := Fin.lastCases (1 - ∑ i, x.1 i) (fun i => x.1 i)
    refine { weights := Finsupp.equivFunOnFinite.symm f, nonneg := ?_, total := ?_ }
    · intro i
      rw [Finsupp.coe_equivFunOnFinite_symm]
      cases i using Fin.lastCases with
      | last =>
        simp only [f, Fin.lastCases_last]
        exact sub_nonneg.mpr x.2.2
      | cast j =>
        simpa [f] using x.2.1 j
    · rw [Finsupp.sum_fintype _ _ (by simp)]
      change (∑ i : Fin (n + 1), f i) = 1
      rw [Fin.sum_univ_castSucc]
      simp only [f, Fin.lastCases_castSucc, Fin.lastCases_last]
      ring
  left_inv s := by
    apply StdSimplex.ext
    ext i
    rw [Finsupp.coe_equivFunOnFinite_symm]
    cases i using Fin.lastCases with
    | last =>
      have hsum : (∑ i : Fin n, s.weights (Fin.castSucc i)) + s.weights (Fin.last n) = 1 := by
        simpa only [Fin.sum_univ_castSucc] using s.total_of_fintype
      simp only [Fin.lastCases_last]
      linarith [hsum]
    | cast j =>
      simp [Fin.lastCases_castSucc]
  right_inv x := by
    apply Subtype.ext
    funext i
    simp [Fin.lastCases_castSucc]

/-- The barycentric-coordinate equivalence is a homeomorphism. -/
noncomputable def stdSimplexCoordsHomeomorph (n : ℕ) :
    StdSimplex ℝ (Fin (n + 1)) ≃ₜ ClosedCoordSimplex n := by
  letI : CompactSpace (StdSimplex ℝ (Fin (n + 1))) := inferInstance
  exact Continuous.homeoOfEquivCompactToT2 (f := stdSimplexCoordsEquiv n) (by
    rw [StdSimplex.continuous_iff]
    intro ι _ f
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    change Continuous (fun a : StdSimplex ℝ ι =>
      (StdSimplex.map f a).weights (Fin.castSucc i))
    exact (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) (Fin.castSucc i)).comp
      (by fun_prop : Continuous (StdSimplex.map f)))

end HomotopyHypothesis.Realization.Boundary
