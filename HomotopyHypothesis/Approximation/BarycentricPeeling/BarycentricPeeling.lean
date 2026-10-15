import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Lattice
import HomotopyHypothesis.Approximation.Zeeman.BarycentricPeelingStatement
/-!
# Barycentric peeling in a finite simplex

A probability vector can be decomposed into a uniform part and a probability
vector on the boundary of the simplex.
-/

universe u

open Convexity

namespace HomotopyHypothesis.Approximation.BarycentricPeeling

theorem barycentricPeelingStatement_proof :
    HomotopyHypothesis.Approximation.Zeeman.BarycentricPeelingStatement := by
  intro n t
  obtain ⟨i, hi⟩ := Finite.exists_min (fun j : Fin (n + 1) => t.weights j)
  let μ : ℝ := t.weights i
  have hmin : ∀ j : Fin (n + 1), μ ≤ t.weights j := by
    intro j
    simpa [μ] using hi j
  have hμ_nonneg : 0 ≤ μ := by
    dsimp [μ]
    exact t.weights_nonneg i
  let c : ℝ := (n + 1 : ℝ) * μ
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (by positivity) hμ_nonneg
  have hc_le : c ≤ 1 := by
    dsimp [c]
    calc
      (n + 1 : ℝ) * μ = ∑ _j : Fin (n + 1), μ := by
        simp [Finset.sum_const, Fintype.card_fin]
      _ ≤ ∑ j : Fin (n + 1), t.weights j :=
        Finset.sum_le_sum fun j _ => hmin j
      _ = 1 := t.total_of_fintype
  by_cases hc : c = 1
  · have hsumDiff : ∑ j : Fin (n + 1), (t.weights j - μ) = 0 := by
      rw [Finset.sum_sub_distrib, t.total_of_fintype]
      have hmul : (n + 1 : ℝ) * μ = 1 := by simpa [c] using hc
      simp [Finset.sum_const, Fintype.card_fin, hmul]
    have hdiff_nonneg : ∀ j : Fin (n + 1), 0 ≤ t.weights j - μ := by
      intro j
      exact sub_nonneg.mpr (hmin j)
    have hweight : ∀ j : Fin (n + 1), t.weights j = μ := by
      intro j
      have hle : t.weights j - μ ≤ ∑ k : Fin (n + 1), (t.weights k - μ) :=
        Finset.single_le_sum (fun k _ => hdiff_nonneg k) (Finset.mem_univ j)
      have hzero : t.weights j - μ = 0 := by
        rw [hsumDiff] at hle
        exact le_antisymm hle (hdiff_nonneg j)
      exact sub_eq_zero.mp hzero
    have hcardmul : (Fintype.card (Fin (n + 1)) : ℝ) * μ = 1 := by
      simpa [Fintype.card_fin, c] using hc
    have hcard : (Fintype.card (Fin (n + 1)) : ℝ) ≠ 0 := by
      rw [Fintype.card_fin]
      positivity
    have hμ : μ = (Fintype.card (Fin (n + 1)) : ℝ)⁻¹ := by
      field_simp [hcard]
      nlinarith [hcardmul]
    left
    apply StdSimplex.ext
    apply Finsupp.ext
    intro j
    simpa only [hweight j, StdSimplex.weights_barycenter_apply, Fintype.card_fin] using hμ
  · have hc_lt : c < 1 := lt_of_le_of_ne hc_le hc
    have hden : 1 - c ≠ 0 := by linarith
    have hsumDiff : ∑ j : Fin (n + 1), (t.weights j - μ) = 1 - c := by
      rw [Finset.sum_sub_distrib, t.total_of_fintype]
      simp [Finset.sum_const, Fintype.card_fin, c]
    let q : StdSimplex ℝ (Fin (n + 1)) := {
      weights := Finsupp.equivFunOnFinite.symm
        (fun j : Fin (n + 1) => (t.weights j - μ) / (1 - c))
      nonneg := by
        intro j
        apply div_nonneg
        · exact sub_nonneg.mpr (hmin j)
        · linarith
      total := by
        have htotal : ∑ j : Fin (n + 1), (t.weights j - μ) / (1 - c) = 1 := by
          calc
            ∑ j : Fin (n + 1), (t.weights j - μ) / (1 - c) =
                (∑ j : Fin (n + 1), (t.weights j - μ)) * (1 - c)⁻¹ := by
              simp_rw [div_eq_mul_inv]
              rw [← Finset.sum_mul]
            _ = 1 := by rw [hsumDiff]; exact mul_inv_cancel₀ hden
        simpa [Finsupp.sum_fintype] using htotal
    }
    right
    refine ⟨c, q, i, hc_nonneg, hc_lt, ?_, ?_⟩
    · change (t.weights i - μ) / (1 - c) = 0
      have hiμ : t.weights i = μ := by rfl
      rw [hiμ]
      simp
    · intro j
      change t.weights j = c *
        (StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))).weights j +
          (1 - c) * ((t.weights j - μ) / (1 - c))
      rw [StdSimplex.weights_barycenter_apply]
      have hcard : (Fintype.card (Fin (n + 1)) : ℝ) ≠ 0 := by
        rw [Fintype.card_fin]
        positivity
      have hunif : c * (Fintype.card (Fin (n + 1)) : ℝ)⁻¹ = μ := by
        dsimp [c]
        rw [Fintype.card_fin]
        field_simp [hcard]
        push_cast
        ring
      rw [hunif]
      field_simp [hden]
      ring

#print axioms HomotopyHypothesis.Approximation.BarycentricPeeling.barycentricPeelingStatement_proof
