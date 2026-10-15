import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import HomotopyHypothesis.Approximation.Zeeman.FiniteAverageContractionStatement
/-!
# Finite average contraction estimate

For real numbers bounded in an interval `[a, b]`, the average over an embedded
nonempty finite subset differs from the total average by at most `(n / (n + 1)) * (b - a)`.
-/

universe u

open scoped BigOperators

namespace HomotopyHypothesis.Finite.AverageContraction

open HomotopyHypothesis.Approximation.Zeeman

lemma abs_sub_le_of_bounds {a b u v : ℝ}
    (hu : a ≤ u ∧ u ≤ b) (hv : a ≤ v ∧ v ≤ b) :
    |u - v| ≤ b - a := by
  rw [abs_le]
  constructor
  · linarith
  · linarith

lemma average_bounds {m : ℕ} (y : Fin (m + 1) → ℝ) (a b : ℝ)
    (hy : ∀ j, a ≤ y j ∧ y j ≤ b) :
    a ≤ (∑ j : Fin (m + 1), y j) / ((m : ℝ) + 1) ∧
    (∑ j : Fin (m + 1), y j) / ((m : ℝ) + 1) ≤ b := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  constructor
  · rw [le_div_iff₀ hm]
    have h1 : ∑ j : Fin (m + 1), a ≤ ∑ j : Fin (m + 1), y j :=
      Finset.sum_le_sum (fun j _ => (hy j).1)
    have h2 : ∑ j : Fin (m + 1), a = ((m : ℝ) + 1) * a := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    linarith
  · rw [div_le_iff₀ hm]
    have h1 : ∑ j : Fin (m + 1), y j ≤ ∑ j : Fin (m + 1), b :=
      Finset.sum_le_sum (fun j _ => (hy j).2)
    have h2 : ∑ j : Fin (m + 1), b = ((m : ℝ) + 1) * b := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    linarith

/-- The finite average contraction estimate for nested nonempty subsets. -/
theorem finiteAverageContractionStatement_proof : FiniteAverageContractionStatement := by
  intro n m e x a b hx
  have hba : 0 ≤ b - a := by
    have h0 := hx 0
    linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  let S : Finset (Fin (n + 1)) := Finset.univ.map e
  let T : Finset (Fin (n + 1)) := Finset.univ \ S
  have hS_sub : S ⊆ Finset.univ := Finset.subset_univ S
  have hcard_sdiff : T.card + S.card = (Finset.univ : Finset (Fin (n + 1))).card :=
    Finset.card_sdiff_add_card_eq_card hS_sub
  have hcard_S : S.card = m + 1 := by
    dsimp [S]
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hcard_univ : (Finset.univ : Finset (Fin (n + 1))).card = n + 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hcard : T.card + (m + 1) = n + 1 := by
    rw [hcard_S, hcard_univ] at hcard_sdiff
    exact hcard_sdiff
  have hcard_le : T.card ≤ n := by omega
  have hcard_le_real : (T.card : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hcard_le
  have hcard_real : (T.card : ℝ) + ((m : ℝ) + 1) = (n : ℝ) + 1 := by
    have hc := congr_arg (Nat.cast : ℕ → ℝ) hcard
    push_cast at hc
    exact hc
  have hsum_split : (∑ i ∈ T, x i) + ∑ i ∈ S, x i = ∑ i : Fin (n + 1), x i :=
    Finset.sum_sdiff hS_sub
  have hsum_map : ∑ i ∈ S, x i = ∑ j : Fin (m + 1), x (e j) :=
    Finset.sum_map Finset.univ e x
  let A_S : ℝ := (∑ j : Fin (m + 1), x (e j)) / ((m : ℝ) + 1)
  have hAS_mul : ((m : ℝ) + 1) * A_S = ∑ j : Fin (m + 1), x (e j) := by
    dsimp [A_S]
    rw [mul_div_cancel₀ _ (ne_of_gt hm_pos)]
  have hN_div : ((n : ℝ) + 1) * ((∑ i : Fin (n + 1), x i) / ((n : ℝ) + 1)) =
      ∑ i : Fin (n + 1), x i :=
    mul_div_cancel₀ _ (ne_of_gt hn_pos)
  have hsum_const : ∑ i ∈ T, A_S = (T.card : ℝ) * A_S := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h_diff_mul :
      ((n : ℝ) + 1) * (A_S - (∑ i : Fin (n + 1), x i) / ((n : ℝ) + 1)) =
      ∑ i ∈ T, (A_S - x i) := by
    rw [mul_sub, hN_div, ← hsum_split, hsum_map, ← hAS_mul, Finset.sum_sub_distrib, hsum_const]
    rw [← hcard_real]
    ring
  have h_diff_eq :
      A_S - (∑ i : Fin (n + 1), x i) / ((n : ℝ) + 1) =
      (∑ i ∈ T, (A_S - x i)) / ((n : ℝ) + 1) := by
    rw [← h_diff_mul, mul_div_cancel_left₀ _ (ne_of_gt hn_pos)]
  have h_abs_eq :
      |A_S - (∑ i : Fin (n + 1), x i) / ((n : ℝ) + 1)| =
      |∑ i ∈ T, (A_S - x i)| / ((n : ℝ) + 1) := by
    rw [h_diff_eq, abs_div, abs_of_pos hn_pos]
  have hAS_bounds : a ≤ A_S ∧ A_S ≤ b :=
    average_bounds (fun j => x (e j)) a b (fun j => hx (e j))
  have h_term_le : ∀ i ∈ T, |A_S - x i| ≤ b - a := by
    intro i _
    exact abs_sub_le_of_bounds hAS_bounds (hx i)
  have h_abs_sum :
      |∑ i ∈ T, (A_S - x i)| ≤ ∑ i ∈ T, |A_S - x i| :=
    Finset.abs_sum_le_sum_abs _ _
  have h_sum_le :
      ∑ i ∈ T, |A_S - x i| ≤ (T.card : ℝ) * (b - a) := by
    have h1 : ∑ i ∈ T, |A_S - x i| ≤ ∑ i ∈ T, (b - a) :=
      Finset.sum_le_sum h_term_le
    have h2 : ∑ i ∈ T, (b - a) = (T.card : ℝ) * (b - a) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    linarith
  have h_abs_total_le :
      |∑ i ∈ T, (A_S - x i)| ≤ (T.card : ℝ) * (b - a) :=
    le_trans h_abs_sum h_sum_le
  have h_bound1 :
      |A_S - (∑ i : Fin (n + 1), x i) / ((n : ℝ) + 1)| ≤
      ((T.card : ℝ) * (b - a)) / ((n : ℝ) + 1) := by
    rw [h_abs_eq]
    exact div_le_div_of_nonneg_right h_abs_total_le (le_of_lt hn_pos)
  have h_bound2 :
      ((T.card : ℝ) * (b - a)) / ((n : ℝ) + 1) ≤
      (n : ℝ) / ((n : ℝ) + 1) * (b - a) := by
    have hnum : (T.card : ℝ) * (b - a) ≤ (n : ℝ) * (b - a) :=
      mul_le_mul_of_nonneg_right hcard_le_real hba
    have hdiv : ((T.card : ℝ) * (b - a)) / ((n : ℝ) + 1) ≤ ((n : ℝ) * (b - a)) / ((n : ℝ) + 1) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hn_pos)
    have heq : ((n : ℝ) * (b - a)) / ((n : ℝ) + 1) = (n : ℝ) / ((n : ℝ) + 1) * (b - a) := by
      ring
    rw [heq] at hdiv
    exact hdiv
  exact le_trans h_bound1 h_bound2

example : FiniteAverageContractionStatement :=
  finiteAverageContractionStatement_proof

end HomotopyHypothesis.Finite.AverageContraction

#print axioms HomotopyHypothesis.Finite.AverageContraction.finiteAverageContractionStatement_proof
