import HomotopyHypothesis.Realization.Boundary.RealizationBoundary
import HomotopyHypothesis.Realization.Boundary.SimplexDisk
/-!
# A prism retraction for a simplex horn

The radial parameter stays between one half and one. This bound keeps the projection continuous
and ensures that it maps the simplex prism back into itself.
-/

universe u

set_option maxHeartbeats 1000000

open CategoryTheory Limits
open HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Realization.Boundary

/-- The barycentric weight of a coordinate-simplex point. -/
noncomputable def hornPrismWeight (n : ℕ) (x : ClosedCoordSimplex n) (i : Fin (n + 1)) : ℝ :=
  closedCoordBarycentricWeights n x i

theorem hornPrismWeight_total (n : ℕ) (x : ClosedCoordSimplex n) :
    ∑ i : Fin (n + 1), hornPrismWeight n x i = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [hornPrismWeight, closedCoordBarycentricWeights_castSucc,
    closedCoordBarycentricWeights_last]
  ring

/-- The barycentric coordinates other than the omitted horn vertex. -/
def hornPrismIndices (n : ℕ) (k : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.erase k

theorem hornPrismIndices_nonempty {n : ℕ} (hn : 0 < n) (k : Fin (n + 1)) :
    (hornPrismIndices n k).Nonempty := by
  apply Finset.card_pos.mp
  simp [hornPrismIndices, Finset.card_erase_of_mem]
  omega

/-- The finite face maximum in the radial projection formula. -/
noncomputable def hornPrismFaceMax (n : ℕ) (k : Fin (n + 1))
    (x : ClosedCoordSimplex n) : ℝ :=
  (hornPrismIndices n k).fold max 0
    (fun i => 1 - (n : ℝ) * hornPrismWeight n x i / 2)

/-- The radial scale for the prism projection onto the horn prism. -/
noncomputable def hornPrismScale (n : ℕ) (hn : 0 < n) (k : Fin (n + 1))
    (x : ClosedCoordSimplex n) (t : unitInterval) : ℝ :=
  max (hornPrismFaceMax n k x) |2 * (t : ℝ) - 1|

theorem hornPrismScale_lower {n : ℕ} (hn : 0 < n) (k : Fin (n + 1))
    (x : ClosedCoordSimplex n) (t : unitInterval) :
    (1 : ℝ) / 2 ≤ hornPrismScale n hn k x t := by
  let S : Finset (Fin (n + 1)) := hornPrismIndices n k
  have hS : S.Nonempty := hornPrismIndices_nonempty hn k
  let w := hornPrismWeight n x
  have htotal : ∑ i : Fin (n + 1), w i = 1 := by
    simpa [w] using hornPrismWeight_total n x
  have hweight (i : Fin (n + 1)) : 0 ≤ w i := by
    exact ((stdSimplexCoordsEquiv n).symm x).weights_nonneg i
  have hsumS : ∑ i ∈ S, w i = 1 - w k := by
    have h := Finset.sum_erase_add Finset.univ w (Finset.mem_univ k)
    rw [htotal] at h
    dsimp [S, hornPrismIndices] at h ⊢
    linarith
  have hcard : (S.card : ℝ) = n := by
    simp [S, hornPrismIndices]
  have hsumOne : ∑ i ∈ S, (1 : ℝ) = n := by
    calc
      _ = (S.card : ℝ) := by simp
      _ = n := hcard
  have hsumQ :
      ∑ i ∈ S, (1 - (n : ℝ) * w i / 2) = (n : ℝ) * (1 + w k) / 2 := by
    calc
      _ = (∑ i ∈ S, (1 : ℝ)) -
          ∑ i ∈ S, ((n : ℝ) / 2 * w i) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (S.card : ℝ) - (n : ℝ) / 2 * (1 - w k) := by
        rw [hsumOne, hcard, ← Finset.mul_sum, hsumS]
      _ = (n : ℝ) * (1 + w k) / 2 := by
        have hcard' : (S.card : ℝ) = (n : ℝ) := hcard
        rw [← hcard']
        ring
  let qmax : ℝ := S.fold max 0 (fun i => 1 - (n : ℝ) * w i / 2)
  have hsum_le :
      (∑ i ∈ S, (1 - (n : ℝ) * w i / 2)) ≤ (S.card : ℝ) * qmax := by
    have hfold : 0 ≤ qmax ∧ ∀ i ∈ S, 1 - (n : ℝ) * w i / 2 ≤ qmax := by
      apply (Finset.fold_max_le (s := S) (b := (0 : ℝ))
        (f := fun i => 1 - (n : ℝ) * w i / 2) qmax).mp
      rfl
    calc
      _ ≤ ∑ i ∈ S, qmax := Finset.sum_le_sum fun i hi => by
        exact hfold.2 i hi
      _ = (S.card : ℝ) * qmax := by simp [Finset.sum_const]
  have hqmax : (1 : ℝ) / 2 ≤ qmax := by
    have hwk := hweight k
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    rw [hsumQ] at hsum_le
    rw [hcard] at hsum_le
    nlinarith [hsum_le, mul_nonneg (le_of_lt hnR) hwk]
  have hscale : qmax ≤ hornPrismScale n hn k x t := by
    change qmax ≤ max qmax _
    exact le_max_left _ _
  exact hqmax.trans hscale

theorem hornPrismScale_upper {n : ℕ} (hn : 0 < n) (k : Fin (n + 1))
    (x : ClosedCoordSimplex n) (t : unitInterval) :
    hornPrismScale n hn k x t ≤ 1 := by
  let S := hornPrismIndices n k
  have hqmax : hornPrismFaceMax n k x ≤ 1 := by
    dsimp [hornPrismFaceMax, S]
    apply (Finset.fold_max_le (s := hornPrismIndices n k) (b := (0 : ℝ))
      (f := fun i => 1 - (n : ℝ) * hornPrismWeight n x i / 2) (1 : ℝ)).2
    constructor
    · norm_num
    · intro i hi
      have hw : 0 ≤ hornPrismWeight n x i :=
        ((stdSimplexCoordsEquiv n).symm x).weights_nonneg i
      have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      nlinarith [mul_nonneg hnR hw]
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have habs : |2 * (t : ℝ) - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  exact max_le hqmax habs

/-- The point beyond the omitted face used for radial projection. -/
noncomputable def hornPrismCenterWeight (n : ℕ) (k i : Fin (n + 1)) : ℝ :=
  if i = k then -1 else 2 / (n : ℝ)

/-- The barycentric coordinates after radial projection. -/
noncomputable def hornPrismProjectedWeight (n : ℕ) (hn : 0 < n) (k : Fin (n + 1))
    (x : ClosedCoordSimplex n) (t : unitInterval) (i : Fin (n + 1)) : ℝ :=
  hornPrismCenterWeight n k i +
    (hornPrismWeight n x i - hornPrismCenterWeight n k i) / hornPrismScale n hn k x t

theorem hornPrismCenterWeight_sum {n : ℕ} (hn : 0 < n) (k : Fin (n + 1)) :
    ∑ i : Fin (n + 1), hornPrismCenterWeight n k i = 1 := by
  let S := hornPrismIndices n k
  have hcard : (S.card : ℝ) = n := by simp [S, hornPrismIndices]
  have hsumS : ∑ i ∈ S, hornPrismCenterWeight n k i = (S.card : ℝ) * (2 / (n : ℝ)) := by
    calc
      _ = ∑ i ∈ S, (2 / (n : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i ∈ Finset.univ.erase k := by simpa [S, hornPrismIndices] using hi
        have hik : i ≠ k := (Finset.mem_erase.mp hi').1
        simp [hornPrismCenterWeight, hik]
      _ = _ := by simp [Finset.sum_const]
  have hdecomp := Finset.sum_erase_add Finset.univ (hornPrismCenterWeight n k)
    (Finset.mem_univ k)
  calc
    _ = (∑ i ∈ S, hornPrismCenterWeight n k i) + hornPrismCenterWeight n k k := by
      dsimp [S, hornPrismIndices]
      exact hdecomp.symm
    _ = (S.card : ℝ) * (2 / (n : ℝ)) - 1 := by
      rw [hsumS]
      simp [hornPrismCenterWeight]
      ring
    _ = 1 := by
      rw [hcard]
      have hnR : (n : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hn)
      field_simp
      <;> ring

theorem hornPrismProjectedWeight_sum {n : ℕ} (hn : 0 < n) (k : Fin (n + 1))
    (x : ClosedCoordSimplex n) (t : unitInterval) :
    ∑ i : Fin (n + 1), hornPrismProjectedWeight n hn k x t i = 1 := by
  simp_rw [hornPrismProjectedWeight]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib]
  have hw : ∑ i : Fin (n + 1), hornPrismWeight n x i = 1 :=
    hornPrismWeight_total n x
  rw [hw, hornPrismCenterWeight_sum hn k]
  simp

theorem hornPrismProjectedWeight_nonneg {n : ℕ} (hn : 0 < n) (k : Fin (n + 1))
    (x : ClosedCoordSimplex n) (t : unitInterval) (i : Fin (n + 1)) :
    0 ≤ hornPrismProjectedWeight n hn k x t i := by
  let d := hornPrismScale n hn k x t
  have hdlo : (1 : ℝ) / 2 ≤ d := by simpa [d] using hornPrismScale_lower hn k x t
  have hdhi : d ≤ 1 := by simpa [d] using hornPrismScale_upper hn k x t
  have hdpos : 0 < d := by linarith
  have hw : 0 ≤ hornPrismWeight n x i :=
    ((stdSimplexCoordsEquiv n).symm x).weights_nonneg i
  have hmul : d * hornPrismProjectedWeight n hn k x t i =
      hornPrismWeight n x i + (d - 1) * hornPrismCenterWeight n k i := by
    dsimp [hornPrismProjectedWeight, d]
    have hdne : hornPrismScale n hn k x t ≠ 0 := ne_of_gt (by linarith [hdlo])
    field_simp [hdne]
    <;> ring
  have hscaled : 0 ≤ d * hornPrismProjectedWeight n hn k x t i := by
    rw [hmul]
    by_cases hik : i = k
    · subst i
      simp [hornPrismCenterWeight]
      nlinarith
    · have hrad : 1 - (n : ℝ) * hornPrismWeight n x i / 2 ≤ d := by
        have hi : i ∈ hornPrismIndices n k := Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩
        have hq := (Finset.fold_max_le (s := hornPrismIndices n k) (b := (0 : ℝ))
          (f := fun j => 1 - (n : ℝ) * hornPrismWeight n x j / 2)
          (hornPrismFaceMax n k x)).mp le_rfl
        exact (hq.2 i hi).trans (le_max_left _ _)
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hlinear : 0 ≤ (n : ℝ) * hornPrismWeight n x i + 2 * (d - 1) := by
        nlinarith [hrad]
      have hmul' : (n : ℝ) *
          (hornPrismWeight n x i + (2 / (n : ℝ)) * (d - 1)) =
          (n : ℝ) * hornPrismWeight n x i + 2 * (d - 1) := by
        field_simp [ne_of_gt hnR]
        <;> ring
      have hnonneg : 0 ≤ hornPrismWeight n x i + (2 / (n : ℝ)) * (d - 1) := by
        apply (mul_nonneg_iff_of_pos_left hnR).1
        rw [hmul']
        exact hlinear
      simpa [hornPrismCenterWeight, hik, mul_comm] using hnonneg
  exact (mul_nonneg_iff_of_pos_left hdpos).1 hscaled

/-- The projected barycentric coordinates, with the last one omitted. -/
noncomputable def hornPrismProjectedCoords (n : ℕ) (hn : 0 < n) (k : Fin (n + 1))
    (x : ClosedCoordSimplex n) (t : unitInterval) : ClosedCoordSimplex n := by
  refine ⟨fun i => hornPrismProjectedWeight n hn k x t i.castSucc, ?_⟩
  constructor
  · intro i
    exact hornPrismProjectedWeight_nonneg hn k x t i.castSucc
  · have htotal := hornPrismProjectedWeight_sum hn k x t
    have hdecomp :
        (∑ i : Fin n, hornPrismProjectedWeight n hn k x t i.castSucc) +
          hornPrismProjectedWeight n hn k x t (Fin.last n) = 1 := by
      simpa only [Fin.sum_univ_castSucc] using htotal
    have hlast := hornPrismProjectedWeight_nonneg hn k x t (Fin.last n)
    linarith

@[simp]
theorem hornPrismProjectedCoords_weight_castSucc {n : ℕ} (hn : 0 < n)
    (k : Fin (n + 1)) (x : ClosedCoordSimplex n) (t : unitInterval) (i : Fin n) :
    closedCoordBarycentricWeights n (hornPrismProjectedCoords n hn k x t) i.castSucc =
      hornPrismProjectedWeight n hn k x t i.castSucc := by
  rw [closedCoordBarycentricWeights_castSucc]
  rfl

@[simp]
theorem hornPrismProjectedCoords_weight_last {n : ℕ} (hn : 0 < n)
    (k : Fin (n + 1)) (x : ClosedCoordSimplex n) (t : unitInterval) :
    closedCoordBarycentricWeights n (hornPrismProjectedCoords n hn k x t) (Fin.last n) =
      hornPrismProjectedWeight n hn k x t (Fin.last n) := by
  rw [closedCoordBarycentricWeights_last]
  have htotal := hornPrismProjectedWeight_sum hn k x t
  have hdecomp :
      (∑ i : Fin n, hornPrismProjectedWeight n hn k x t i.castSucc) +
        hornPrismProjectedWeight n hn k x t (Fin.last n) = 1 := by
    simpa only [Fin.sum_univ_castSucc] using htotal
  change 1 - (∑ i : Fin n, hornPrismProjectedWeight n hn k x t i.castSucc) = _
  linarith

theorem hornPrismProjectedCoords_weight {n : ℕ} (hn : 0 < n)
    (k : Fin (n + 1)) (x : ClosedCoordSimplex n) (t : unitInterval)
    (i : Fin (n + 1)) :
    hornPrismWeight n (hornPrismProjectedCoords n hn k x t) i =
      hornPrismProjectedWeight n hn k x t i := by
  cases i using Fin.lastCases with
  | last => exact hornPrismProjectedCoords_weight_last hn k x t
  | cast j => exact hornPrismProjectedCoords_weight_castSucc hn k x t j

/-- The union of the faces of the simplex opposite vertices other than `k`. -/
def coordinateHorn (n : ℕ) (k : Fin (n + 1)) : Set (ClosedCoordSimplex n) :=
  {x | ∃ i, i ≠ k ∧ hornPrismWeight n x i = 0}

/-- The horn prism, including both time endpoints. -/
def coordinateHornPrism (n : ℕ) (k : Fin (n + 1)) :
    Set (ClosedCoordSimplex n × unitInterval) :=
  {z | (∃ i, i ≠ k ∧ hornPrismWeight n z.1 i = 0) ∨
    ((z.2 : ℝ) = 0 ∨ (z.2 : ℝ) = 1)}

/-- The radial projection of a simplex prism point to the horn prism. -/
noncomputable def hornPrismProjectedTime (n : ℕ) (hn : 0 < n) (k : Fin (n + 1))
    (x : ClosedCoordSimplex n) (t : unitInterval) : unitInterval := by
  let d := hornPrismScale n hn k x t
  have hdlo : (1 : ℝ) / 2 ≤ d := by simpa [d] using hornPrismScale_lower hn k x t
  have hdpos : 0 < d := by linarith
  have hv : 2 * |(t : ℝ) - 1 / 2| ≤ d := by
    have hv' : |2 * (t : ℝ) - 1| ≤ d := le_max_right _ _
    have heq : |2 * (t : ℝ) - 1| = 2 * |(t : ℝ) - 1 / 2| := by
      rw [show 2 * (t : ℝ) - 1 = 2 * ((t : ℝ) - 1 / 2) by ring,
        abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [heq] at hv'
    exact hv'
  have hdev : |((t : ℝ) - 1 / 2) / d| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hdpos]
    apply (div_le_iff₀ hdpos).2
    nlinarith [hv]
  refine ⟨1 / 2 + ((t : ℝ) - 1 / 2) / d, ?_⟩
  rcases abs_le.mp hdev with ⟨hlo, hhi⟩
  constructor <;> linarith

/-- The explicit radial projection onto a horn prism. -/
noncomputable def hornPrismProjectedPair (n : ℕ) (hn : 0 < n) (k : Fin (n + 1))
    (z : ClosedCoordSimplex n × unitInterval) : ClosedCoordSimplex n × unitInterval :=
  (hornPrismProjectedCoords n hn k z.1 z.2, hornPrismProjectedTime n hn k z.1 z.2)

theorem hornPrismProjectedPair_mem {n : ℕ} (hn : 0 < n) (k : Fin (n + 1))
    (z : ClosedCoordSimplex n × unitInterval) :
    hornPrismProjectedPair n hn k z ∈ coordinateHornPrism n k := by
  let x := z.1
  let t := z.2
  let d := hornPrismScale n hn k x t
  let S := hornPrismIndices n k
  let q := fun i : Fin (n + 1) => 1 - (n : ℝ) * hornPrismWeight n x i / 2
  let qmax := S.fold max 0 q
  have hdlo : (1 : ℝ) / 2 ≤ d := by simpa [d, x, t] using hornPrismScale_lower hn k x t
  have hdpos : 0 < d := by linarith
  have hvq : |2 * (t : ℝ) - 1| ≤ qmax ∨ qmax ≤ |2 * (t : ℝ) - 1| :=
    le_total _ _
  by_cases hcase : |2 * (t : ℝ) - 1| ≤ qmax
  · have hd : d = qmax := by
      change max (hornPrismFaceMax n k x) |2 * (t : ℝ) - 1| = qmax
      have hface : hornPrismFaceMax n k x = qmax := by
        rfl
      rw [hface]
      exact max_eq_left hcase
    have hqmaxlo : (1 : ℝ) / 2 ≤ qmax := by rw [← hd]; exact hdlo
    have hfold : qmax ≤ 0 ∨ ∃ i ∈ S, qmax ≤ q i := by
      simpa [qmax] using
        (Finset.le_fold_max (s := S) (b := (0 : ℝ)) (f := q)
          (S.fold max 0 q)).mp (le_rfl : S.fold max 0 q ≤ S.fold max 0 q)
    rcases hfold with hqzero | ⟨i, hi, hle⟩
    · exfalso
      linarith [hqmaxlo]
    · have hupper : q i ≤ qmax := by
        have h := (Finset.fold_max_le (s := S) (b := (0 : ℝ)) (f := q)
          (S.fold max 0 q)).mp (le_rfl : S.fold max 0 q ≤ S.fold max 0 q)
        exact h.2 i hi
      have hiq : q i = qmax := le_antisymm hupper hle
      have hi' : i ∈ Finset.univ.erase k := by simpa [S, hornPrismIndices] using hi
      have hik : i ≠ k := (Finset.mem_erase.mp hi').1
      have hqeq : q i = d := hiq.trans hd.symm
      have hden : q i ≠ 0 := by rw [hqeq]; exact ne_of_gt hdpos
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
      have hzero : hornPrismProjectedWeight n hn k x t i = 0 := by
        simp only [hornPrismProjectedWeight, hornPrismCenterWeight, if_neg hik]
        change 2 / (n : ℝ) +
          (hornPrismWeight n x i - 2 / (n : ℝ)) / d = 0
        rw [← hqeq]
        simp only [q]
        have hdenForm : (1 - (n : ℝ) * hornPrismWeight n x i / 2) ≠ 0 := by
          simpa [q] using hden
        have hden2 : 2 - (n : ℝ) * hornPrismWeight n x i ≠ 0 := by
          intro hz
          apply hdenForm
          nlinarith
        have hquot :
            (hornPrismWeight n x i - 2 / (n : ℝ)) /
                (1 - (n : ℝ) * hornPrismWeight n x i / 2) = -2 / (n : ℝ) := by
          apply (div_eq_iff hdenForm).2
          field_simp [hnR, hden2]
          <;> ring
        rw [hquot]
        ring
      change (∃ i, i ≠ k ∧
        hornPrismWeight n (hornPrismProjectedCoords n hn k x t) i = 0) ∨ _
      exact Or.inl ⟨i, hik, by rw [hornPrismProjectedCoords_weight]; exact hzero⟩
  · have hvert : qmax ≤ |2 * (t : ℝ) - 1| := le_of_not_ge hcase
    have hd : d = |2 * (t : ℝ) - 1| := by
      change max (hornPrismFaceMax n k x) |2 * (t : ℝ) - 1| =
        |2 * (t : ℝ) - 1|
      have hface : hornPrismFaceMax n k x = qmax := by rfl
      rw [hface]
      exact max_eq_right hvert
    by_cases hpos : 0 ≤ 2 * (t : ℝ) - 1
    · apply Or.inr
      right
      change (hornPrismProjectedTime n hn k x t : ℝ) = 1
      change 1 / 2 + ((t : ℝ) - 1 / 2) / d = 1
      rw [hd, abs_of_nonneg hpos]
      have hne : 2 * (t : ℝ) - 1 ≠ 0 := by
        intro hz
        have hdz : d = 0 := by simpa [hz] using hd
        linarith [hdpos, hdz]
      have hquot : ((t : ℝ) - 1 / 2) / (2 * (t : ℝ) - 1) = 1 / 2 := by
        apply (div_eq_iff hne).2
        ring
      rw [hquot]
      ring
    · apply Or.inr
      left
      change (hornPrismProjectedTime n hn k x t : ℝ) = 0
      change 1 / 2 + ((t : ℝ) - 1 / 2) / d = 0
      have hneg : 2 * (t : ℝ) - 1 < 0 := lt_of_not_ge hpos
      rw [hd, abs_of_neg hneg]
      have hne : 1 - 2 * (t : ℝ) ≠ 0 := by
        intro hz
        have hz' : 2 * (t : ℝ) - 1 = 0 := by linarith
        have hdz : d = 0 := by simpa [hz'] using hd
        linarith [hdpos, hdz]
      have hne' : -1 + 2 * (t : ℝ) ≠ 0 := by
        intro hz
        apply hne
        linarith
      have hquot : ((t : ℝ) - 1 / 2) / (1 - 2 * (t : ℝ)) = -1 / 2 := by
        apply (div_eq_iff hne).2
        ring
      have hdenEq : 1 - 2 * (t : ℝ) = -(2 * (t : ℝ) - 1) := by ring
      rw [hdenEq] at hquot
      rw [hquot]
      ring

theorem hornPrismProjectedPair_fixed {n : ℕ} (hn : 0 < n) (k : Fin (n + 1))
    (z : ClosedCoordSimplex n × unitInterval) (hz : z ∈ coordinateHornPrism n k) :
    hornPrismProjectedPair n hn k z = z := by
  let d := hornPrismScale n hn k z.1 z.2
  let S := hornPrismIndices n k
  let q := fun i : Fin (n + 1) => 1 - (n : ℝ) * hornPrismWeight n z.1 i / 2
  let qmax := S.fold max 0 q
  have hdlo : (1 : ℝ) / 2 ≤ d := by
    simpa [d] using hornPrismScale_lower hn k z.1 z.2
  have hdhi : d ≤ 1 := by
    simpa [d] using hornPrismScale_upper hn k z.1 z.2
  have hd : d = 1 := by
    apply le_antisymm hdhi
    change (∃ i, i ≠ k ∧ hornPrismWeight n z.1 i = 0) ∨
      ((z.2 : ℝ) = 0 ∨ (z.2 : ℝ) = 1) at hz
    rcases hz with ⟨i, hik, hi⟩ | htime
    · have hiS : i ∈ S := by
        dsimp [S, hornPrismIndices]
        exact Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩
      have hq : 1 ≤ qmax := by
        have h := (Finset.le_fold_max (s := S) (b := (0 : ℝ)) (f := q) 1).2
          (Or.inr ⟨i, hiS, by simp [q, hi]⟩)
        simpa [qmax] using h
      have hqle : 1 ≤ d := by
        change 1 ≤ max (hornPrismFaceMax n k z.1)
          |2 * (z.2 : ℝ) - 1|
        have hface : hornPrismFaceMax n k z.1 = qmax := by rfl
        rw [hface]
        exact le_trans hq (le_max_left _ _)
      exact hqle
    · rcases htime with hzero | hone
      · have hv : |2 * (z.2 : ℝ) - 1| = 1 := by rw [hzero]; norm_num
        have hle : 1 ≤ d := by
          change 1 ≤ max (hornPrismFaceMax n k z.1)
            |2 * (z.2 : ℝ) - 1|
          rw [hv]
          exact le_max_right _ _
        exact hle
      · have hv : |2 * (z.2 : ℝ) - 1| = 1 := by rw [hone]; norm_num
        have hle : 1 ≤ d := by
          change 1 ≤ max (hornPrismFaceMax n k z.1)
            |2 * (z.2 : ℝ) - 1|
          rw [hv]
          exact le_max_right _ _
        exact hle
  have hscale : hornPrismScale n hn k z.1 z.2 = 1 := by simpa [d] using hd
  apply Prod.ext
  · apply Subtype.ext
    funext i
    change hornPrismProjectedWeight n hn k z.1 z.2 i.castSucc = z.1.1 i
    simp [hornPrismProjectedWeight, hornPrismCenterWeight, hornPrismWeight, hscale,
      closedCoordBarycentricWeights_castSucc]
  · apply Subtype.ext
    change (hornPrismProjectedTime n hn k z.1 z.2 : ℝ) = (z.2 : ℝ)
    simp [hornPrismProjectedTime, hscale]

theorem hornPrismWeight_continuous (n : ℕ) (i : Fin (n + 1)) :
    Continuous (fun x : ClosedCoordSimplex n => hornPrismWeight n x i) := by
  cases i using Fin.lastCases with
  | last =>
    simp only [hornPrismWeight, closedCoordBarycentricWeights_last]
    have hcoord (j : Fin n) : Continuous (fun x : ClosedCoordSimplex n => x.1 j) := by
      exact (continuous_apply j).comp continuous_subtype_val
    exact continuous_const.sub (continuous_finsetSum _ fun j _ => hcoord j)
  | cast j =>
    simp only [hornPrismWeight, closedCoordBarycentricWeights_castSucc]
    exact (continuous_apply j).comp continuous_subtype_val

theorem hornPrismFaceMax_continuous (n : ℕ) (k : Fin (n + 1)) :
    Continuous (fun x : ClosedCoordSimplex n => hornPrismFaceMax n k x) := by
  let S := hornPrismIndices n k
  have hw (i : Fin (n + 1)) :
      Continuous (fun x : ClosedCoordSimplex n => hornPrismWeight n x i) :=
    hornPrismWeight_continuous n i
  let f : Fin (n + 1) → ClosedCoordSimplex n → ℝ :=
    fun i x => 1 - (n : ℝ) * hornPrismWeight n x i / 2
  have hfold : Continuous (fun x : ClosedCoordSimplex n => S.fold max 0 (f · x)) := by
    classical
    induction S using Finset.induction_on with
    | empty => exact continuous_const
    | @insert i S hi ih =>
      simp only [Finset.fold_insert hi]
      have hqi : Continuous (f i) := by
        exact continuous_const.sub ((continuous_const.mul (hw i)).div_const 2)
      exact hqi.max ih
  simpa [hornPrismFaceMax, S, f] using hfold

theorem hornPrismScale_continuous {n : ℕ} (hn : 0 < n) (k : Fin (n + 1)) :
    Continuous (fun z : ClosedCoordSimplex n × unitInterval =>
      hornPrismScale n hn k z.1 z.2) := by
  have hface : Continuous (fun z : ClosedCoordSimplex n × unitInterval =>
      hornPrismFaceMax n k z.1) := (hornPrismFaceMax_continuous n k).comp continuous_fst
  have hv : Continuous (fun z : ClosedCoordSimplex n × unitInterval =>
      |2 * (z.2 : ℝ) - 1|) := by fun_prop
  simpa [hornPrismScale] using hface.max hv

theorem hornPrismScale_pos {n : ℕ} (hn : 0 < n) (k : Fin (n + 1))
    (x : ClosedCoordSimplex n) (t : unitInterval) :
    0 < hornPrismScale n hn k x t := by
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hornPrismScale_lower hn k x t)

theorem hornPrismProjectedWeight_continuous {n : ℕ} (hn : 0 < n) (k : Fin (n + 1))
    (i : Fin (n + 1)) :
    Continuous (fun z : ClosedCoordSimplex n × unitInterval =>
      hornPrismProjectedWeight n hn k z.1 z.2 i) := by
  have hw : Continuous (fun z : ClosedCoordSimplex n × unitInterval =>
      hornPrismWeight n z.1 i) :=
    (hornPrismWeight_continuous n i).comp continuous_fst
  have hd : Continuous (fun z : ClosedCoordSimplex n × unitInterval =>
      hornPrismScale n hn k z.1 z.2) := hornPrismScale_continuous hn k
  have hdne : ∀ z : ClosedCoordSimplex n × unitInterval,
      hornPrismScale n hn k z.1 z.2 ≠ 0 := fun z =>
    ne_of_gt (hornPrismScale_pos hn k z.1 z.2)
  exact continuous_const.add ((hw.sub continuous_const).div hd hdne)

theorem hornPrismProjectedCoords_continuous {n : ℕ} (hn : 0 < n) (k : Fin (n + 1)) :
    Continuous (fun z : ClosedCoordSimplex n × unitInterval =>
      hornPrismProjectedCoords n hn k z.1 z.2) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i => hornPrismProjectedWeight_continuous hn k i.castSucc

theorem hornPrismProjectedTime_continuous {n : ℕ} (hn : 0 < n) (k : Fin (n + 1)) :
    Continuous (fun z : ClosedCoordSimplex n × unitInterval =>
      hornPrismProjectedTime n hn k z.1 z.2) := by
  have hd := hornPrismScale_continuous hn k
  have hdne : ∀ z : ClosedCoordSimplex n × unitInterval,
      hornPrismScale n hn k z.1 z.2 ≠ 0 := by
    intro z
    exact ne_of_gt (hornPrismScale_pos hn k z.1 z.2)
  have ht : Continuous (fun z : ClosedCoordSimplex n × unitInterval => (z.2 : ℝ)) := by
    fun_prop
  have hreal : Continuous (fun z : ClosedCoordSimplex n × unitInterval =>
      1 / 2 + ((z.2 : ℝ) - 1 / 2) / hornPrismScale n hn k z.1 z.2) :=
    continuous_const.add ((ht.sub continuous_const).div hd hdne)
  apply continuous_induced_rng.2
  change Continuous (fun z : ClosedCoordSimplex n × unitInterval =>
    1 / 2 + ((z.2 : ℝ) - 1 / 2) / hornPrismScale n hn k z.1 z.2)
  exact hreal

theorem hornPrismProjectedPair_continuous {n : ℕ} (hn : 0 < n) (k : Fin (n + 1)) :
    Continuous (fun z : ClosedCoordSimplex n × unitInterval =>
      hornPrismProjectedPair n hn k z) := by
  exact (hornPrismProjectedCoords_continuous hn k).prodMk
    (hornPrismProjectedTime_continuous hn k)

end HomotopyHypothesis.Realization.Boundary
