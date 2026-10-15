import HomotopyHypothesis.Challenge
/-!
# Retraction of a disk onto a source hemisphere

The source face `Bᵐ ↪ Bⁿ` lands on a hemisphere of the boundary sphere. That inclusion is a
strong deformation retract of the closed disk: fold the height coordinate by absolute value,
send the resulting point to the hemisphere by the explicit radial formula below, and join the
two ends by the straight line in the convex disk.
-/

noncomputable section

namespace HomotopyHypothesis.Realization.Disk

open scoped unitInterval
open ContinuousMap

/-- Euclidean space `ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The `k`-th coordinate of a vector, or `0` when `k` is out of range. -/
def coord {n : ℕ} (y : E n) (k : ℕ) : ℝ :=
  if hk : k < n then y ⟨k, hk⟩ else 0

lemma coord_of_lt {n : ℕ} (y : E n) {k : ℕ} (hk : k < n) : coord y k = y ⟨k, hk⟩ := by
  simp [coord, hk]

lemma continuous_coord {n : ℕ} (k : ℕ) : Continuous fun y : E n => coord y k := by
  by_cases hk : k < n
  · have hfun : (fun y : E n => coord y k) = fun y => y ⟨k, hk⟩ := by
      ext y
      simp [coord, hk]
    rw [hfun]
    exact PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) ⟨k, hk⟩
  · have hfun : (fun y : E n => coord y k) = fun _ => 0 := by
      ext y
      simp [coord, hk]
    rw [hfun]
    exact continuous_const

/-- Sum of squares of the first `m` coordinates. -/
def frontNormSq {n : ℕ} (m : ℕ) (y : E n) : ℝ :=
  ∑ k ∈ Finset.range m, (coord y k) ^ 2

lemma frontNormSq_nonneg {n : ℕ} (m : ℕ) (y : E n) : 0 ≤ frontNormSq m y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma continuous_frontNormSq {n : ℕ} (m : ℕ) : Continuous fun y : E n => frontNormSq m y := by
  unfold frontNormSq
  exact continuous_finsetSum _ fun k _ => (continuous_coord k).pow 2

/-- Absolute value of the height coordinate, the `m`-th one. -/
def absHeight {n : ℕ} (m : ℕ) (y : E n) : ℝ := |coord y m|

lemma absHeight_nonneg {n : ℕ} (m : ℕ) (y : E n) : 0 ≤ absHeight m y := abs_nonneg _

lemma continuous_absHeight {n : ℕ} (m : ℕ) : Continuous fun y : E n => absHeight m y :=
  continuous_abs.comp (continuous_coord m)

/-- `s + 1`, where `s` is the absolute height. This is at least `1`. -/
def projA {n : ℕ} (m : ℕ) (y : E n) : ℝ := absHeight m y + 1

lemma projA_one_le {n : ℕ} (m : ℕ) (y : E n) : 1 ≤ projA m y := by
  simp only [projA]
  linarith [absHeight_nonneg m y]

lemma continuous_projA {n : ℕ} (m : ℕ) : Continuous fun y : E n => projA m y :=
  (continuous_absHeight m).add continuous_const

/-- Denominator `q + (s + 1)²`. It is at least `1` for every vector. -/
def projDenom {n : ℕ} (m : ℕ) (y : E n) : ℝ := frontNormSq m y + (projA m y) ^ 2

lemma projDenom_one_le {n : ℕ} (m : ℕ) (y : E n) : 1 ≤ projDenom m y := by
  have hq : 0 ≤ frontNormSq m y := frontNormSq_nonneg m y
  have ha : 1 ≤ projA m y := projA_one_le m y
  have ha2 : 1 ≤ (projA m y) ^ 2 := by nlinarith [sq_nonneg (projA m y - 1)]
  simp only [projDenom]
  linarith

lemma projDenom_ne {n : ℕ} (m : ℕ) (y : E n) : projDenom m y ≠ 0 := by
  linarith [projDenom_one_le m y]

lemma continuous_projDenom {n : ℕ} (m : ℕ) : Continuous fun y : E n => projDenom m y :=
  (continuous_frontNormSq m).add ((continuous_projA m).pow 2)

/-- Scale factor `2(s + 1) / (q + (s + 1)²)`. -/
def projT {n : ℕ} (m : ℕ) (y : E n) : ℝ := (2 * projA m y) / projDenom m y

lemma continuous_projT {n : ℕ} (m : ℕ) : Continuous fun y : E n => projT m y := by
  refine ((continuous_const.mul (continuous_projA m)).div (continuous_projDenom m) ?_)
  intro y
  exact projDenom_ne m y

/-- One coordinate of the hemisphere projection. -/
def projectCoordN {n m : ℕ} (_hm : m < n) (y : E n) (k : ℕ) : ℝ :=
  if k < m then projT m y * coord y k
  else if k = m then -1 + projT m y * projA m y
  else 0

lemma continuous_projectCoordN {n m : ℕ} (hm : m < n) (k : ℕ) :
    Continuous fun y : E n => projectCoordN hm y k := by
  by_cases hk : k < m
  · have hfun : (fun y : E n => projectCoordN hm y k) = fun y => projT m y * coord y k := by
      ext y
      simp [projectCoordN, hk]
    rw [hfun]
    exact (continuous_projT m).mul (continuous_coord k)
  · by_cases he : k = m
    · have hfun : (fun y : E n => projectCoordN hm y k) =
          fun y => -1 + projT m y * projA m y := by
        ext y
        simp [projectCoordN, he]
      rw [hfun]
      exact continuous_const.add ((continuous_projT m).mul (continuous_projA m))
    · have hfun : (fun y : E n => projectCoordN hm y k) = fun _ => 0 := by
        ext y
        simp [projectCoordN, hk, he]
      rw [hfun]
      exact continuous_const

/-- Projection of `ℝⁿ` onto the source hemisphere in the coordinate `m`-plane.
The same algebraic expression is continuous on all of `ℝⁿ`: the denominator never vanishes. -/
def projectVec {n m : ℕ} (hm : m < n) (y : E n) : E n :=
  WithLp.toLp 2 fun i : Fin n => projectCoordN hm y i

lemma continuous_projectVec {n m : ℕ} (hm : m < n) : Continuous (projectVec hm) := by
  unfold projectVec
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  simpa using continuous_projectCoordN hm (i : ℕ)

lemma projectVec_apply {n m : ℕ} (hm : m < n) (y : E n) (i : Fin n) :
    projectVec hm y i = projectCoordN hm y i := by
  simp [projectVec, PiLp.toLp_apply]

/-- The first `m` coordinates of the projection, as a vector of `ℝᵐ`. -/
def frontVec {n m : ℕ} (hm : m < n) (y : E n) : E m :=
  WithLp.toLp 2 fun i : Fin m => projectVec hm y (Fin.castLE (Nat.le_of_lt hm) i)

lemma frontVec_apply {n m : ℕ} (hm : m < n) (y : E n) (i : Fin m) :
    frontVec hm y i = projectCoordN hm y i := by
  have hcoe : ((Fin.castLE (Nat.le_of_lt hm) i : Fin n) : ℕ) = i := by
    simp
  simp only [frontVec, projectVec, PiLp.toLp_apply, projectCoordN, hcoe]

lemma continuous_frontVec {n m : ℕ} (hm : m < n) : Continuous (frontVec hm) := by
  unfold frontVec
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) _).comp (continuous_projectVec hm)

/-- `‖front‖² = t² q`. -/
lemma norm_sq_frontVec {n m : ℕ} (hm : m < n) (y : E n) :
    ‖frontVec hm y‖ ^ 2 = projT m y ^ 2 * frontNormSq m y := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have hcoord : ∀ i : Fin m, frontVec hm y i = projT m y * coord y (i : ℕ) := by
    intro i
    rw [frontVec_apply]
    simp only [projectCoordN, ite_eq_left i.isLt]
  trans ∑ i : Fin m, (projT m y * coord y (i : ℕ)) ^ 2
  · refine Fintype.sum_congr _ _ fun i => ?_
    rw [hcoord i]
  · simp_rw [mul_pow, ← Finset.mul_sum]
    rw [frontNormSq, ← Fin.sum_univ_eq_sum_range (fun k => (coord y k) ^ 2) m]

/-- The scale identity `t² q + (t a - 1)² = 1`. -/
lemma scale_sq (q a : ℝ) (hq : 0 ≤ q) (ha : 1 ≤ a) :
    ((2 * a) / (q + a ^ 2)) ^ 2 * q + ((2 * a) / (q + a ^ 2) * a - 1) ^ 2 = 1 := by
  have hd : q + a ^ 2 ≠ 0 := by
    have ha2 : 1 ≤ a ^ 2 := by nlinarith [sq_nonneg (a - 1)]
    linarith
  field_simp [hd]
  ring

lemma front_height_one {n m : ℕ} (hm : m < n) (y : E n) :
    ‖frontVec hm y‖ ^ 2 + (-1 + projT m y * projA m y) ^ 2 = 1 := by
  rw [norm_sq_frontVec hm y]
  have hid := scale_sq (frontNormSq m y) (projA m y) (frontNormSq_nonneg m y) (projA_one_le m y)
  have hrewrite : projT m y = (2 * projA m y) / (frontNormSq m y + (projA m y) ^ 2) := rfl
  rw [hrewrite]
  have hsq : (-1 + (2 * projA m y) / (frontNormSq m y + (projA m y) ^ 2) * projA m y) ^ 2 =
      ((2 * projA m y) / (frontNormSq m y + (projA m y) ^ 2) * projA m y - 1) ^ 2 := by
    ring
  rw [hsq]
  exact hid

lemma frontVec_norm_le {n m : ℕ} (hm : m < n) (y : E n) : ‖frontVec hm y‖ ≤ 1 := by
  have h := front_height_one hm y
  have hnn : 0 ≤ ‖frontVec hm y‖ := norm_nonneg _
  have hsq : ‖frontVec hm y‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (-1 + projT m y * projA m y)]
  nlinarith

lemma frontVec_mem {n m : ℕ} (hm : m < n) (y : E n) :
    frontVec hm y ∈ Metric.closedBall (0 : E m) 1 := by
  rw [mem_closedBall_zero_iff]
  exact frontVec_norm_le hm y

/-- Norm decomposition `‖y‖² = q + yₘ² +` tail. -/
lemma norm_sq_parts {n m : ℕ} (hm : m < n) (y : E n) :
    ‖y‖ ^ 2 = frontNormSq m y + (coord y m) ^ 2 +
      ∑ k ∈ Finset.Ico (m + 1) n, (coord y k) ^ 2 := by
  have hsum : ‖y‖ ^ 2 = ∑ k ∈ Finset.range n, (coord y k) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq,
      ← Fin.sum_univ_eq_sum_range (fun k => (coord y k) ^ 2) n]
    refine Fintype.sum_congr _ _ fun i => ?_
    simp [coord, i.isLt]
  rw [hsum, ← Finset.sum_range_add_sum_Ico (fun k => (coord y k) ^ 2) hm.le,
    Finset.sum_eq_sum_Ico_succ_bot hm (fun k => (coord y k) ^ 2), frontNormSq, add_assoc]

lemma num_nonneg {n m : ℕ} (hm : m < n) (y : Ball n) :
    0 ≤ (projA m (y : E n)) ^ 2 - frontNormSq m (y : E n) := by
  have hy : ‖(y : E n)‖ ≤ 1 := (mem_closedBall_zero_iff).mp y.2
  have hysq : ‖(y : E n)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (y : E n)]
  have hparts := norm_sq_parts hm (y : E n)
  have htail : 0 ≤ ∑ k ∈ Finset.Ico (m + 1) n, (coord (y : E n) k) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs : (coord (y : E n) m) ^ 2 = absHeight m (y : E n) ^ 2 := by
    simp [absHeight, sq_abs]
  have hlin : frontNormSq m (y : E n) + absHeight m (y : E n) ^ 2 ≤ 1 := by
    nlinarith [hparts, htail, hysq, hs]
  have hs0 : 0 ≤ absHeight m (y : E n) := absHeight_nonneg _ _
  have hgap : 0 ≤ 1 - (frontNormSq m (y : E n) + absHeight m (y : E n) ^ 2) := by
    linarith [hlin]
  calc
    (projA m (y : E n)) ^ 2 - frontNormSq m (y : E n)
        = (absHeight m (y : E n) + 1) ^ 2 - frontNormSq m (y : E n) := by
          simp [projA]
      _ = absHeight m (y : E n) ^ 2 + 2 * absHeight m (y : E n) + 1
            - frontNormSq m (y : E n) := by ring
      _ = (1 - (frontNormSq m (y : E n) + absHeight m (y : E n) ^ 2))
            + 2 * absHeight m (y : E n) ^ 2 + 2 * absHeight m (y : E n) := by ring
      _ ≥ 0 := by nlinarith [hgap, hs0]

lemma height_formula (q a : ℝ) (hd : q + a ^ 2 ≠ 0) :
    -1 + (2 * a) / (q + a ^ 2) * a = (a ^ 2 - q) / (q + a ^ 2) := by
  field_simp [hd]
  ring

lemma height_nonneg {n m : ℕ} (hm : m < n) (y : Ball n) :
    0 ≤ -1 + projT m (y : E n) * projA m (y : E n) := by
  have hform := height_formula (frontNormSq m (y : E n)) (projA m (y : E n))
    (by simpa [projDenom] using projDenom_ne m (y : E n))
  have hden : 0 ≤ frontNormSq m (y : E n) + (projA m (y : E n)) ^ 2 := by
    have h := projDenom_one_le m (y : E n)
    simp only [projDenom] at h
    linarith
  rw [show projT m (y : E n) = (2 * projA m (y : E n)) /
      (frontNormSq m (y : E n) + (projA m (y : E n)) ^ 2) from rfl, hform]
  exact div_nonneg (num_nonneg hm y) hden

lemma height_sq_complement {n m : ℕ} (hm : m < n) (y : Ball n) :
    -1 + projT m (y : E n) * projA m (y : E n) =
      Real.sqrt (1 - ‖frontVec hm (y : E n)‖ ^ 2) := by
  have hsum := front_height_one hm (y : E n)
  have hnn := height_nonneg hm y
  have hrest : 0 ≤ 1 - ‖frontVec hm (y : E n)‖ ^ 2 := by nlinarith [hsum]
  exact ((Real.sqrt_eq_iff_eq_sq hrest hnn).mpr (by nlinarith [hsum])).symm

/-- On the closed disk the projection is the source-face inclusion of its front vector. -/
lemma projectVec_eq_faceVec {n m : ℕ} (hm : m < n) (y : Ball n) :
    projectVec hm (y : E n) = faceVec m n false (frontVec hm (y : E n)) := by
  apply PiLp.ext
  intro i
  rw [projectVec_apply]
  by_cases hi : (i : ℕ) < m
  · rw [← frontVec_apply hm (y : E n) ⟨(i : ℕ), hi⟩]
    simp only [faceVec, PiLp.toLp_apply, dite_eq_left hi]
  · by_cases he : (i : ℕ) = m
    · have hpc : projectCoordN hm (y : E n) (i : ℕ) =
          -1 + projT m (y : E n) * projA m (y : E n) := by
        simp only [projectCoordN, ite_eq_right hi, ite_eq_left he]
      rw [hpc, height_sq_complement hm y]
      simp only [faceVec, PiLp.toLp_apply, dite_eq_right hi, ite_eq_left he]
      have hcoef : (if false = true then (-1 : ℝ) else 1) = 1 := by norm_num
      rw [hcoef, one_mul]
    · have hpc : projectCoordN hm (y : E n) (i : ℕ) = 0 := by
        simp only [projectCoordN, ite_eq_right hi, ite_eq_right he]
      rw [hpc]
      simp only [faceVec, PiLp.toLp_apply, dite_eq_right hi, ite_eq_right he]

/-- Coordinate formula for a globe face. -/
lemma faceVec_coord {m n : ℕ} (hm : m < n) (side : Bool) (x : E m) (k : ℕ) :
    coord (faceVec m n side x) k =
      if _hk : k < m then coord x k
      else if k = m then (if side then -1 else 1) * Real.sqrt (1 - ‖x‖ ^ 2)
      else 0 := by
  by_cases hkn : k < n
  · rw [coord_of_lt (faceVec m n side x) hkn]
    simp only [faceVec, PiLp.toLp_apply]
    by_cases hkm : k < m
    · rw [dite_eq_left hkm, dite_eq_left hkm, coord_of_lt x hkm]
    · by_cases he : k = m
      · rw [dite_eq_right hkm, dite_eq_right hkm, ite_eq_left he]
      · rw [dite_eq_right hkm, dite_eq_right hkm, ite_eq_right he]
  · rw [coord, dite_eq_right hkn]
    have hkm : ¬ k < m := by omega
    have he : k ≠ m := by omega
    rw [dite_eq_right hkm, ite_eq_right he]

lemma faceVec_coord_lt {m n : ℕ} (hm : m < n) (side : Bool) (x : E m) {k : ℕ} (hk : k < m) :
    coord (faceVec m n side x) k = coord x k := by
  simp [faceVec_coord hm side x k, hk]

lemma frontNormSq_faceVec {m n : ℕ} (hm : m < n) (side : Bool) (x : E m) :
    frontNormSq m (faceVec m n side x) = ‖x‖ ^ 2 := by
  rw [frontNormSq, EuclideanSpace.real_norm_sq_eq]
  rw [← Fin.sum_univ_eq_sum_range (fun k => (coord (faceVec m n side x) k) ^ 2) m]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [faceVec_coord_lt hm side x i.isLt, coord_of_lt x i.isLt]

lemma absHeight_faceVec_source {m n : ℕ} (hm : m < n) (x : E m) (_hx : ‖x‖ ≤ 1) :
    absHeight m (faceVec m n false x) = Real.sqrt (1 - ‖x‖ ^ 2) := by
  have hcoord := faceVec_coord hm false x m
  rw [absHeight, hcoord, dite_eq_right (lt_irrefl m), ite_eq_left rfl]
  have hcoef : (if false = true then (-1 : ℝ) else 1) = 1 := by norm_num
  rw [hcoef, one_mul, abs_of_nonneg (Real.sqrt_nonneg _)]

lemma projT_faceVec {m n : ℕ} (hm : m < n) (x : Ball m) :
    projT m (faceVec m n false (x : E m)) = 1 := by
  have hx : ‖(x : E m)‖ ≤ 1 := (mem_closedBall_zero_iff).mp x.2
  have hnn : 0 ≤ 1 - ‖(x : E m)‖ ^ 2 := by nlinarith [norm_nonneg (x : E m)]
  have hs := absHeight_faceVec_source hm (x : E m) hx
  have hq := frontNormSq_faceVec hm false (x : E m)
  have hden : ‖(x : E m)‖ ^ 2 + (Real.sqrt (1 - ‖(x : E m)‖ ^ 2) + 1) ^ 2 =
      2 * (Real.sqrt (1 - ‖(x : E m)‖ ^ 2) + 1) := by
    calc
      ‖(x : E m)‖ ^ 2 + (Real.sqrt (1 - ‖(x : E m)‖ ^ 2) + 1) ^ 2
          = ‖(x : E m)‖ ^ 2 + ((Real.sqrt (1 - ‖(x : E m)‖ ^ 2)) ^ 2
            + 2 * Real.sqrt (1 - ‖(x : E m)‖ ^ 2) + 1) := by ring
        _ = ‖(x : E m)‖ ^ 2 + (1 - ‖(x : E m)‖ ^ 2
            + 2 * Real.sqrt (1 - ‖(x : E m)‖ ^ 2) + 1) := by rw [Real.sq_sqrt hnn]
        _ = 2 * (Real.sqrt (1 - ‖(x : E m)‖ ^ 2) + 1) := by ring
  have hpos : Real.sqrt (1 - ‖(x : E m)‖ ^ 2) + 1 ≠ 0 := by
    linarith [Real.sqrt_nonneg (1 - ‖(x : E m)‖ ^ 2)]
  simp only [projT, projDenom, projA, hs, hq, hden]
  field_simp [hpos]

/-- The projection fixes the source hemisphere pointwise. -/
lemma projectVec_faceVec {m n : ℕ} (hm : m < n) (x : Ball m) :
    projectVec hm (faceVec m n false (x : E m)) = faceVec m n false (x : E m) := by
  apply PiLp.ext
  intro i
  rw [projectVec_apply, ← coord_of_lt (faceVec m n false (x : E m)) i.isLt,
    faceVec_coord hm false (x : E m) (i : ℕ)]
  have hT := projT_faceVec hm x
  have hx : ‖(x : E m)‖ ≤ 1 := (mem_closedBall_zero_iff).mp x.2
  by_cases hi : (i : ℕ) < m
  · rw [dite_eq_left hi]
    have hL : projectCoordN hm (faceVec m n false (x : E m)) (i : ℕ) =
        projT m (faceVec m n false (x : E m)) *
          coord (faceVec m n false (x : E m)) (i : ℕ) := by
      simp only [projectCoordN, ite_eq_left hi]
    rw [hL, hT, one_mul, faceVec_coord_lt hm false (x : E m) hi]
  · by_cases he : (i : ℕ) = m
    · rw [dite_eq_right hi, ite_eq_left he]
      have hL : projectCoordN hm (faceVec m n false (x : E m)) (i : ℕ) =
          -1 + projT m (faceVec m n false (x : E m)) *
            projA m (faceVec m n false (x : E m)) := by
        simp only [projectCoordN, ite_eq_right hi, ite_eq_left he]
      rw [hL, hT, one_mul, projA, absHeight_faceVec_source hm (x : E m) hx]
      have hcoef : (if false = true then (-1 : ℝ) else 1) = 1 := by norm_num
      rw [hcoef, one_mul]
      ring
    · rw [dite_eq_right hi, ite_eq_right he]
      simp only [projectCoordN, ite_eq_right hi, ite_eq_right he]

lemma faceVec_castLE {m n : ℕ} (hm : m < n) (side : Bool) (x : E m) (i : Fin m) :
    faceVec m n side x (Fin.castLE (Nat.le_of_lt hm) i) = x i := by
  have hlt : ((Fin.castLE (Nat.le_of_lt hm) i : Fin n) : ℕ) < m :=
    lt_of_eq_of_lt (Fin.val_castLE (Nat.le_of_lt hm) i).symm i.isLt
  simp only [faceVec, PiLp.toLp_apply, dite_eq_left hlt]
  exact congr_arg (fun j : Fin m => x j)
    (Fin.ext (Fin.val_castLE (Nat.le_of_lt hm) i))

lemma frontVec_faceVec {m n : ℕ} (hm : m < n) (x : Ball m) :
    frontVec hm (faceVec m n false (x : E m)) = (x : E m) := by
  apply PiLp.ext
  intro i
  have h := congr_arg (fun v : E n => v (Fin.castLE (Nat.le_of_lt hm) i))
    (projectVec_faceVec hm x)
  rw [projectVec_apply] at h
  have hcoe : ((Fin.castLE (Nat.le_of_lt hm) i : Fin n) : ℕ) = (i : ℕ) :=
    Fin.val_castLE _ _
  rw [frontVec_apply, ← hcoe, h, faceVec_castLE hm false (x : E m) i]

/-- Retraction `Bⁿ → Bᵐ` onto the coordinates of the source hemisphere. -/
def faceFront {m n : ℕ} (hm : m < n) : C(Ball n, Ball m) where
  toFun y := ⟨frontVec hm (y : E n), frontVec_mem hm (y : E n)⟩
  continuous_toFun := by
    have hcont : Continuous (fun y : Ball n => frontVec hm (y : E n)) :=
      (continuous_frontVec hm).comp
        (continuous_subtype_val : Continuous (fun y : Ball n => (y : E n)))
    exact Continuous.subtype_mk hcont (fun y => frontVec_mem hm (y : E n))

/-- The source hemisphere, as a self-map of `Bⁿ`. -/
def faceRetract {m n : ℕ} (hm : m < n) : C(Ball n, Ball n) :=
  (ballFace hm false).comp (faceFront hm)

lemma faceRetract_eq_projectVec {m n : ℕ} (hm : m < n) (y : Ball n) :
    ((faceRetract hm y : Ball n) : E n) = projectVec hm (y : E n) := by
  simp only [faceRetract, ContinuousMap.comp_apply, ballFace, faceFront]
  exact (projectVec_eq_faceVec hm y).symm

/-- The front retraction is a section of the source face. -/
lemma faceFront_section {m n : ℕ} (hm : m < n) :
    (faceFront hm).comp (ballFace hm false) = ContinuousMap.id (Ball m) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact frontVec_faceVec hm x

lemma faceRetract_face {m n : ℕ} (hm : m < n) (a : Ball m) :
    faceRetract hm (ballFace hm false a) = ballFace hm false a := by
  have hs := faceFront_section hm
  change ((ballFace hm false).comp (faceFront hm)) (ballFace hm false a) = _
  rw [← ContinuousMap.comp_apply, ContinuousMap.comp_assoc, hs, ContinuousMap.comp_id]

/-- Straight-line combination in `ℝⁿ`. -/
def seg {n : ℕ} (t : ℝ) (y r : E n) : E n := (1 - t) • y + t • r

lemma seg_zero {n : ℕ} (y r : E n) : seg 0 y r = y := by
  simp [seg]

lemma seg_one {n : ℕ} (y r : E n) : seg 1 y r = r := by
  simp [seg]

lemma seg_same {n : ℕ} (t : ℝ) (y : E n) : seg t y y = y := by
  simp only [seg]
  rw [← add_smul, sub_add_cancel, one_smul]

lemma seg_mem {n : ℕ} (y r : Ball n) (t : unitInterval) :
    seg (t : ℝ) (y : E n) (r : E n) ∈ Metric.closedBall (0 : E n) 1 := by
  exact (convex_iff_add_mem.mp (convex_closedBall (0 : E n) 1)) y.2 r.2
    (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel _ _)

/-- Straight-line strong deformation retraction of the disk onto the source hemisphere. -/
def faceDeformation {m n : ℕ} (hm : m < n) :
    Homotopy (ContinuousMap.id (Ball n)) (faceRetract hm) where
  toFun p := ⟨seg (p.1 : ℝ) (p.2 : E n) ((faceRetract hm p.2 : Ball n) : E n),
    seg_mem p.2 (faceRetract hm p.2) p.1⟩
  continuous_toFun := by
    have hval : Continuous (fun y : Ball n => (y : E n)) := continuous_subtype_val
    have hfst : Continuous (fun p : unitInterval × Ball n => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hsnd : Continuous (fun p : unitInterval × Ball n => (p.2 : E n)) :=
      hval.comp continuous_snd
    have hr : Continuous (fun p : unitInterval × Ball n =>
        ((faceRetract hm p.2 : Ball n) : E n)) :=
      hval.comp ((faceRetract hm).continuous.comp continuous_snd)
    have hmap : Continuous (fun p : unitInterval × Ball n =>
        seg (p.1 : ℝ) (p.2 : E n) ((faceRetract hm p.2 : Ball n) : E n)) :=
      ((continuous_const.sub hfst).smul hsnd).add (hfst.smul hr)
    exact Continuous.subtype_mk hmap fun p => seg_mem p.2 (faceRetract hm p.2) p.1
  map_zero_left y := by
    apply Subtype.ext
    dsimp
    rw [seg_zero]
  map_one_left y := by
    apply Subtype.ext
    dsimp
    rw [seg_one]

lemma faceDeformation_apply {m n : ℕ} (hm : m < n) (p : unitInterval × Ball n) :
    (faceDeformation hm p : Ball n) =
      ⟨seg (p.1 : ℝ) (p.2 : E n) ((faceRetract hm p.2 : Ball n) : E n),
        seg_mem p.2 (faceRetract hm p.2) p.1⟩ :=
  rfl

lemma faceDeformation_fixes {m n : ℕ} (hm : m < n) (t : unitInterval) (a : Ball m) :
    faceDeformation hm (t, ballFace hm false a) = ballFace hm false a := by
  apply Subtype.ext
  rw [faceDeformation_apply]
  change seg (t : ℝ) ((ballFace hm false a : Ball n) : E n)
      ((faceRetract hm (ballFace hm false a) : Ball n) : E n) =
    ((ballFace hm false a : Ball n) : E n)
  rw [faceRetract_face hm a, seg_same]

end HomotopyHypothesis.Realization.Disk
