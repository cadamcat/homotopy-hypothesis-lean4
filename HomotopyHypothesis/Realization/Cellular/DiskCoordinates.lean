import HomotopyHypothesis.Challenge
noncomputable section

open CategoryTheory Limits Topology

namespace HomotopyHypothesis.Realization.Cellular

/-- The first coordinates of a Euclidean vector. -/
def dropLast {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => x i.castSucc

@[simp] theorem dropLast_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    dropLast x i = x i.castSucc := rfl

theorem continuous_dropLast (n : ℕ) :
    Continuous (dropLast : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n)) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
    PiLp.continuous_apply 2 _ i.castSucc)

theorem norm_sq_dropLast {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖dropLast x‖ ^ 2 + (x (Fin.last n)) ^ 2 = ‖x‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, dropLast_apply]
  exact (Fin.sum_univ_castSucc (fun i : Fin (n + 1) => (x i) ^ 2)).symm

theorem dropLast_norm_le {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖dropLast x‖ ≤ ‖x‖ := by
  have := norm_sq_dropLast x
  nlinarith [norm_nonneg (dropLast x), norm_nonneg x, sq_nonneg (x (Fin.last n))]

/-- Projection of a disk onto its first coordinates. -/
def diskProject {n : ℕ} : C(Ball (n + 1), Ball n) where
  toFun x := ⟨dropLast x.1, mem_closedBall_zero_iff.mpr
    ((dropLast_norm_le x.1).trans (mem_closedBall_zero_iff.mp x.2))⟩
  continuous_toFun := ((continuous_dropLast n).comp continuous_subtype_val).subtype_mk _

@[simp] theorem dropLast_faceVec (n : ℕ) (b : Bool) (x : EuclideanSpace ℝ (Fin n)) :
    dropLast (faceVec n (n + 1) b x) = x := by
  ext i
  simp [dropLast, faceVec, i.isLt]

@[simp] theorem last_faceVec (n : ℕ) (b : Bool) (x : EuclideanSpace ℝ (Fin n)) :
    faceVec n (n + 1) b x (Fin.last n) =
      (if b then -1 else 1) * Real.sqrt (1 - ‖x‖ ^ 2) := by
  simp [faceVec]

@[simp] theorem diskProject_face (n : ℕ) (b : Bool) (x : Ball n) :
    diskProject (ballFace (Nat.lt_succ_self n) b x) = x := by
  apply Subtype.ext
  exact dropLast_faceVec n b x.1

/-- The nonnegative height of the upper hemisphere over the first coordinates. -/
def capHeight {n : ℕ} (x : Ball (n + 1)) : ℝ := Real.sqrt (1 - ‖dropLast x.1‖ ^ 2)

theorem continuous_capHeight (n : ℕ) : Continuous (capHeight : Ball (n + 1) → ℝ) :=
  (continuous_const.sub (((continuous_dropLast n).comp continuous_subtype_val).norm.pow 2)).sqrt

theorem capHeight_nonneg {n : ℕ} (x : Ball (n + 1)) : 0 ≤ capHeight x :=
  Real.sqrt_nonneg _

theorem capHeight_sq {n : ℕ} (x : Ball (n + 1)) :
    capHeight x ^ 2 = 1 - ‖dropLast x.1‖ ^ 2 := by
  apply Real.sq_sqrt
  have := mem_closedBall_zero_iff.mp (diskProject x).2
  change ‖dropLast x.1‖ ≤ 1 at this
  nlinarith [norm_nonneg (dropLast x.1)]

theorem capHeight_le_one {n : ℕ} (x : Ball (n + 1)) : capHeight x ≤ 1 := by
  have := capHeight_sq x
  nlinarith [capHeight_nonneg x, sq_nonneg ‖dropLast x.1‖]

theorem last_bounds {n : ℕ} (x : Ball (n + 1)) :
    -capHeight x ≤ x.1 (Fin.last n) ∧ x.1 (Fin.last n) ≤ capHeight x := by
  have := norm_sq_dropLast x.1
  have hx := mem_closedBall_zero_iff.mp x.2
  have hc := capHeight_sq x
  have hn := capHeight_nonneg x
  constructor <;> nlinarith [norm_nonneg x.1]

@[simp] theorem capHeight_face (n : ℕ) (b : Bool) (x : Ball n) :
    capHeight (ballFace (Nat.lt_succ_self n) b x) = Real.sqrt (1 - ‖x.1‖ ^ 2) := by
  simp [capHeight, ballFace]

/-- The vertical gap to the upper hemisphere. -/
def capGap {n : ℕ} (x : Ball (n + 1)) : ℝ := capHeight x - x.1 (Fin.last n)

theorem capGap_bounds {n : ℕ} (x : Ball (n + 1)) : 0 ≤ capGap x ∧ capGap x ≤ 2 := by
  have := last_bounds x
  have := capHeight_le_one x
  dsimp [capGap]
  constructor <;> linarith

theorem continuous_capGap (n : ℕ) : Continuous (capGap : Ball (n + 1) → ℝ) :=
  (continuous_capHeight n).sub ((PiLp.continuous_apply 2 _ (Fin.last n)).comp
    continuous_subtype_val)

@[simp] theorem capGap_face (n : ℕ) (x : Ball n) :
    capGap (ballFace (Nat.lt_succ_self n) false x) = 0 := by
  rw [capGap, capHeight_face]
  simp [ballFace]

end HomotopyHypothesis.Realization.Cellular
