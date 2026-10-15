import HomotopyHypothesis.Challenge
import HomotopyHypothesis.Realization.Cellular.DiskCoordinates
import HomotopyHypothesis.Realization.Cellular.EndpointLifting
import HomotopyHypothesis.Realization.Cellular.SpherePushout
noncomputable section

open CategoryTheory Limits Topology

namespace HomotopyHypothesis.Realization.Cellular

/-- Replace the last coordinate, leaving the preceding coordinates fixed. -/
def withLast {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) (z : ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.lastCases z fun i => x i.castSucc)

@[simp] theorem dropLast_withLast {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) (z : ℝ) :
    dropLast (withLast x z) = dropLast x := by
  ext i
  simp [dropLast, withLast]

@[simp] theorem last_withLast {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) (z : ℝ) :
    withLast x z (Fin.last n) = z := by simp [withLast]

theorem continuous_withLast (n : ℕ) :
    Continuous (fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ => withLast p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last]
    exact continuous_snd
  · simp only [Fin.lastCases_castSucc]
    exact (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) j.castSucc).comp continuous_fst

/-- The amount of vertical movement used to extend a homotopy from a hemisphere. -/
def capShift {n : ℕ} (p : Ball (n + 1) × unitInterval) : ℝ :=
  min (capGap p.1 / 8) (min (p.2 : ℝ) (1 - p.2))

theorem capShift_bounds {n : ℕ} (p : Ball (n + 1) × unitInterval) :
    0 ≤ capShift p ∧ capShift p ≤ 1 / 4 ∧ capShift p ≤ capGap p.1 / 8 ∧
      capShift p ≤ p.2 ∧ capShift p ≤ 1 - p.2 := by
  have hg := capGap_bounds p.1
  have ht := p.2.2
  have ht₁ : (p.2 : ℝ) ≤ 1 := p.2.2.2
  have h₁ : capShift p ≤ capGap p.1 / 8 := min_le_left _ _
  have h₂ : capShift p ≤ min (p.2 : ℝ) (1 - p.2) := min_le_right _ _
  refine ⟨le_min (by linarith) (le_min ht.1 (by linarith)), by linarith, h₁,
    h₂.trans (min_le_left _ _), h₂.trans (min_le_right _ _)⟩

theorem continuous_capShift (n : ℕ) :
    Continuous (capShift : Ball (n + 1) × unitInterval → ℝ) :=
  (((continuous_capGap n).comp continuous_fst).div_const 8).min
    ((continuous_subtype_val.comp continuous_snd).min
      (continuous_const.sub (continuous_subtype_val.comp continuous_snd)))

/-- Move a point vertically, stopping at the hemisphere or at a time endpoint. -/
def capSlide {n : ℕ} : C(Ball (n + 1) × unitInterval, Ball (n + 1)) where
  toFun p := ⟨withLast p.1.1 (p.1.1 (Fin.last n) + 8 * capShift p), by
    rw [mem_closedBall_zero_iff]
    have hs := capShift_bounds p
    have hb := last_bounds p.1
    have hq := capHeight_sq p.1
    have hnorm := norm_sq_dropLast
      (withLast p.1.1 (p.1.1 (Fin.last n) + 8 * capShift p))
    simp only [dropLast_withLast, last_withLast] at hnorm
    have hz : p.1.1 (Fin.last n) + 8 * capShift p ≤ capHeight p.1 := by
      have := hs.2.2.1
      dsimp [capGap] at this
      linarith
    nlinarith [capHeight_nonneg p.1,
      norm_nonneg (withLast p.1.1 (p.1.1 (Fin.last n) + 8 * capShift p))]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_withLast n).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (((PiLp.continuous_apply 2 _ (Fin.last n)).comp
          (continuous_subtype_val.comp continuous_fst)).add
            (continuous_const.mul (continuous_capShift n))))

/-- Rescaled time after the vertical movement. -/
def capTime {n : ℕ} : C(Ball (n + 1) × unitInterval, unitInterval) where
  toFun p := ⟨((p.2 : ℝ) - capShift p) / (1 - 2 * capShift p), by
    have h := capShift_bounds p
    have hd : 0 < 1 - 2 * capShift p := by linarith
    exact ⟨div_nonneg (by linarith [h.2.2.2.1]) hd.le,
      (div_le_one hd).mpr (by linarith [h.2.2.2.2])⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.div
    · exact (continuous_subtype_val.comp continuous_snd).sub (continuous_capShift n)
    · exact continuous_const.sub (continuous_const.mul (continuous_capShift n))
    · intro p
      have := (capShift_bounds p).2.1
      linarith

@[simp] theorem capSlide_zero {n : ℕ} (x : Ball (n + 1)) : capSlide (x, 0) = x := by
  have hz : capShift (x, 0) = 0 := by
    have := capShift_bounds (x, 0)
    simp only [Set.Icc.coe_zero] at this
    linarith [this.2.2.2.1]
  apply Subtype.ext
  apply euclidean_ext_dropLast_last
  · exact dropLast_withLast _ _
  · change withLast x.1 (x.1 (Fin.last n) + 8 * capShift (x, 0)) (Fin.last n) = _
    simp [hz]

@[simp] theorem capSlide_one {n : ℕ} (x : Ball (n + 1)) : capSlide (x, 1) = x := by
  have hz : capShift (x, 1) = 0 := by
    have := capShift_bounds (x, 1)
    simp only [Set.Icc.coe_one, sub_self] at this
    linarith [this.2.2.2.2]
  apply Subtype.ext
  apply euclidean_ext_dropLast_last
  · exact dropLast_withLast _ _
  · change withLast x.1 (x.1 (Fin.last n) + 8 * capShift (x, 1)) (Fin.last n) = _
    simp [hz]

theorem capSlide_top {n : ℕ} (p : Ball (n + 1) × unitInterval)
    (h : capShift p = capGap p.1 / 8) :
    capSlide p = ballFace (Nat.lt_succ_self n) false (diskProject p.1) := by
  apply Subtype.ext
  apply euclidean_ext_dropLast_last
  · simp [capSlide, ballFace, diskProject]
  · change withLast p.1.1 (p.1.1 (Fin.last n) + 8 * capShift p) (Fin.last n) =
      faceVec n (n + 1) false (dropLast p.1.1) (Fin.last n)
    rw [last_withLast, last_faceVec]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    change p.1.1 (Fin.last n) + 8 * capShift p = capHeight p.1
    rw [h]
    dsimp [capGap]
    ring

theorem capTime_zero {n : ℕ} (p : Ball (n + 1) × unitInterval)
    (h : capShift p = (p.2 : ℝ)) : capTime p = 0 := by
  apply Subtype.ext
  change ((p.2 : ℝ) - capShift p) / _ = 0
  rw [h, sub_self, zero_div]

theorem capTime_one {n : ℕ} (p : Ball (n + 1) × unitInterval)
    (h : capShift p = 1 - (p.2 : ℝ)) : capTime p = 1 := by
  have hd : 1 - 2 * capShift p ≠ 0 := by have := (capShift_bounds p).2.1; linarith
  apply Subtype.ext
  change ((p.2 : ℝ) - capShift p) / (1 - 2 * capShift p) = 1
  apply (div_eq_one_iff_eq hd).mpr
  linarith

/-- A homotopy on an upper hemisphere extends with prescribed endpoint maps. -/
theorem hemisphere_path_extension {Y : Type*} [TopologicalSpace Y] (n : ℕ)
    (a : C(Ball n × unitInterval, Y)) (b₀ b₁ : C(Ball (n + 1), Y))
    (h₀ : ∀ x, a (x, 0) = b₀ (ballFace (Nat.lt_succ_self n) false x))
    (h₁ : ∀ x, a (x, 1) = b₁ (ballFace (Nat.lt_succ_self n) false x)) :
    ∃ H : C(Ball (n + 1) × unitInterval, Y),
      (∀ x t, H (ballFace (Nat.lt_succ_self n) false x, t) = a (x, t)) ∧
      (∀ x, H (x, 0) = b₀ x) ∧ (∀ x, H (x, 1) = b₁ x) := by
  classical
  let u : Ball (n + 1) × unitInterval → ℝ := fun p => capGap p.1 / 8
  have hu : Continuous u := ((continuous_capGap n).comp continuous_fst).div_const 8
  have hub (p : Ball (n + 1) × unitInterval) : 0 ≤ u p ∧ u p ≤ 1 / 4 := by
    have := capGap_bounds p.1
    dsimp [u]
    constructor <;> linarith
  let middle : C(Ball (n + 1) × unitInterval, Y) :=
    a.comp ((diskProject.comp ContinuousMap.fst).prodMk capTime)
  let bottom : C(Ball (n + 1) × unitInterval, Y) := b₀.comp capSlide
  let top : C(Ball (n + 1) × unitInterval, Y) := b₁.comp capSlide
  have hshift (p : Ball (n + 1) × unitInterval)
      (hleft : u p ≤ p.2) (hright : u p ≤ 1 - p.2) : capShift p = u p := by
    exact min_eq_left (le_min hleft hright)
  have hc₁ : Continuous (fun p : Ball (n + 1) × unitInterval =>
      if 1 - (p.2 : ℝ) ≤ u p then top p else middle p) := by
    apply top.continuous.if_le middle.continuous
      (continuous_const.sub (continuous_subtype_val.comp continuous_snd)) hu
    intro p hp
    change 1 - (p.2 : ℝ) = u p at hp
    have ht := p.2.2
    have hsh : capShift p = u p := hshift p (by linarith [(hub p).2]) (by linarith)
    have htm : capTime p = 1 := capTime_one p (by rw [hsh]; linarith)
    change b₁ (capSlide p) = a (diskProject p.1, capTime p)
    rw [capSlide_top p hsh, htm]
    exact (h₁ _).symm
  have hc : Continuous (fun p : Ball (n + 1) × unitInterval =>
      if (p.2 : ℝ) ≤ u p then bottom p
      else if 1 - (p.2 : ℝ) ≤ u p then top p else middle p) := by
    apply bottom.continuous.if_le hc₁ (continuous_subtype_val.comp continuous_snd) hu
    intro p hp
    change (p.2 : ℝ) = u p at hp
    have hh : ¬ 1 - (p.2 : ℝ) ≤ u p := by linarith [(hub p).2]
    rw [if_neg hh]
    have hsh : capShift p = u p := hshift p (by linarith) (by linarith [(hub p).2])
    have htm : capTime p = 0 := capTime_zero p (by rw [hsh]; linarith)
    change b₀ (capSlide p) = a (diskProject p.1, capTime p)
    rw [capSlide_top p hsh, htm]
    exact (h₀ _).symm
  let H : C(Ball (n + 1) × unitInterval, Y) := ⟨_, hc⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · intro x t
    have huf : u (ballFace (Nat.lt_succ_self n) false x, t) = 0 := by simp [u]
    have hsh : capShift (ballFace (Nat.lt_succ_self n) false x, t) = 0 := by
      have := capShift_bounds (ballFace (Nat.lt_succ_self n) false x, t)
      have hh := capGap_face n x
      rw [hh] at this
      linarith [this.2.2.1]
    have htm : capTime (ballFace (Nat.lt_succ_self n) false x, t) = t := by
      apply Subtype.ext
      change ((t : ℝ) - capShift _) / (1 - 2 * capShift _) = t
      simp [hsh]
    change (if (t : ℝ) ≤ u _ then bottom _ else if 1 - (t : ℝ) ≤ u _ then top _ else middle _) = _
    rw [huf]
    split_ifs with ht ht'
    · have heq : t = 0 := Subtype.ext (by change (t : ℝ) = 0; linarith [t.2.1])
      subst t
      exact (congrArg b₀ (capSlide_zero _)).trans (h₀ x).symm
    · have heq : t = 1 := Subtype.ext (by change (t : ℝ) = 1; linarith [t.2.2])
      subst t
      exact (congrArg b₁ (capSlide_one _)).trans (h₁ x).symm
    · change a (diskProject (ballFace (Nat.lt_succ_self n) false x), capTime _) = _
      rw [diskProject_face, htm]
  · intro x
    change (if (0 : ℝ) ≤ u (x, 0) then bottom (x, 0)
      else if 1 - (0 : ℝ) ≤ u (x, 0) then top (x, 0) else middle (x, 0)) = _
    rw [if_pos (hub (x, 0)).1]
    exact congrArg b₀ (capSlide_zero x)
  · intro x
    have hh : ¬ (1 : ℝ) ≤ u (x, 1) := by linarith [(hub (x, 1)).2]
    change (if (1 : ℝ) ≤ u (x, 1) then bottom (x, 1)
      else if 1 - (1 : ℝ) ≤ u (x, 1) then top (x, 1) else middle (x, 1)) = _
    rw [if_neg hh, if_pos (by linarith [(hub (x, 1)).1])]
    exact congrArg b₁ (capSlide_one x)

end HomotopyHypothesis.Realization.Cellular
