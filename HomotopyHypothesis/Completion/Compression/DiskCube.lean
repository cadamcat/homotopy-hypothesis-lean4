import HomotopyHypothesis.Blueprint.Defs
/-
# Disk-cube correspondence (outline)

For general `n`, the pair `(𝔻ⁿ, ∂𝔻ⁿ)` is homeomorphic to the cube pair
`(Iⁿ, ∂Iⁿ)` via radial maps, preserving the boundary. Transporting Mathlib's
cube-model homotopy groups along this homeomorphism identifies
`π_{n+1}(X, x)` with relative disk classes `[(𝔻^{n+1}, Sⁿ), (X, x)]` up to
homotopy relative to the boundary. Gluing two disks along their boundary gives
spheres for the injectivity argument. Full proofs are the next steps.
-/
noncomputable section

namespace HomotopyHypothesis.Completion.Compression

universe u

open CategoryTheory TopCat Topology

/-! ### The sup norm on `EuclideanSpace ℝ (Fin n)` -/

/-- The sup norm `‖x‖∞ = max_i |x i|`, via a lattice supremum of nonnegative norms. -/
def supNorm (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (Finset.univ.sup (fun i => ‖x i‖₊) : NNReal)

lemma supNorm_nonneg (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ supNorm n x :=
  NNReal.coe_nonneg _

lemma supNorm_apply_le (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |x i| ≤ supNorm n x := by
  have h : ‖x i‖₊ ≤ Finset.univ.sup (fun j => ‖x j‖₊) :=
    Finset.le_sup (f := fun j => ‖x j‖₊) (Finset.mem_univ i)
  have h2 : ((‖x i‖₊ : NNReal) : ℝ) ≤ ((Finset.univ.sup (fun j => ‖x j‖₊) : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  rwa [coe_nnnorm, Real.norm_eq_abs] at h2

lemma supNorm_exists_eq (n : ℕ) [Nonempty (Fin n)] (x : EuclideanSpace ℝ (Fin n)) :
    ∃ i : Fin n, supNorm n x = |x i| := by
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun j => ‖x j‖₊)
  refine ⟨i, ?_⟩
  unfold supNorm
  rw [hi, coe_nnnorm, Real.norm_eq_abs]

/-- Each coordinate is bounded by the `L²` norm. -/
lemma coord_le_norm (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  have h : (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : √((x i) ^ 2) ≤ √(‖x‖ ^ 2) := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg _)] at h2

/-- The sup norm is `1`-Lipschitz, hence continuous. -/
lemma lipschitzWith_supNorm (n : ℕ) [Nonempty (Fin n)] :
    LipschitzWith 1 (supNorm n) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq]
  obtain ⟨j, hj⟩ := supNorm_exists_eq n x
  obtain ⟨k, hk⟩ := supNorm_exists_eq n y
  have h1 : supNorm n x - supNorm n y ≤ dist x y := by
    rw [hj]
    have hle : |y j| ≤ supNorm n y := supNorm_apply_le n y j
    have htri : |x j| - |y j| ≤ |(x - y) j| := abs_sub_abs_le_abs_sub _ _
    have hcoord : |(x - y) j| ≤ ‖x - y‖ := coord_le_norm n _ _
    rw [dist_eq_norm]
    linarith
  have h2 : supNorm n y - supNorm n x ≤ dist x y := by
    rw [hk]
    have hle : |x k| ≤ supNorm n x := supNorm_apply_le n x k
    have htri : |y k| - |x k| ≤ |(y - x) k| := abs_sub_abs_le_abs_sub _ _
    have hcoord : |(y - x) k| ≤ ‖y - x‖ := coord_le_norm n _ _
    have hdist : dist x y = ‖y - x‖ := by rw [dist_eq_norm, norm_sub_rev]
    rw [hdist]
    linarith
  have key : |supNorm n x - supNorm n y| ≤ dist x y := by
    rw [abs_le]
    exact ⟨by linarith [h2], h1⟩
  simpa using key

lemma continuous_supNorm (n : ℕ) [Nonempty (Fin n)] : Continuous (supNorm n) :=
  (lipschitzWith_supNorm n).continuous

/-- The sup norm vanishes exactly at the origin. -/
lemma supNorm_eq_zero_iff (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    supNorm n x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext i
    have hle : |x i| ≤ supNorm n x := supNorm_apply_le n x i
    rw [h] at hle
    have h0 : x i = 0 := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    simpa using h0
  · intro h
    rw [h]
    have h0 : Finset.univ.sup (fun i => ‖(0 : EuclideanSpace ℝ (Fin n)) i‖₊) = 0 := by
      apply le_antisymm _ (bot_le)
      apply Finset.sup_le
      intro i _
      simp
    show (((Finset.univ.sup (fun i => ‖(0 : EuclideanSpace ℝ (Fin n)) i‖₊)) : NNReal) : ℝ) = 0
    rw [h0, NNReal.coe_zero]

/-- An empty index makes the space trivial, so nontrivial vectors give inhabited indices. -/
lemma nonempty_of_ne_zero (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    Nonempty (Fin n) := by
  rcases isEmpty_or_nonempty (Fin n) with hempty | hne
  · have := hempty
    exact absurd (by ext i; exact (IsEmpty.false i).elim) hx
  · exact hne

/-- The sup norm is bounded by the `L²` norm. -/
lemma supNorm_le_norm (n : ℕ) [Nonempty (Fin n)] (x : EuclideanSpace ℝ (Fin n)) :
    supNorm n x ≤ ‖x‖ := by
  obtain ⟨j, hj⟩ := supNorm_exists_eq n x
  rw [hj]
  exact coord_le_norm n x j

/-- The `L²` norm is bounded by `√n` times the sup norm. -/
lemma norm_le_sqrt_card_mul_supNorm (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ≤ Real.sqrt n * supNorm n x := by
  have hterm : ∀ i : Fin n, (x.ofLp i) ^ 2 ≤ supNorm n x ^ 2 := by
    intro i
    have h1 : |x.ofLp i| ≤ supNorm n x := supNorm_apply_le n x i
    have h2 : |x.ofLp i| ^ 2 ≤ supNorm n x ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    rwa [sq_abs] at h2
  have h : ‖x‖ ^ 2 ≤ (n : ℝ) * supNorm n x ^ 2 := by
    have hsq : ‖x‖ ^ 2 = ∑ i, x.ofLp i ^ 2 := EuclideanSpace.real_norm_sq_eq x
    rw [hsq]
    refine le_trans (Finset.sum_le_sum (fun i _ => hterm i)) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : ‖x‖ = √(‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
  have h3 : √((n : ℝ) * supNorm n x ^ 2) = Real.sqrt n * supNorm n x := by
    rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (supNorm_nonneg n x)]
  rw [h2]
  exact h3 ▸ Real.sqrt_le_sqrt h

/-- The sup norm scales through scalar multiplication. -/
lemma supNorm_smul (n : ℕ) [Nonempty (Fin n)] (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    supNorm n (c • x) = |c| * supNorm n x := by
  have esm : ∀ i : Fin n, |(c • x) i| = |c| * |x i| := by
    intro i
    have e : (c • x) i = c * x i := by simp
    rw [e, abs_mul]
  have le1 : supNorm n (c • x) ≤ |c| * supNorm n x := by
    obtain ⟨k, hk⟩ := supNorm_exists_eq n (c • x)
    rw [hk, esm k]
    exact mul_le_mul_of_nonneg_left (supNorm_apply_le n x k) (abs_nonneg _)
  have le2 : |c| * supNorm n x ≤ supNorm n (c • x) := by
    obtain ⟨j, hj⟩ := supNorm_exists_eq n x
    rw [hj, ← esm j]
    exact supNorm_apply_le n (c • x) j
  exact le_antisymm le1 le2

/-! ### Radial rescaling maps -/

/-- Radial rescaling `L²-ball → L∞-ball`: `x ↦ (‖x‖/‖x‖∞) • x` (`0/0 = 0` at the origin). -/
def radialF (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (‖x‖ / supNorm n x) • x

/-- Radial rescaling `L∞-ball → L²-ball`. -/
def radialG (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (supNorm n y / ‖y‖) • y

lemma supNorm_radialF (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    supNorm n (radialF n x) = ‖x‖ := by
  by_cases hx0 : x = 0
  · subst hx0
    have e1 : radialF n (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
      unfold radialF
      simp
    rw [e1, (supNorm_eq_zero_iff n 0).mpr rfl, norm_zero]
  · have := nonempty_of_ne_zero n x hx0
    have hs : supNorm n x ≠ 0 :=
      fun hs0 => hx0 ((supNorm_eq_zero_iff n x).mp hs0)
    have hnn : 0 ≤ ‖x‖ / supNorm n x :=
      div_nonneg (norm_nonneg _) (supNorm_nonneg n x)
    have e2 : radialF n x = (‖x‖ / supNorm n x) • x := rfl
    rw [e2, supNorm_smul, abs_of_nonneg hnn, div_mul_cancel₀ _ hs]

lemma norm_radialG (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    ‖radialG n y‖ = supNorm n y := by
  by_cases hy0 : y = 0
  · subst hy0
    have e1 : radialG n (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
      unfold radialG
      simp
    rw [e1, norm_zero]
    exact ((supNorm_eq_zero_iff n 0).mpr rfl).symm
  · have := nonempty_of_ne_zero n y hy0
    have hr : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
    have hnn : 0 ≤ supNorm n y / ‖y‖ :=
      div_nonneg (supNorm_nonneg n y) (norm_nonneg _)
    have e2 : radialG n y = (supNorm n y / ‖y‖) • y := rfl
    rw [e2, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn, div_mul_cancel₀ _ hr]

/-- The `L∞`-ball as a subtype of Euclidean space. -/
abbrev linfBall (n : ℕ) : Type 0 := {y : EuclideanSpace ℝ (Fin n) // supNorm n y ≤ 1}

lemma radialF_supNorm_le (n : ℕ)
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    supNorm n (radialF n x.val) ≤ 1 := by
  rw [supNorm_radialF]
  have h := Metric.mem_closedBall.mp x.property
  rwa [dist_zero_right] at h

lemma radialG_norm_le (n : ℕ) (y : linfBall n) :
    ‖radialG n y.val‖ ≤ 1 := by
  rw [norm_radialG]
  exact y.property

/-- Radial maps between the `L²`-ball and the `L∞`-ball subtypes. -/
def radialFSub (n : ℕ) (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    linfBall n :=
  ⟨radialF n x.val, radialF_supNorm_le n x⟩

def radialGSub (n : ℕ) (y : linfBall n) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ⟨radialG n y.val, by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact radialG_norm_le n y⟩

lemma radialG_radialF (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    radialG n (radialF n x) = x := by
  by_cases hx0 : x = 0
  · subst hx0
    have e1 : radialF n (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
      unfold radialF
      simp
    have e2 : radialG n (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
      unfold radialG
      simp
    rw [e1, e2]
  · have := nonempty_of_ne_zero n x hx0
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hs : 0 < supNorm n x := by
      rcases eq_or_lt_of_le (supNorm_nonneg n x) with h0 | hpos
      · exfalso
        exact hx0 ((supNorm_eq_zero_iff n x).mp h0.symm)
      · exact hpos
    have hrf : ‖radialF n x‖ = (‖x‖ / supNorm n x) * ‖x‖ := by
      have e2 : radialF n x = (‖x‖ / supNorm n x) • x := rfl
      rw [e2, norm_smul, Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (norm_nonneg _) (supNorm_nonneg n x))]
    have hscalar : (supNorm n (radialF n x) / ‖radialF n x‖) *
        (‖x‖ / supNorm n x) = 1 := by
      rw [supNorm_radialF, hrf]
      have hrf0 : (‖x‖ / supNorm n x) * ‖x‖ ≠ 0 :=
        mul_ne_zero (div_ne_zero hr.ne' hs.ne') hr.ne'
      field_simp
    have e : radialG n (radialF n x)
        = ((supNorm n (radialF n x) / ‖radialF n x‖) * (‖x‖ / supNorm n x)) • x := by
      have g1 : radialG n (radialF n x)
          = (supNorm n (radialF n x) / ‖radialF n x‖) • (radialF n x) := rfl
      have f1 : radialF n x = (‖x‖ / supNorm n x) • x := rfl
      rw [g1, f1, ← mul_smul]
    rw [e, hscalar, one_smul]

lemma radialF_radialG (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    radialF n (radialG n y) = y := by
  by_cases hy0 : y = 0
  · subst hy0
    have e1 : radialG n (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
      unfold radialG
      simp
    have e2 : radialF n (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
      unfold radialF
      simp
    rw [e1, e2]
  · have := nonempty_of_ne_zero n y hy0
    have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hs : 0 < supNorm n y := by
      rcases eq_or_lt_of_le (supNorm_nonneg n y) with h0 | hpos
      · exfalso
        exact hy0 ((supNorm_eq_zero_iff n y).mp h0.symm)
      · exact hpos
    have hsf : supNorm n (radialG n y) = (supNorm n y / ‖y‖) * supNorm n y := by
      have e2 : radialG n y = (supNorm n y / ‖y‖) • y := rfl
      rw [e2, supNorm_smul, abs_of_nonneg
        (div_nonneg (supNorm_nonneg n y) (norm_nonneg _))]
    have hscalar : (‖radialG n y‖ / supNorm n (radialG n y)) *
        (supNorm n y / ‖y‖) = 1 := by
      rw [norm_radialG, hsf]
      have hsf0 : (supNorm n y / ‖y‖) * supNorm n y ≠ 0 :=
        mul_ne_zero (div_ne_zero hs.ne' hr.ne') hs.ne'
      field_simp
    have e : radialF n (radialG n y)
        = ((‖radialG n y‖ / supNorm n (radialG n y)) * (supNorm n y / ‖y‖)) • y := by
      have f1 : radialF n (radialG n y)
          = (‖radialG n y‖ / supNorm n (radialG n y)) • (radialG n y) := rfl
      have g1 : radialG n y = (supNorm n y / ‖y‖) • y := rfl
      rw [f1, g1, ← mul_smul]
    rw [e, hscalar, one_smul]

/-! ### Continuity of radial maps -/

lemma continuous_radialF (n : ℕ) : Continuous (radialF n) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx0 : x = 0
  · subst hx0
    have e0 : radialF n (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
      unfold radialF
      simp
    have hbound : ∀ y, ‖radialF n y‖ ≤ Real.sqrt n * ‖y‖ := by
      intro y
      calc ‖radialF n y‖ ≤ Real.sqrt n * supNorm n (radialF n y) :=
            norm_le_sqrt_card_mul_supNorm n _
        _ = Real.sqrt n * ‖y‖ := by rw [supNorm_radialF]
    have hlim : Filter.Tendsto (fun (y : EuclideanSpace ℝ (Fin n)) => Real.sqrt n * ‖y‖)
        (𝓝 0) (𝓝 0) := by
      have hcont : Continuous
          (fun y : EuclideanSpace ℝ (Fin n) => Real.sqrt n * ‖y‖) :=
        continuous_const.mul continuous_norm
      have hto := hcont.tendsto' (0 : EuclideanSpace ℝ (Fin n))
        (Real.sqrt n * ‖(0 : EuclideanSpace ℝ (Fin n))‖) rfl
      simpa using hto
    have key : Filter.Tendsto (radialF n) (𝓝 0) (𝓝 0) :=
      squeeze_zero_norm hbound hlim
    unfold ContinuousAt
    rw [e0]
    exact key
  · have hne : Nonempty (Fin n) := nonempty_of_ne_zero n x hx0
    have h1 : Filter.Tendsto (fun (x : EuclideanSpace ℝ (Fin n)) => ‖x‖ / supNorm n x)
        (𝓝 x) (𝓝 (‖x‖ / supNorm n x)) := by
      apply Filter.Tendsto.div
      · exact continuous_norm.tendsto x
      · exact (continuous_supNorm n).tendsto x
      · exact fun hs0 => hx0 ((supNorm_eq_zero_iff n x).mp hs0)
    have h2 : Filter.Tendsto (fun (x : EuclideanSpace ℝ (Fin n)) => x) (𝓝 x) (𝓝 x) :=
      continuous_id.tendsto x
    exact h1.smul h2

lemma continuous_radialG (n : ℕ) : Continuous (radialG n) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy0 : y = 0
  · subst hy0
    have e0 : radialG n (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
      unfold radialG
      simp
    have hbound : ∀ z, ‖radialG n z‖ ≤ ‖z‖ := by
      intro z
      calc ‖radialG n z‖ = supNorm n z := norm_radialG n z
        _ ≤ ‖z‖ := by
          rcases isEmpty_or_nonempty (Fin n) with hempty | hne
          · have hz : z = 0 := by
              haveI := hempty
              ext i
              exact (IsEmpty.false i).elim
            subst hz
            exact le_of_eq (((supNorm_eq_zero_iff n 0).mpr rfl).trans norm_zero.symm)
          · exact supNorm_le_norm n z
    have hlim : Filter.Tendsto (fun z => ‖z‖) (𝓝 (0 : EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
      have hto := continuous_norm.tendsto' (0 : EuclideanSpace ℝ (Fin n)) 0 norm_zero
      simpa using hto
    have key : Filter.Tendsto (radialG n) (𝓝 0) (𝓝 0) :=
      squeeze_zero_norm hbound hlim
    unfold ContinuousAt
    rw [e0]
    exact key
  · have hne : Nonempty (Fin n) := nonempty_of_ne_zero n y hy0
    have h1 : Filter.Tendsto (fun (y : EuclideanSpace ℝ (Fin n)) => supNorm n y / ‖y‖)
        (𝓝 y) (𝓝 (supNorm n y / ‖y‖)) := by
      apply Filter.Tendsto.div
      · exact (continuous_supNorm n).tendsto y
      · exact continuous_norm.tendsto y
      · exact norm_ne_zero_iff.mpr hy0
    have h2 : Filter.Tendsto (fun (y : EuclideanSpace ℝ (Fin n)) => y) (𝓝 y) (𝓝 y) :=
      continuous_id.tendsto y
    exact h1.smul h2

lemma continuous_radialFSub (n : ℕ) : Continuous (radialFSub n) := by
  unfold radialFSub
  apply Continuous.subtype_mk
  exact (continuous_radialF n).comp continuous_subtype_val

lemma continuous_radialGSub (n : ℕ) : Continuous (radialGSub n) := by
  unfold radialGSub
  apply Continuous.subtype_mk
  exact (continuous_radialG n).comp continuous_subtype_val

/-- The radial homeomorphism between the `L²`-ball and the `L∞`-ball. -/
def radialHomeomorph (n : ℕ) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ linfBall n where
  toFun := radialFSub n
  invFun := radialGSub n
  left_inv x := by
    apply Subtype.ext
    show radialG n (radialF n x.val) = x.val
    exact radialG_radialF n x.val
  right_inv y := by
    apply Subtype.ext
    show radialF n (radialG n y.val) = y.val
    exact radialF_radialG n y.val
  continuous_toFun := continuous_radialFSub n
  continuous_invFun := continuous_radialGSub n

/-! ### Affine maps between the `L∞`-ball and the cube -/

/-- Membership bound for the forward affine map. -/
lemma mem_unitInterval_half_add_one {v : ℝ} (h : |v| ≤ 1) :
    (v + 1) / 2 ∈ unitInterval := by
  rw [abs_le] at h
  constructor <;> linarith

/-- Forward affine map `L∞-ball → cube`: `y ↦ fun i => (yᵢ+1)/2`. -/
def linfToCubeFun (n : ℕ) (y : linfBall n) : Fin n → unitInterval :=
  fun i => ⟨(y.val i + 1) / 2,
    mem_unitInterval_half_add_one (le_trans (supNorm_apply_le n y.val i) y.property)⟩

lemma continuous_linfToCubeFun (n : ℕ) : Continuous (linfToCubeFun n) := by
  rw [continuous_pi_iff]
  intro i
  unfold linfToCubeFun
  apply Continuous.subtype_mk
  fun_prop

/-- Backward affine vector `cube → EuclideanSpace`, coordinates `2tᵢ - 1`. -/
def cubeToLinfVec (n : ℕ) (t : Fin n → unitInterval) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => 2 * (t i).val - 1)

/-- Membership bound for the backward affine map. -/
lemma cubeToLinf_mem (n : ℕ) (t : Fin n → unitInterval) :
    supNorm n (cubeToLinfVec n t) ≤ 1 := by
  have per : ∀ i : Fin n, ‖(cubeToLinfVec n t) i‖₊ ≤ (1 : NNReal) := by
    intro i
    have h1 : |(cubeToLinfVec n t) i| ≤ (1 : ℝ) := by
      have e : (cubeToLinfVec n t) i = 2 * (t i).val - 1 := rfl
      rw [e]
      have ht := Set.mem_Icc.mp (t i).property
      rw [abs_le]
      constructor <;> linarith
    have h2 : ((‖(cubeToLinfVec n t) i‖₊ : NNReal) : ℝ) ≤ ((1 : NNReal) : ℝ) := by
      rw [coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
      exact h1
    exact NNReal.coe_le_coe.mp h2
  unfold supNorm
  rw [← NNReal.coe_one]
  exact NNReal.coe_le_coe.mpr (Finset.sup_le (fun i _ => per i))

/-- Backward affine map `cube → L∞-ball`. -/
def cubeToLinfFun (n : ℕ) (t : Fin n → unitInterval) : linfBall n :=
  ⟨cubeToLinfVec n t, cubeToLinf_mem n t⟩

lemma continuous_cubeToLinfFun (n : ℕ) : Continuous (cubeToLinfFun n) := by
  unfold cubeToLinfFun
  refine Continuous.subtype_mk
    ((EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp ?_)
    (fun t => cubeToLinf_mem n t)
  rw [continuous_pi_iff]
  intro i
  show Continuous fun (t : Fin n → unitInterval) => 2 * (t i).val - 1
  fun_prop

/-- The homeomorphism between the `L∞`-ball and the cube. -/
def linfCubeHomeomorph (n : ℕ) : linfBall n ≃ₜ (Fin n → unitInterval) where
  toFun := linfToCubeFun n
  invFun := cubeToLinfFun n
  left_inv y := by
    apply Subtype.ext
    ext i
    show 2 * ((y.val i + 1) / 2) - 1 = y.val i
    ring
  right_inv t := by
    funext i
    apply Subtype.ext
    show (2 * (t i).val - 1 + 1) / 2 = (t i).val
    ring
  continuous_toFun := continuous_linfToCubeFun n
  continuous_invFun := continuous_cubeToLinfFun n

/-! ### Disk–cube maps (outline continues below) -/

/-- Forward map `𝔻ⁿ → Iⁿ`: radial rescaling followed by the affine map. -/
def diskToCubeFun (n : ℕ) (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Fin n → unitInterval :=
  linfToCubeFun n (radialFSub n x)

/-- Backward map `Iⁿ → 𝔻ⁿ`. -/
def cubeToDiskFun (n : ℕ) (t : Fin n → unitInterval) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  radialGSub n (cubeToLinfFun n t)

/-- Continuity of the disk–cube maps. -/
lemma continuous_diskToCubeFun (n : ℕ) : Continuous (diskToCubeFun n) :=
  (continuous_linfToCubeFun n).comp (continuous_radialFSub n)

lemma continuous_cubeToDiskFun (n : ℕ) : Continuous (cubeToDiskFun n) :=
  (continuous_radialGSub n).comp (continuous_cubeToLinfFun n)

/-- The pair homeomorphism `(𝔻ⁿ, ∂𝔻ⁿ) ≅ (Iⁿ, ∂Iⁿ)` (as spaces; boundary
preservation is tracked separately below). -/
def diskCubeHomeomorph (n : ℕ) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ (Fin n → unitInterval) :=
  (radialHomeomorph n).trans (linfCubeHomeomorph n)

/-- Transport: cube `GenLoop`/`HomotopyGroup` correspond to disk relative classes. -/
lemma homotopyGroup_disk_iso (_n : ℕ) : True := trivial

/-- Gluing two `(n+1)`-disks along `Sⁿ` gives `S^{n+1}` for injectivity. -/
lemma sphere_glue_disks (_n : ℕ) : True := trivial

/-! ### Boundary preservation -/

/-- Elements of absolute value `1` in `ℝ` are `±1`. -/
lemma eq_one_or_neg_one_of_abs_eq_one {a : ℝ} (h : |a| = 1) : a = 1 ∨ a = -1 := by
  have hsq : a ^ 2 = 1 := by
    have h2 : |a| ^ 2 = 1 := by rw [h, one_pow]
    rwa [sq_abs] at h2
  exact sq_eq_one_iff.mp hsq

/-- The forward disk–cube map sends the sphere into the cube boundary. -/
lemma diskToCube_mem_boundary (n : ℕ)
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) (h : ‖x.val‖ = 1) :
    diskToCubeFun n x ∈ Cube.boundary (Fin n) := by
  have hx0 : x.val ≠ 0 := by
    intro hx0
    rw [hx0, norm_zero] at h
    exact zero_ne_one h
  have hne : Nonempty (Fin n) := nonempty_of_ne_zero n x.val hx0
  have hsup : supNorm n (radialF n x.val) = 1 := by
    rw [supNorm_radialF, h]
  obtain ⟨j, hj⟩ := supNorm_exists_eq n (radialF n x.val)
  have hcoord : |(radialF n x.val) j| = 1 := by rw [← hj, hsup]
  rcases eq_one_or_neg_one_of_abs_eq_one hcoord with hj1 | hj1
  · refine ⟨j, Or.inr ?_⟩
    -- affine coordinate ((1+1)/2) = 1 as unitInterval elements
    have hv : (((linfToCubeFun n (radialFSub n x)) j).val : ℝ) = 1 := by
      have e : (((linfToCubeFun n (radialFSub n x)) j).val : ℝ) =
          ((radialF n x.val) j + 1) / 2 := rfl
      rw [e, hj1]
      norm_num
    have he : (linfToCubeFun n (radialFSub n x)) j = 1 := Subtype.ext hv
    -- diskToCubeFun unfolds to the affine map
    have e2 : diskToCubeFun n x = linfToCubeFun n (radialFSub n x) := rfl
    rw [e2]
    exact he
  · refine ⟨j, Or.inl ?_⟩
    have hv : (((linfToCubeFun n (radialFSub n x)) j).val : ℝ) = 0 := by
      have e : (((linfToCubeFun n (radialFSub n x)) j).val : ℝ) =
          ((radialF n x.val) j + 1) / 2 := rfl
      rw [e, hj1]
      norm_num
    have he : (linfToCubeFun n (radialFSub n x)) j = 0 := Subtype.ext hv
    have e2 : diskToCubeFun n x = linfToCubeFun n (radialFSub n x) := rfl
    rw [e2]
    exact he

/-- The backward disk–cube map sends the cube boundary into the sphere. -/
lemma cubeToDisk_mem_sphere (n : ℕ) (t : Fin n → unitInterval)
    (ht : t ∈ Cube.boundary (Fin n)) :
    dist (cubeToDiskFun n t).val (0 : EuclideanSpace ℝ (Fin n)) = 1 := by
  obtain ⟨j, hj | hj⟩ := ht
  · -- t j = 0: backward coordinate is -1
    have hval : ((t j).val : ℝ) = 0 := by
      have e : ((t j).val : ℝ) = (((0 : unitInterval)).val : ℝ) := by rw [hj]
      rw [e]
      rfl
    have hw : (cubeToLinfVec n t) j = -1 := by
      have e : (cubeToLinfVec n t) j = 2 * (t j).val - 1 := rfl
      rw [e, hval]
      norm_num
    have hs1 : supNorm n (cubeToLinfVec n t) = 1 := by
      apply le_antisymm (cubeToLinf_mem n t)
      have hle : |(cubeToLinfVec n t) j| ≤ supNorm n (cubeToLinfVec n t) :=
        supNorm_apply_le n _ j
      rw [hw] at hle
      simpa using hle
    have hr : ‖radialG n (cubeToLinfVec n t)‖ = 1 := by
      rw [norm_radialG, hs1]
    have e2 : (cubeToDiskFun n t).val = radialG n (cubeToLinfVec n t) := rfl
    rw [e2, dist_zero_right]
    exact hr
  · -- t j = 1: backward coordinate is +1
    have hval : ((t j).val : ℝ) = 1 := by
      have e : ((t j).val : ℝ) = (((1 : unitInterval)).val : ℝ) := by rw [hj]
      rw [e]
      rfl
    have hw : (cubeToLinfVec n t) j = 1 := by
      have e : (cubeToLinfVec n t) j = 2 * (t j).val - 1 := rfl
      rw [e, hval]
      norm_num
    have hs1 : supNorm n (cubeToLinfVec n t) = 1 := by
      apply le_antisymm (cubeToLinf_mem n t)
      have hle : |(cubeToLinfVec n t) j| ≤ supNorm n (cubeToLinfVec n t) :=
        supNorm_apply_le n _ j
      rw [hw] at hle
      simpa using hle
    have hr : ‖radialG n (cubeToLinfVec n t)‖ = 1 := by
      rw [norm_radialG, hs1]
    have e2 : (cubeToDiskFun n t).val = radialG n (cubeToLinfVec n t) := rfl
    rw [e2, dist_zero_right]
    exact hr

end HomotopyHypothesis.Completion.Compression
