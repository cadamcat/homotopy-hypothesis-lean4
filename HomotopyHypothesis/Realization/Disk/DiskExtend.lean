import HomotopyHypothesis.Challenge
import HomotopyHypothesis.Realization.Disk.FaceRetract
/-!
# Extending parallel disk maps into a contractible space

Two maps `𝔻 n → X` that agree on the boundary sphere determine a continuous map on the
boundary sphere of `𝔻 (n+1)`, by reading the source hemisphere as the first map and the
target hemisphere as the second. A contraction of `X` cones that sphere map off to a
filler `𝔻 (n+1) → X`.
-/

noncomputable section

namespace HomotopyHypothesis.Realization.Disk

open ContinuousMap
open scoped unitInterval
open Set Filter Topology

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The boundary sphere of the closed disk, as a subtype. -/
abbrev Sphere (n : ℕ) := {y : Ball n // ‖(y : E n)‖ = 1}

/-- The closed disk with the origin removed. -/
abbrev Punctured (n : ℕ) := {y : Ball n // ‖(y : E n)‖ ≠ 0}

instance (n : ℕ) : CompactSpace (Sphere n) := by
  rw [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ, Subtype.range_coe_subtype]
  change IsCompact {y : Ball n | ‖(y : E n)‖ = 1}
  have hclosed : IsClosed {y : Ball n | ‖(y : E n)‖ = 1} :=
    isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const
  exact hclosed.isCompact

/-- Drop the last coordinate. -/
def dropLast {n : ℕ} (y : E (n + 1)) : E n :=
  WithLp.toLp 2 fun i => y i.castSucc

/-- The last coordinate. -/
def lastCoord {n : ℕ} (y : E (n + 1)) : ℝ :=
  y (Fin.last n)

lemma norm_sq_dropLast {n : ℕ} (y : E (n + 1)) :
    ‖y‖ ^ 2 = ‖dropLast y‖ ^ 2 + lastCoord y ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, dropLast, lastCoord]
  rw [Fin.sum_univ_castSucc]

/-- A coordinate of an adjacent face. The ambient dimension is one more than the source, so the
trailing-zero branch of `faceVec` is empty. -/
lemma faceVec_succ_apply {n : ℕ} (side : Bool) (x : E n) (i : Fin (n + 1)) :
    faceVec n (n + 1) side x i =
      if h : (i : ℕ) < n then x ⟨i, h⟩
      else (if side then -1 else 1) * Real.sqrt (1 - ‖x‖ ^ 2) := by
  simp only [faceVec, PiLp.toLp_apply]
  by_cases h1 : (i : ℕ) < n
  · conv_lhs => rw [dite_eq_left h1]
    conv_rhs => rw [dite_eq_left h1]
  · have h2 : (i : ℕ) = n := by
      have hlt : (i : ℕ) < n + 1 := i.isLt
      omega
    conv_lhs =>
      rw [dite_eq_right h1]
      rw [ite_eq_left h2]
    conv_rhs => rw [dite_eq_right h1]

lemma dropLast_faceVec {n : ℕ} (side : Bool) (x : E n) :
    dropLast (faceVec n (n + 1) side x) = x := by
  ext i
  simp only [dropLast, faceVec, PiLp.toLp_apply]
  rw [dif_pos (by simpa using i.isLt)]
  exact congrArg (fun j : Fin n => x j) (Fin.ext (by simp))

lemma lastCoord_faceVec {n : ℕ} (side : Bool) (x : E n) :
    lastCoord (faceVec n (n + 1) side x) =
      (if side then -1 else 1) * Real.sqrt (1 - ‖x‖ ^ 2) := by
  simp only [lastCoord, faceVec, PiLp.toLp_apply]
  rw [dif_neg (by simp : ¬ ((Fin.last n : ℕ) < n))]
  simp

/-- Projection of a point of `𝔻 (n+1)` onto the first `n` coordinates. -/
def diskProj {n : ℕ} (y : Ball (n + 1)) : Ball n :=
  ⟨dropLast y.1, by
    rw [mem_closedBall_zero_iff]
    have hy : ‖(y : E (n + 1))‖ ≤ 1 := mem_closedBall_zero_iff.mp y.2
    have hsq : ‖dropLast y.1‖ ^ 2 ≤ ‖(y : E (n + 1))‖ ^ 2 := by
      rw [norm_sq_dropLast]
      nlinarith [sq_nonneg (lastCoord y.1)]
    exact (le_of_sq_le_sq hsq (norm_nonneg _)).trans hy⟩

lemma continuous_diskProj {n : ℕ} : Continuous (diskProj (n := n)) := by
  rw [Topology.IsInducing.subtypeVal.continuous_iff]
  change Continuous fun y : Ball (n + 1) => (diskProj y : E n)
  have hfun : (fun y : Ball (n + 1) => (diskProj y : E n)) = fun y => dropLast y.1 := by
    ext y; rfl
  rw [hfun]
  unfold dropLast
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  exact (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) i.castSucc).comp
    continuous_subtype_val

lemma continuous_lastCoord {n : ℕ} :
    Continuous (fun y : Ball (n + 1) => lastCoord y.1) :=
  (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).comp continuous_subtype_val

lemma norm_ballFace {n : ℕ} (side : Bool) (x : Ball n) :
    ‖((ballFace (Nat.lt_succ_self n) side x) : E (n + 1))‖ = 1 := by
  have hx : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
  have hsq := norm_sq_faceVec (Nat.lt_succ_self n) side x.1 hx
  have hvec : ((ballFace (Nat.lt_succ_self n) side x) : E (n + 1)) =
      faceVec n (n + 1) side x.1 := rfl
  rw [hvec]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hsq)

lemma diskProj_ballFace {n : ℕ} (side : Bool) (x : Ball n) :
    diskProj (ballFace (Nat.lt_succ_self n) side x) = x := by
  apply Subtype.ext
  have hvec : ((ballFace (Nat.lt_succ_self n) side x) : E (n + 1)) =
      faceVec n (n + 1) side x.1 := rfl
  simp only [diskProj]
  rw [hvec]
  exact dropLast_faceVec side x.1

lemma lastCoord_ballFace {n : ℕ} (side : Bool) (x : Ball n) :
    lastCoord (ballFace (Nat.lt_succ_self n) side x).1 =
      (if side then -1 else 1 : ℝ) * Real.sqrt (1 - ‖x.1‖ ^ 2) := by
  have hvec : ((ballFace (Nat.lt_succ_self n) side x) : E (n + 1)) =
      faceVec n (n + 1) side x.1 := rfl
  rw [hvec]
  exact lastCoord_faceVec side x.1

/-- Every boundary point of `𝔻 (n+1)` lies on the source or the target hemisphere. -/
theorem exists_ballFace_of_sphere {n : ℕ} (y : Ball (n + 1))
    (hy : ‖(y : E (n + 1))‖ = 1) :
    ∃ side : Bool, ∃ x : Ball n, ballFace (Nat.lt_succ_self n) side x = y := by
  let v : E n := dropLast y.1
  have hsplit := norm_sq_dropLast y.1
  have hv : ‖v‖ ≤ 1 := by
    have hsq : ‖v‖ ^ 2 ≤ 1 := by
      have : ‖v‖ ^ 2 ≤ ‖(y : E (n + 1))‖ ^ 2 := by
        rw [hsplit]
        nlinarith [sq_nonneg (lastCoord y.1)]
      rw [hy] at this
      simpa using this
    exact le_of_sq_le_sq (by simpa [one_pow] using hsq) zero_le_one
  let x : Ball n := ⟨v, mem_closedBall_zero_iff.mpr hv⟩
  have ht2 : lastCoord y.1 ^ 2 = 1 - ‖v‖ ^ 2 := by
    have := hsplit
    rw [hy] at this
    nlinarith
  by_cases hs : 0 ≤ lastCoord y.1
  · refine ⟨false, x, ?_⟩
    apply Subtype.ext
    apply PiLp.ext
    intro i
    have hface : ((ballFace (Nat.lt_succ_self n) false x) : E (n + 1)) =
        faceVec n (n + 1) false v := rfl
    rw [hface, faceVec_succ_apply]
    by_cases hi : (i : ℕ) < n
    · simp only [hi, dite_true, v]
      conv_rhs => rw [show i = (⟨i, hi⟩ : Fin n).castSucc by ext; simp]
      simp [dropLast, PiLp.toLp_apply]
    · simp only [hi, dite_false]
      have hi' : i = Fin.last n := by
        apply Fin.ext
        simp only [Fin.val_last]
        have hlt : (i : ℕ) < n + 1 := i.isLt
        omega
      rw [hi', ← lastCoord]
      have hnn : 0 ≤ 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v, hv]
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      rw [Real.sqrt_eq_iff_eq_sq hnn hs]
      exact ht2.symm
  · refine ⟨true, x, ?_⟩
    apply Subtype.ext
    apply PiLp.ext
    intro i
    have hface : ((ballFace (Nat.lt_succ_self n) true x) : E (n + 1)) =
        faceVec n (n + 1) true v := rfl
    rw [hface, faceVec_succ_apply]
    by_cases hi : (i : ℕ) < n
    · simp only [hi, dite_true, v]
      conv_rhs => rw [show i = (⟨i, hi⟩ : Fin n).castSucc by ext; simp]
      simp [dropLast, PiLp.toLp_apply]
    · simp only [hi, dite_false]
      have hi' : i = Fin.last n := by
        apply Fin.ext
        simp only [Fin.val_last]
        have hlt : (i : ℕ) < n + 1 := i.isLt
        omega
      rw [hi', ← lastCoord]
      have hnn : 0 ≤ 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v, hv]
      have hneg : lastCoord y.1 ≤ 0 := le_of_not_ge hs
      simp only [↓reduceIte]
      rw [neg_one_mul, neg_eq_iff_eq_neg, Real.sqrt_eq_iff_eq_sq hnn (neg_nonneg.mpr hneg), neg_sq]
      exact ht2.symm

/-- Maps that agree on both hemispheres agree on the sphere those hemispheres cover. -/
theorem agree_on_sphere_of_faces {n : ℕ} {f g : C(Ball (n + 1), X)}
    (hsource : f.comp (ballFace (Nat.lt_succ_self n) false) =
      g.comp (ballFace (Nat.lt_succ_self n) false))
    (htarget : f.comp (ballFace (Nat.lt_succ_self n) true) =
      g.comp (ballFace (Nat.lt_succ_self n) true))
    (y : Ball (n + 1)) (hy : ‖(y : E (n + 1))‖ = 1) : f y = g y := by
  obtain ⟨side, x, hx⟩ := exists_ballFace_of_sphere y hy
  cases side
  · have hpt := DFunLike.congr_fun hsource x
    simp only [ContinuousMap.comp_apply, hx] at hpt
    exact hpt
  · have hpt := DFunLike.congr_fun htarget x
    simp only [ContinuousMap.comp_apply, hx] at hpt
    exact hpt

/-- The sphere map that is `f` on the source hemisphere and `g` on the target hemisphere. -/
def boundaryMap {n : ℕ} (f g : C(Ball n, X))
    (hagree : ∀ y : Ball n, ‖(y : E n)‖ = 1 → f y = g y) : C(Sphere (n + 1), X) where
  toFun y :=
    if 0 ≤ lastCoord y.1.1 then f (diskProj y.1) else g (diskProj y.1)
  continuous_toFun := by
    refine continuous_if_le continuous_const
      (continuous_lastCoord.comp continuous_subtype_val) ?_ ?_ ?_
    · exact ((f.continuous.comp continuous_diskProj).comp continuous_subtype_val).continuousOn
    · exact ((g.continuous.comp continuous_diskProj).comp continuous_subtype_val).continuousOn
    · intro y hEq
      have hy1 : ‖(y.1 : E (n + 1))‖ = 1 := y.2
      have ht : lastCoord y.1.1 = 0 := hEq.symm
      have hsq := norm_sq_dropLast y.1.1
      have hdrop : ‖dropLast y.1.1‖ ^ 2 = 1 := by nlinarith
      have hnorm : ‖(diskProj y.1 : E n)‖ = 1 :=
        (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa [diskProj, one_pow] using hdrop)
      exact hagree (diskProj y.1) hnorm

lemma boundaryMap_source {n : ℕ} (f g : C(Ball n, X))
    (hagree : ∀ y : Ball n, ‖(y : E n)‖ = 1 → f y = g y) (x : Ball n) :
    boundaryMap f g hagree ⟨ballFace (Nat.lt_succ_self n) false x, norm_ballFace false x⟩ =
      f x := by
  have hlast : 0 ≤ lastCoord (ballFace (Nat.lt_succ_self n) false x).1 := by
    rw [lastCoord_ballFace]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    exact Real.sqrt_nonneg _
  simp only [boundaryMap, ContinuousMap.coe_mk, hlast, ↓reduceIte, diskProj_ballFace]

lemma boundaryMap_target {n : ℕ} (f g : C(Ball n, X))
    (hagree : ∀ y : Ball n, ‖(y : E n)‖ = 1 → f y = g y) (x : Ball n) :
    boundaryMap f g hagree ⟨ballFace (Nat.lt_succ_self n) true x, norm_ballFace true x⟩ =
      g x := by
  have hlast : lastCoord (ballFace (Nat.lt_succ_self n) true x).1 =
      -Real.sqrt (1 - ‖x.1‖ ^ 2) := by
    rw [lastCoord_ballFace]
    simp only [↓reduceIte, neg_one_mul]
  by_cases hle : 0 ≤ lastCoord (ballFace (Nat.lt_succ_self n) true x).1
  · have hnonpos : lastCoord (ballFace (Nat.lt_succ_self n) true x).1 ≤ 0 := by
      rw [hlast]
      exact neg_nonpos.mpr (Real.sqrt_nonneg _)
    have hzero : lastCoord (ballFace (Nat.lt_succ_self n) true x).1 = 0 :=
      le_antisymm hnonpos hle
    have hsqrt : Real.sqrt (1 - ‖x.1‖ ^ 2) = 0 := by
      rw [hlast] at hzero
      exact neg_eq_zero.mp hzero
    have hnn : 0 ≤ 1 - ‖x.1‖ ^ 2 := by
      have hx : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
      have hsq : ‖x.1‖ ^ 2 ≤ 1 := by
        simpa [sq, one_mul] using mul_self_le_mul_self (norm_nonneg _) hx
      exact sub_nonneg.mpr hsq
    have hrad : 1 - ‖x.1‖ ^ 2 = 0 := by
      rw [← Real.sq_sqrt hnn, hsqrt, sq, mul_zero]
    have hx1 : ‖x.1‖ = 1 :=
      (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by
        have : ‖x.1‖ ^ 2 = 1 := by linarith
        simpa [one_pow] using this)
    simp only [boundaryMap, ContinuousMap.coe_mk, hle, ↓reduceIte, diskProj_ballFace]
    exact hagree x hx1
  · simp only [boundaryMap, ContinuousMap.coe_mk, hle, ↓reduceIte, diskProj_ballFace]

/-- The origin of the closed disk. -/
def origin (n : ℕ) : Ball n :=
  ⟨0, by rw [mem_closedBall_zero_iff, norm_zero]; exact zero_le_one⟩

/-- Radial time, equal to `1` at the origin and to `0` on the sphere. -/
def timeOf {n : ℕ} (y : Ball n) : unitInterval :=
  ⟨1 - ‖(y : E n)‖, by
    constructor
    · exact sub_nonneg.mpr (mem_closedBall_zero_iff.mp y.2)
    · exact sub_le_self _ (norm_nonneg _)⟩

lemma continuous_timeOf {n : ℕ} : Continuous (timeOf (n := n)) := by
  rw [Topology.IsInducing.subtypeVal.continuous_iff]
  change Continuous fun y : Ball n => (timeOf y : ℝ)
  have hfun : (fun y : Ball n => (timeOf y : ℝ)) =
      (fun y : Ball n => 1 - ‖(y : E n)‖) := by
    ext y; rfl
  rw [hfun]
  exact continuous_const.sub (continuous_norm.comp continuous_subtype_val)

lemma timeOf_origin (n : ℕ) : timeOf (origin n) = 1 := by
  apply Subtype.ext
  simp [timeOf, origin]

lemma timeOf_of_norm_one {n : ℕ} (y : Ball n) (hy : ‖(y : E n)‖ = 1) : timeOf y = 0 := by
  apply Subtype.ext
  simp [timeOf, hy]

/-- Unit radial vector of a point other than the origin. -/
def radial {n : ℕ} (p : Punctured n) : E n :=
  ‖p.1.1‖⁻¹ • p.1.1

lemma sphere_radial_mem {n : ℕ} (p : Punctured n) :
    radial p ∈ Metric.closedBall (0 : E n) 1 := by
  rw [radial, mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact (inv_mul_cancel₀ p.2).le

lemma sphere_radial_norm {n : ℕ} (p : Punctured n) : ‖radial p‖ = 1 := by
  rw [radial, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ p.2]

def spherePoint {n : ℕ} (p : Punctured n) : Sphere n :=
  ⟨⟨radial p, sphere_radial_mem p⟩, sphere_radial_norm p⟩

lemma continuous_spherePoint {n : ℕ} : Continuous (spherePoint (n := n)) := by
  unfold spherePoint
  refine Continuous.subtype_mk ?_ sphere_radial_norm
  refine Continuous.subtype_mk ?_ sphere_radial_mem
  unfold radial
  exact (Continuous.inv₀
      ((continuous_norm.comp continuous_subtype_val).comp continuous_subtype_val)
      (fun p => p.2)).smul
    (continuous_subtype_val.comp continuous_subtype_val)

lemma spherePoint_of_norm_one {n : ℕ} (y : Ball n) (hy : ‖(y : E n)‖ = 1) :
    spherePoint ⟨y, by rw [hy]; exact one_ne_zero⟩ = ⟨y, hy⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [spherePoint, radial]
  rw [hy, inv_one, one_smul]

/-- Cone a sphere map off along a contraction of the target. `H` runs from the identity at time
`0` to the constant `c` at time `1`. -/
def coneFun {n : ℕ} (c : X) (Φ : C(Sphere (n + 1), X))
    (H : Homotopy (ContinuousMap.id X) (ContinuousMap.const X c)) (y : Ball (n + 1)) : X :=
  if hy : ‖(y : E (n + 1))‖ = 0 then c
  else H (timeOf y, Φ (spherePoint ⟨y, hy⟩))

lemma coneFun_origin {n : ℕ} (c : X) (Φ : C(Sphere (n + 1), X))
    (H : Homotopy (ContinuousMap.id X) (ContinuousMap.const X c)) :
    coneFun c Φ H (origin (n + 1)) = c := by
  simp [coneFun, origin, norm_zero]

lemma coneFun_sphere {n : ℕ} (c : X) (Φ : C(Sphere (n + 1), X))
    (H : Homotopy (ContinuousMap.id X) (ContinuousMap.const X c))
    (y : Ball (n + 1)) (hy : ‖(y : E (n + 1))‖ = 1) :
    coneFun c Φ H y = Φ ⟨y, hy⟩ := by
  have hne : ‖(y : E (n + 1))‖ ≠ 0 := by simp [hy]
  rw [coneFun]
  split_ifs with hzero
  · exact absurd hy (by simp [hzero])
  · have hs : spherePoint ⟨y, hne⟩ = ⟨y, hy⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [spherePoint, radial, hy, inv_one, one_smul]
    rw [timeOf_of_norm_one y hy, hs]
    exact H.apply_zero (Φ ⟨y, hy⟩)

lemma continuous_coneFun {n : ℕ} (c : X) (Φ : C(Sphere (n + 1), X))
    (H : Homotopy (ContinuousMap.id X) (ContinuousMap.const X c)) :
    Continuous (coneFun c Φ H) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : ‖(y : E (n + 1))‖ = 0
  · have hy0 : y = origin (n + 1) := Subtype.ext (norm_eq_zero.mp hy)
    rw [hy0]
    rw [continuousAt_def]
    intro U hU
    rw [coneFun_origin] at hU
    obtain ⟨V, hVU, hVopen, hcV⟩ := mem_nhds_iff.mp hU
    have hsubset : {(1 : unitInterval)} ×ˢ range (⇑Φ) ⊆ (⇑H) ⁻¹' V := by
      intro p hp
      rw [mem_prod] at hp
      obtain ⟨s, hs⟩ := hp.2
      have hp1 : p.1 = 1 := by simpa using hp.1
      have hpeq : p = (1, Φ s) := Prod.ext hp1 hs.symm
      rw [mem_preimage, hpeq, H.apply_one, ContinuousMap.const_apply]
      exact hcV
    obtain ⟨u, v, huo, _hvo, hsu, hsv, hprod⟩ :=
      generalized_tube_lemma (X := unitInterval) (Y := X) (s := {(1 : unitInterval)})
        isCompact_singleton (isCompact_range (map_continuous Φ))
        (H.continuous_toFun.isOpen_preimage V hVopen) hsubset
    have h1u : (1 : unitInterval) ∈ u := by simpa using hsu
    have hpre : timeOf ⁻¹' u ∈ 𝓝 (origin (n + 1)) :=
      continuous_timeOf.continuousAt.preimage_mem_nhds
        (huo.mem_nhds (by rw [timeOf_origin]; exact h1u))
    refine mem_of_superset hpre ?_
    intro z hz
    rw [Set.mem_preimage]
    by_cases hzn : ‖(z : E (n + 1))‖ = 0
    · have hz0 : z = origin (n + 1) := Subtype.ext (norm_eq_zero.mp hzn)
      rw [hz0, coneFun_origin]
      exact hVU hcV
    · rw [coneFun, dite_eq_right hzn]
      apply hVU
      apply hprod
      rw [mem_prod]
      exact ⟨hz, hsv (mem_range_self _)⟩
  · have hopen : IsOpen {z : Ball (n + 1) | ‖(z : E (n + 1))‖ ≠ 0} := by
      have hset : {z : Ball (n + 1) | ‖(z : E (n + 1))‖ ≠ 0} =
          (fun z : Ball (n + 1) => ‖(z : E (n + 1))‖) ⁻¹' ({(0 : ℝ)}ᶜ) := by
        ext z
        simp
      rw [hset]
      exact (continuous_norm.comp continuous_subtype_val).isOpen_preimage
        ({(0 : ℝ)}ᶜ) isOpen_compl_singleton
    have hmap := map_nhds_subtype_coe_eq_nhds (p := fun z : Ball (n + 1) =>
      ‖(z : E (n + 1))‖ ≠ 0) hy (hopen.mem_nhds (by simpa using hy))
    rw [ContinuousAt, ← hmap, tendsto_map'_iff]
    have hcone : Continuous fun q : Punctured (n + 1) =>
        H (timeOf q.1, Φ (spherePoint q)) :=
      (map_continuous H).comp
        ((continuous_timeOf.comp continuous_subtype_val).prodMk
          ((map_continuous Φ).comp continuous_spherePoint))
    have hEq : coneFun c Φ H ∘ (Subtype.val : Punctured (n + 1) → Ball (n + 1)) =
        fun q => H (timeOf q.1, Φ (spherePoint q)) := by
      ext q
      rw [Function.comp_apply, coneFun, dite_eq_right q.2, Subtype.eta]
    have hval : coneFun c Φ H y =
        H (timeOf y, Φ (spherePoint ⟨y, hy⟩)) := by
      rw [coneFun, dite_eq_right hy]
    rw [hEq, hval]
    exact hcone.continuousAt

/-- The cone extension, as a continuous map. -/
def coneMap {n : ℕ} (c : X) (Φ : C(Sphere (n + 1), X))
    (H : Homotopy (ContinuousMap.id X) (ContinuousMap.const X c)) : C(Ball (n + 1), X) :=
  ⟨coneFun c Φ H, continuous_coneFun c Φ H⟩

lemma coneMap_source {n : ℕ} (c : X) (f g : C(Ball n, X))
    (hagree : ∀ y : Ball n, ‖(y : E n)‖ = 1 → f y = g y)
    (H : Homotopy (ContinuousMap.id X) (ContinuousMap.const X c)) :
    (coneMap c (boundaryMap f g hagree) H).comp (ballFace (Nat.lt_succ_self n) false) = f := by
  apply ContinuousMap.ext
  intro x
  rw [ContinuousMap.comp_apply, coneMap, ContinuousMap.coe_mk,
    coneFun_sphere _ _ _ _ (norm_ballFace false x)]
  exact boundaryMap_source f g hagree x

lemma coneMap_target {n : ℕ} (c : X) (f g : C(Ball n, X))
    (hagree : ∀ y : Ball n, ‖(y : E n)‖ = 1 → f y = g y)
    (H : Homotopy (ContinuousMap.id X) (ContinuousMap.const X c)) :
    (coneMap c (boundaryMap f g hagree) H).comp (ballFace (Nat.lt_succ_self n) true) = g := by
  apply ContinuousMap.ext
  intro x
  rw [ContinuousMap.comp_apply, coneMap, ContinuousMap.coe_mk,
    coneFun_sphere _ _ _ _ (norm_ballFace true x)]
  exact boundaryMap_target f g hagree x

/-- In a contractible space, parallel disk maps extend across the next globe. -/
theorem exists_ballFiller {n : ℕ} (f g : C(Ball n, X)) [ContractibleSpace X]
    (hagree : ∀ y : Ball n, ‖(y : E n)‖ = 1 → f y = g y) :
    ∃ w : C(Ball (n + 1), X),
      w.comp (ballFace (Nat.lt_succ_self n) false) = f ∧
      w.comp (ballFace (Nat.lt_succ_self n) true) = g := by
  obtain ⟨c, ⟨H⟩⟩ := id_nullhomotopic X
  refine ⟨coneMap c (boundaryMap f g hagree) H, ?_, ?_⟩
  · exact coneMap_source c f g hagree H
  · exact coneMap_target c f g hagree H

end HomotopyHypothesis.Realization.Disk
