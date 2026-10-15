import Mathlib
/-!
# Disks, hemispheres and the cube model

Maps of pairs `(𝔻^{n}, S^{n-1}) → (X, x)` are the representatives of the globe homotopy groups.
They are compared with Mathlib's cube model `Ωⁿ` through an explicit homeomorphism of pairs,
and a globe filler is compared with a homotopy relative to the boundary by slicing the disk.
-/

noncomputable section

namespace HomotopyHypothesis.Comparison.FundamentalGroupoid.Geom

open scoped unitInterval Topology
open ContinuousMap

variable {X : Type*} [TopologicalSpace X]

/-- Euclidean space `ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The closed unit disk `𝔻 n`. -/
abbrev ClosedBall (n : ℕ) := Metric.closedBall (0 : E n) 1

/-- The boundary sphere, as a subset of the disk. -/
def sphereSet (n : ℕ) : Set (ClosedBall n) := {y | ‖(y : E n)‖ = 1}

/-- Append a last coordinate. `i < n` reads `v`, and the last coordinate is `t`. -/
def snocVec {n : ℕ} (v : E n) (t : ℝ) : E (n + 1) :=
  WithLp.toLp 2 fun i => if h : (i : ℕ) < n then v ⟨i, h⟩ else t

/-- Drop the last coordinate. -/
def dropLast {n : ℕ} (y : E (n + 1)) : E n :=
  WithLp.toLp 2 fun i => y i.castSucc

/-- The last coordinate. -/
def lastCoord {n : ℕ} (y : E (n + 1)) : ℝ :=
  y (Fin.last n)

@[simp] lemma snocVec_castSucc {n : ℕ} (v : E n) (t : ℝ) (i : Fin n) :
    snocVec v t i.castSucc = v i := by
  simp only [snocVec, PiLp.toLp_apply]
  rw [dif_pos (by simpa using i.isLt)]
  exact congrArg (fun j : Fin n => v j) (Fin.ext (by simp))

@[simp] lemma snocVec_last {n : ℕ} (v : E n) (t : ℝ) :
    snocVec v t (Fin.last n) = t := by
  simp only [snocVec, PiLp.toLp_apply]
  rw [dif_neg (by simp)]

@[simp] lemma dropLast_snocVec {n : ℕ} (v : E n) (t : ℝ) : dropLast (snocVec v t) = v := by
  ext i
  simp [dropLast, snocVec_castSucc]

@[simp] lemma lastCoord_snocVec {n : ℕ} (v : E n) (t : ℝ) : lastCoord (snocVec v t) = t := by
  simp [lastCoord, snocVec_last]

lemma norm_sq_snocVec {n : ℕ} (v : E n) (t : ℝ) :
    ‖snocVec v t‖ ^ 2 = ‖v‖ ^ 2 + t ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp [snocVec_castSucc, snocVec_last, EuclideanSpace.real_norm_sq_eq]

lemma norm_sq_dropLast {n : ℕ} (y : E (n + 1)) :
    ‖y‖ ^ 2 = ‖dropLast y‖ ^ 2 + lastCoord y ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, dropLast, lastCoord, PiLp.toLp_apply]
  rw [Fin.sum_univ_castSucc]

/-- The origin of the disk. -/
def originBall (n : ℕ) : ClosedBall n :=
  ⟨0, by simp⟩

/-- Hemisphere inclusion `𝔻 n ↪ 𝔻 (n+1)`. `side = false` is the source (last coordinate `≥ 0`)
and `side = true` is the target. -/
def hemi (n : ℕ) (side : Bool) : C(ClosedBall n, ClosedBall (n + 1)) where
  toFun x :=
    ⟨snocVec x.1 ((if side then -1 else 1) * Real.sqrt (1 - ‖x.1‖ ^ 2)), by
      rw [mem_closedBall_zero_iff]
      have hx : ‖x.1‖ ≤ 1 := (mem_closedBall_zero_iff).mp x.2
      have hnn : 0 ≤ 1 - ‖x.1‖ ^ 2 := by nlinarith [norm_nonneg x.1]
      have hsq : ((if side then -1 else 1 : ℝ) ^ 2) = 1 := by cases side <;> norm_num
      have hnorm : ‖snocVec x.1 ((if side then -1 else 1) * Real.sqrt (1 - ‖x.1‖ ^ 2))‖ ^ 2 = 1 := by
        rw [norm_sq_snocVec, mul_pow, Real.sq_sqrt hnn, hsq, one_mul]
        ring
      nlinarith [norm_nonneg (snocVec x.1 ((if side then -1 else 1) * Real.sqrt (1 - ‖x.1‖ ^ 2)))]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold snocVec
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    by_cases hi : (i : ℕ) < n
    · have hfun : (fun x : ClosedBall n =>
          (WithLp.toLp 2 (fun j => if h : (j : ℕ) < n then (x : E n) ⟨j, h⟩ else
            (if side then -1 else 1) * Real.sqrt (1 - ‖(x : E n)‖ ^ 2)) : E (n + 1)) i) =
          (fun x : ClosedBall n => (x : E n) ⟨i, hi⟩) := by
        ext x
        simp only [PiLp.toLp_apply]
        rw [dif_pos hi]
      rw [hfun]
      exact (PiLp.continuous_apply 2 _ (⟨i, hi⟩ : Fin n)).comp continuous_subtype_val
    · have hfun : (fun x : ClosedBall n =>
          (WithLp.toLp 2 (fun j => if h : (j : ℕ) < n then (x : E n) ⟨j, h⟩ else
            (if side then -1 else 1) * Real.sqrt (1 - ‖(x : E n)‖ ^ 2)) : E (n + 1)) i) =
          (fun x : ClosedBall n =>
            (if side then -1 else 1) * Real.sqrt (1 - ‖(x : E n)‖ ^ 2)) := by
        ext x
        simp only [PiLp.toLp_apply]
        rw [dif_neg hi]
      rw [hfun]
      exact continuous_const.mul <| Real.continuous_sqrt.comp <|
        continuous_const.sub ((continuous_norm.comp continuous_subtype_val).pow 2)

lemma hemi_norm {n : ℕ} (side : Bool) (x : ClosedBall n) :
    ‖((hemi n side x) : E (n + 1))‖ = 1 := by
  have hx : ‖x.1‖ ≤ 1 := (mem_closedBall_zero_iff).mp x.2
  have hnn : 0 ≤ 1 - ‖x.1‖ ^ 2 := by nlinarith [norm_nonneg x.1]
  have hsq : ((if side then -1 else 1 : ℝ) ^ 2) = 1 := by cases side <;> norm_num
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  have hcoe : ((hemi n side x) : E (n + 1)) =
      snocVec x.1 ((if side then -1 else 1) * Real.sqrt (1 - ‖x.1‖ ^ 2)) := by
    simp [hemi]
  rw [hcoe, norm_sq_snocVec, mul_pow, Real.sq_sqrt hnn, hsq, one_mul]
  ring

lemma hemi_mem_sphere {n : ℕ} (side : Bool) (x : ClosedBall n) :
    hemi n side x ∈ sphereSet (n + 1) :=
  hemi_norm side x

/-- Both hemispheres cover the sphere, and they meet on the equator. -/
theorem exists_hemi_eq {n : ℕ} {y : ClosedBall (n + 1)} (hy : y ∈ sphereSet (n + 1)) :
    ∃ side : Bool, ∃ x : ClosedBall n, hemi n side x = y := by
  let v : E n := dropLast y.1
  have hy' : ‖(y : E (n + 1))‖ = 1 := hy
  have hsplit := norm_sq_dropLast (y : E (n + 1))
  have hv : ‖v‖ ≤ 1 := by
    have : ‖v‖ ^ 2 ≤ ‖(y : E (n + 1))‖ ^ 2 := by
      rw [hsplit]
      nlinarith [sq_nonneg (lastCoord (y : E (n + 1)))]
    rw [hy'] at this
    nlinarith [norm_nonneg v, sq_nonneg ‖v‖]
  refine ?_
  let x : ClosedBall n := ⟨v, (mem_closedBall_zero_iff).mpr hv⟩
  have ht2 : lastCoord (y : E (n + 1)) ^ 2 = 1 - ‖v‖ ^ 2 := by
    have := hsplit
    rw [hy'] at this
    nlinarith
  by_cases hs : 0 ≤ lastCoord (y : E (n + 1))
  · refine ⟨false, x, ?_⟩
    apply Subtype.ext
    apply PiLp.ext
    intro i
    rw [show (hemi n false x : E (n + 1)) = snocVec v (Real.sqrt (1 - ‖v‖ ^ 2)) by
      simp [hemi, x]]
    by_cases hi : (i : ℕ) < n
    · have hi' : i = (⟨i, hi⟩ : Fin n).castSucc := by ext; simp
      rw [hi', snocVec_castSucc]
      simp [v, dropLast, PiLp.toLp_apply]
    · have hi' : i = Fin.last n := Fin.eq_last_of_not_lt hi
      rw [hi', snocVec_last, ← lastCoord]
      have hnn : 0 ≤ 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v, hv]
      rw [Real.sqrt_eq_iff_eq_sq hnn hs]
      exact ht2.symm
  · refine ⟨true, x, ?_⟩
    apply Subtype.ext
    apply PiLp.ext
    intro i
    rw [show (hemi n true x : E (n + 1)) = snocVec v (-Real.sqrt (1 - ‖v‖ ^ 2)) by
      simp [hemi, x]]
    by_cases hi : (i : ℕ) < n
    · have hi' : i = (⟨i, hi⟩ : Fin n).castSucc := by ext; simp
      rw [hi', snocVec_castSucc]
      simp [v, dropLast, PiLp.toLp_apply]
    · have hi' : i = Fin.last n := Fin.eq_last_of_not_lt hi
      rw [hi', snocVec_last, ← lastCoord]
      have hnn : 0 ≤ 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v, hv]
      have hneg : lastCoord (y : E (n + 1)) ≤ 0 := le_of_not_ge hs
      rw [neg_eq_iff_eq_neg, Real.sqrt_eq_iff_eq_sq hnn (neg_nonneg.mpr hneg), neg_sq]
      exact ht2.symm

theorem const_on_sphere_iff_hemi {n : ℕ} {x : X} (f : C(ClosedBall (n + 1), X)) :
    (∀ y ∈ sphereSet (n + 1), f y = x) ↔
      f.comp (hemi n false) = const _ x ∧ f.comp (hemi n true) = const _ x := by
  constructor
  · intro hf
    constructor <;> ext y <;> exact hf _ (hemi_mem_sphere _ y)
  · intro ⟨h0, h1⟩ y hy
    obtain ⟨side, z, hz⟩ := exists_hemi_eq hy
    cases side with
    | false =>
      have := congrFun (congrArg DFunLike.coe h0) z
      simpa [hz] using this
    | true =>
      have := congrFun (congrArg DFunLike.coe h1) z
      simpa [hz] using this

/-! ### Paths on the 1-disk -/

lemma norm_fin1 (c : ℝ) : ‖WithLp.toLp 2 (fun _ : Fin 1 => c)‖ = |c| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one]
  simp [PiLp.toLp_apply, Real.sqrt_sq_eq_abs]

/-- The point of `𝔻 1` with coordinate `c`. -/
def ofCoord (c : ℝ) (hc : |c| ≤ 1) : ClosedBall 1 :=
  ⟨WithLp.toLp 2 (fun _ : Fin 1 => c), by
    rw [mem_closedBall_zero_iff, norm_fin1]
    exact hc⟩

lemma ofCoord_coord (c : ℝ) (hc : |c| ≤ 1) : (ofCoord c hc : E 1) 0 = c := by
  simp [ofCoord, PiLp.toLp_apply]

lemma coord_abs_le (y : ClosedBall 1) : |(y : E 1) 0| ≤ 1 := by
  have h : ‖(y : E 1)‖ ≤ 1 := (mem_closedBall_zero_iff).mp y.2
  rw [show ‖(y : E 1)‖ = |(y : E 1) 0| by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one]
    simp [Real.sqrt_sq_eq_abs]] at h
  exact h

/-- Source endpoint of `𝔻 1`, the point `+1`. -/
def endpointSource : ClosedBall 1 := ofCoord 1 (by norm_num)

/-- Target endpoint of `𝔻 1`, the point `-1`. -/
def endpointTarget : ClosedBall 1 := ofCoord (-1) (by norm_num)

lemma endpointSource_eq_hemi : endpointSource = hemi 0 false (originBall 0) := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  simp [endpointSource, ofCoord, hemi, originBall, snocVec, PiLp.toLp_apply, Real.sqrt_one]

lemma endpointTarget_eq_hemi : endpointTarget = hemi 0 true (originBall 0) := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  simp [endpointTarget, ofCoord, hemi, originBall, snocVec, PiLp.toLp_apply, Real.sqrt_one]

/-- Straight reparameterization `I → 𝔻 1`, from the source endpoint to the target endpoint. -/
def intervalToBall1 : C(unitInterval, ClosedBall 1) where
  toFun t := ofCoord (1 - 2 * (t : ℝ)) (by
    rw [abs_le]
    constructor <;> linarith [t.2.1, t.2.2])
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => ?_)
    exact continuous_const.sub (continuous_const.mul continuous_subtype_val)

lemma intervalToBall1_zero : intervalToBall1 0 = endpointSource := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  simp [intervalToBall1, endpointSource, ofCoord, PiLp.toLp_apply]

lemma intervalToBall1_one : intervalToBall1 1 = endpointTarget := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  simp [intervalToBall1, endpointTarget, ofCoord, PiLp.toLp_apply]
  norm_num

/-- The path traced by a map `𝔻 1 → X` from its source endpoint to its target endpoint. -/
def pathOfMap (f : C(ClosedBall 1, X)) :
    Path (f endpointSource) (f endpointTarget) where
  toContinuousMap := f.comp intervalToBall1
  source' := by simp [intervalToBall1_zero]
  target' := by simp [intervalToBall1_one]

/-- Extend a path to a map `𝔻 1 → X` by reading the coordinate of the disk. -/
def mapOfPath {a b : X} (p : Path a b) : C(ClosedBall 1, X) where
  toFun y :=
    p ⟨(1 - (y : E 1) 0) / 2, by
      have hc := coord_abs_le y
      constructor
      · rw [abs_le] at hc
        linarith
      · rw [abs_le] at hc
        linarith⟩
  continuous_toFun := by
    refine p.continuous.comp ?_
    apply Continuous.subtype_mk
    exact (continuous_const.sub ((PiLp.continuous_apply 2 _ (0 : Fin 1)).comp
      continuous_subtype_val)).div_const 2

lemma mapOfPath_source {a b : X} (p : Path a b) : mapOfPath p endpointSource = a := by
  simp [mapOfPath, endpointSource, ofCoord, PiLp.toLp_apply, p.source]

lemma mapOfPath_target {a b : X} (p : Path a b) : mapOfPath p endpointTarget = b := by
  simp [mapOfPath, endpointTarget, ofCoord, PiLp.toLp_apply, p.target]

/-! ### Globe fillers and homotopies relative to the boundary -/

/-- A map of the pair `(𝔻 n, S^{n-1})`. -/
def BallPair (n : ℕ) (x : X) :=
  {f : C(ClosedBall n, X) // ∀ y ∈ sphereSet n, f y = x}

/-- Linear slice from the source hemisphere (`s = 1`) to the target hemisphere (`s = -1`). -/
def slice (n : ℕ) (s : ℝ) (hs : |s| ≤ 1) (u : ClosedBall n) : ClosedBall (n + 1) :=
  ⟨snocVec u.1 (s * Real.sqrt (1 - ‖(u : E n)‖ ^ 2)), by
    rw [mem_closedBall_zero_iff]
    have hu : ‖(u : E n)‖ ≤ 1 := (mem_closedBall_zero_iff).mp u.2
    have hnn : 0 ≤ 1 - ‖(u : E n)‖ ^ 2 := by nlinarith [norm_nonneg (u : E n)]
    have hs2 : s ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg s) hs
    have hnorm : ‖snocVec (u : E n) (s * Real.sqrt (1 - ‖(u : E n)‖ ^ 2))‖ ^ 2 =
        ‖(u : E n)‖ ^ 2 + s ^ 2 * (1 - ‖(u : E n)‖ ^ 2) := by
      rw [norm_sq_snocVec, mul_pow, Real.sq_sqrt hnn]
    have : ‖snocVec (u : E n) (s * Real.sqrt (1 - ‖(u : E n)‖ ^ 2))‖ ^ 2 ≤ 1 := by
      rw [hnorm]
      nlinarith
    nlinarith [norm_nonneg (snocVec (u : E n) (s * Real.sqrt (1 - ‖(u : E n)‖ ^ 2)))]⟩

lemma abs_affine (t : I) : |1 - 2 * (t : ℝ)| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [t.2.1, t.2.2]

lemma slice_eq_hemi_false {n : ℕ} (u : ClosedBall n) :
    slice n 1 (by norm_num) u = hemi n false u := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  simp [slice, hemi, snocVec]

lemma slice_eq_hemi_true {n : ℕ} (u : ClosedBall n) :
    slice n (-1) (by norm_num) u = hemi n true u := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  simp [slice, hemi, snocVec]

lemma sqrt_vanishes_on_sphere {n : ℕ} {u : ClosedBall n} (hu : u ∈ sphereSet n) :
    Real.sqrt (1 - ‖(u : E n)‖ ^ 2) = 0 := by
  have : ‖(u : E n)‖ = 1 := hu
  simp [this]

lemma slice_eq_on_sphere {n : ℕ} (s : ℝ) (hs : |s| ≤ 1) {u : ClosedBall n}
    (hu : u ∈ sphereSet n) : slice n s hs u = hemi n false u := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  simp [slice, hemi, sqrt_vanishes_on_sphere hu]

/-- The straight slice, as a continuous map `I × 𝔻 n → 𝔻 (n+1)`. -/
def sliceMap (n : ℕ) : C(I × ClosedBall n, ClosedBall (n + 1)) where
  toFun p := slice n (1 - 2 * (p.1 : ℝ)) (abs_affine p.1) p.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold snocVec
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    by_cases hi : (i : ℕ) < n
    · have hfun : (fun p : I × ClosedBall n =>
          (WithLp.toLp 2 (fun j => if h : (j : ℕ) < n then (p.2 : E n) ⟨j, h⟩ else
            (1 - 2 * (p.1 : ℝ)) * Real.sqrt (1 - ‖(p.2 : E n)‖ ^ 2)) : E (n + 1)) i) =
          fun p => (p.2 : E n) ⟨i, hi⟩ := by
        ext p
        simp only [PiLp.toLp_apply]
        rw [dif_pos hi]
      rw [hfun]
      exact (PiLp.continuous_apply 2 _ (⟨i, hi⟩ : Fin n)).comp
        (continuous_subtype_val.comp continuous_snd)
    · have hfun : (fun p : I × ClosedBall n =>
          (WithLp.toLp 2 (fun j => if h : (j : ℕ) < n then (p.2 : E n) ⟨j, h⟩ else
            (1 - 2 * (p.1 : ℝ)) * Real.sqrt (1 - ‖(p.2 : E n)‖ ^ 2)) : E (n + 1)) i) =
          fun p => (1 - 2 * (p.1 : ℝ)) * Real.sqrt (1 - ‖(p.2 : E n)‖ ^ 2) := by
        ext p
        simp only [PiLp.toLp_apply]
        rw [dif_neg hi]
      rw [hfun]
      exact (continuous_const.sub (continuous_const.mul
        (continuous_subtype_val.comp continuous_fst))).mul <|
        Real.continuous_sqrt.comp <| continuous_const.sub <|
          ((continuous_norm.comp continuous_subtype_val).comp continuous_snd).pow 2

lemma slice_coe {n : ℕ} {s s' : ℝ} {hs : |s| ≤ 1} {hs' : |s'| ≤ 1} {u : ClosedBall n}
    (h : s = s') : (slice n s hs u : E (n + 1)) = slice n s' hs' u := by
  cases h
  rfl

lemma sliceMap_zero {n : ℕ} (u : ClosedBall n) : sliceMap n (0, u) = hemi n false u := by
  apply Subtype.ext
  show (slice n (1 - 2 * (0 : ℝ)) (abs_affine 0) u : E (n + 1)) = (hemi n false u : E (n + 1))
  exact (slice_coe (by norm_num : (1 - 2 * (0 : ℝ)) = 1)).trans <|
    congrArg (fun z : ClosedBall (n + 1) => (z : E (n + 1))) (slice_eq_hemi_false u)

lemma sliceMap_one {n : ℕ} (u : ClosedBall n) : sliceMap n (1, u) = hemi n true u := by
  apply Subtype.ext
  show (slice n (1 - 2 * (1 : ℝ)) (abs_affine 1) u : E (n + 1)) = (hemi n true u : E (n + 1))
  exact (slice_coe (by norm_num : (1 - 2 * (1 : ℝ)) = -1)).trans <|
    congrArg (fun z : ClosedBall (n + 1) => (z : E (n + 1))) (slice_eq_hemi_true u)

lemma sliceMap_sphere {n : ℕ} (t : I) {u : ClosedBall n} (hu : u ∈ sphereSet n) :
    sliceMap n (t, u) = hemi n false u := by
  apply Subtype.ext
  show (slice n (1 - 2 * (t : ℝ)) (abs_affine t) u : E (n + 1)) = (hemi n false u : E (n + 1))
  exact congrArg (fun z : ClosedBall (n + 1) => (z : E (n + 1)))
    (slice_eq_on_sphere (1 - 2 * (t : ℝ)) (abs_affine t) hu)

/-- Sliding from the source hemisphere to the target hemisphere, fixed on the equator. -/
def sliceHomotopy (n : ℕ) :
    HomotopyRel (hemi n false) (hemi n true) (sphereSet n) where
  toFun p := sliceMap n p
  continuous_toFun := map_continuous (sliceMap n)
  map_zero_left := sliceMap_zero
  map_one_left := sliceMap_one
  prop' := fun t => by
    intro u hu
    simpa using sliceMap_sphere t hu

/-- A globe filler of two maps of pairs: an `(n+2)`-disk restricting to them on the hemispheres. -/
def globeRel {n : ℕ} {x : X} (f g : BallPair (n + 1) x) : Prop :=
  ∃ H : C(ClosedBall (n + 2), X),
    H.comp (hemi (n + 1) false) = f.1 ∧ H.comp (hemi (n + 1) true) = g.1

theorem homotopic_of_globeRel {n : ℕ} {x : X} {f g : BallPair (n + 1) x}
    (h : globeRel f g) : f.1.HomotopicRel g.1 (sphereSet (n + 1)) := by
  obtain ⟨H, h0, h1⟩ := h
  exact ⟨((sliceHomotopy (n + 1)).compContinuousMap H).cast h0 h1⟩

/-! ### From a homotopy back to a globe filler -/

lemma norm_dropLast_le {n : ℕ} (y : ClosedBall (n + 1)) :
    ‖dropLast (y : E (n + 1))‖ ≤ 1 := by
  have hy : ‖(y : E (n + 1))‖ ≤ 1 := (mem_closedBall_zero_iff).mp y.2
  have hy2 : ‖(y : E (n + 1))‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hy
  have hsq : ‖dropLast (y : E (n + 1))‖ ^ 2 ≤ 1 := by
    have h := norm_sq_dropLast (y : E (n + 1))
    linarith [sq_nonneg (lastCoord (y : E (n + 1)))]
  calc ‖dropLast (y : E (n + 1))‖
      = Real.sqrt (‖dropLast (y : E (n + 1))‖ ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hsq
    _ = 1 := by simp

/-- Drop the last coordinate, landing again in the closed disk. -/
def dropBall {n : ℕ} (y : ClosedBall (n + 1)) : ClosedBall n :=
  ⟨dropLast (y : E (n + 1)), (mem_closedBall_zero_iff).mpr (norm_dropLast_le y)⟩

lemma continuous_dropBall {n : ℕ} : Continuous (dropBall (n := n)) := by
  unfold dropBall
  apply Continuous.subtype_mk
  unfold dropLast
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  exact (PiLp.continuous_apply 2 _ i.castSucc).comp continuous_subtype_val

lemma dropBall_hemi {n : ℕ} (side : Bool) (u : ClosedBall n) :
    dropBall (hemi n side u) = u := by
  apply Subtype.ext
  simp [dropBall, hemi, dropLast_snocVec]

lemma abs_last_le_sqrt {n : ℕ} (y : ClosedBall (n + 1)) :
    |lastCoord (y : E (n + 1))| ≤
      Real.sqrt (1 - ‖dropLast (y : E (n + 1))‖ ^ 2) := by
  have hy : ‖(y : E (n + 1))‖ ≤ 1 := (mem_closedBall_zero_iff).mp y.2
  have hy2 : ‖(y : E (n + 1))‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hy
  have hsq : lastCoord (y : E (n + 1)) ^ 2 ≤ 1 - ‖dropLast (y : E (n + 1))‖ ^ 2 := by
    have h := norm_sq_dropLast (y : E (n + 1))
    linarith
  calc |lastCoord (y : E (n + 1))|
      = Real.sqrt (lastCoord (y : E (n + 1)) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (1 - ‖dropLast (y : E (n + 1))‖ ^ 2) := Real.sqrt_le_sqrt hsq

/-- Cylinder coordinate of an interior point `(v, t)`, with `‖v‖ < 1`. -/
def cylinderParam {n : ℕ} {y : ClosedBall (n + 2)}
    (hv : ‖dropLast (y : E (n + 2))‖ < 1) : I :=
  let h := Real.sqrt (1 - ‖dropLast (y : E (n + 2))‖ ^ 2)
  let s := lastCoord (y : E (n + 2)) / h
  ⟨(1 - s) / 2, by
    have hpos : 0 < 1 - ‖dropLast (y : E (n + 2))‖ ^ 2 := by
      have hv0 : 0 ≤ ‖dropLast (y : E (n + 2))‖ := norm_nonneg _
      nlinarith
    have hh : 0 < h := (Real.sqrt_pos).2 hpos
    have hs : |s| ≤ 1 := by
      rw [abs_div, abs_of_pos hh]
      exact (div_le_one hh).2 (abs_last_le_sqrt y)
    rw [abs_le] at hs
    constructor <;> linarith⟩

lemma continuous_cylinderCoord {n : ℕ} :
    Continuous fun y : {y : ClosedBall (n + 2) // ‖dropLast (y : E (n + 2))‖ < 1} =>
      (1 - lastCoord (y.1 : E (n + 2)) /
        Real.sqrt (1 - ‖dropLast (y.1 : E (n + 2))‖ ^ 2)) / 2 := by
  have hlast : Continuous fun y : {y : ClosedBall (n + 2) // ‖dropLast (y : E (n + 2))‖ < 1} =>
      lastCoord (y.1 : E (n + 2)) :=
    (PiLp.continuous_apply 2 _ (Fin.last (n + 1))).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  have hdrop : Continuous fun y : {y : ClosedBall (n + 2) // ‖dropLast (y : E (n + 2))‖ < 1} =>
      dropLast (y.1 : E (n + 2)) := by
    unfold dropLast
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact (PiLp.continuous_apply 2 _ i.castSucc).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  have hden : Continuous fun y : {y : ClosedBall (n + 2) // ‖dropLast (y : E (n + 2))‖ < 1} =>
      Real.sqrt (1 - ‖dropLast (y.1 : E (n + 2))‖ ^ 2) :=
    Real.continuous_sqrt.comp (continuous_const.sub ((continuous_norm.comp hdrop).pow 2))
  have hne : ∀ y : {y : ClosedBall (n + 2) // ‖dropLast (y : E (n + 2))‖ < 1},
      Real.sqrt (1 - ‖dropLast (y.1 : E (n + 2))‖ ^ 2) ≠ 0 := by
    intro y
    have hpos : 0 < 1 - ‖dropLast (y.1 : E (n + 2))‖ ^ 2 := by
      nlinarith [norm_nonneg (dropLast (y.1 : E (n + 2))), y.2]
    exact (Real.sqrt_pos.2 hpos).ne'
  exact (continuous_const.sub (hlast.div hden hne)).div_const 2

lemma coe_cylinderParam {n : ℕ} {y : ClosedBall (n + 2)}
    (hv : ‖dropLast (y : E (n + 2))‖ < 1) :
    (cylinderParam hv : ℝ) =
      (1 - lastCoord (y : E (n + 2)) /
        Real.sqrt (1 - ‖dropLast (y : E (n + 2))‖ ^ 2)) / 2 := rfl

lemma continuous_cylinderParam_subtype {n : ℕ} :
    Continuous fun y : {y : ClosedBall (n + 2) // ‖dropLast (y : E (n + 2))‖ < 1} =>
      (cylinderParam y.2 : ℝ) :=
  continuous_cylinderCoord.congr fun y => (coe_cylinderParam y.2).symm

/-- Read a homotopy relative to the sphere as a filler of the two hemispheres. -/
def fillerOfHomotopy {n : ℕ} {x : X} {f g : BallPair (n + 1) x}
    (K : f.1.HomotopyRel g.1 (sphereSet (n + 1))) : C(ClosedBall (n + 2), X) where
  toFun y :=
    if hv : ‖dropLast (y : E (n + 2))‖ < 1 then
      K (cylinderParam hv, dropBall y)
    else
      x
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro y0
    by_cases hv0 : ‖dropLast (y0 : E (n + 2))‖ < 1
    · let s : Set (ClosedBall (n + 2)) := {y | ‖dropLast (y : E (n + 2))‖ < 1}
      have hdropc : Continuous fun y : ClosedBall (n + 2) => dropLast (y : E (n + 2)) := by
        unfold dropLast
        refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
        exact (PiLp.continuous_apply 2 _ i.castSucc).comp continuous_subtype_val
      have hsopen : IsOpen s := isOpen_lt (continuous_norm.comp hdropc) continuous_const
      let ι : ↑s → I × ClosedBall (n + 1) := fun y => (cylinderParam y.2, dropBall y.1)
      have hτ : Continuous (fun y : ↑s => cylinderParam y.2) :=
        continuous_induced_rng.mpr (continuous_cylinderParam_subtype (n := n))
      have hι : Continuous ι :=
        Continuous.prodMk hτ (continuous_dropBall.comp continuous_subtype_val)
      have hrest : Continuous (s.domRestrict fun y =>
          if hv : ‖dropLast (y : E (n + 2))‖ < 1 then
            K (cylinderParam hv, dropBall y) else x) := by
        have heq : s.domRestrict (fun y =>
            if hv : ‖dropLast (y : E (n + 2))‖ < 1 then
              K (cylinderParam hv, dropBall y) else x) = (⇑K) ∘ ι := by
          funext y
          rw [Set.domRestrict_apply]
          have hy : ‖dropLast (y.1 : E (n + 2))‖ < 1 := y.2
          rw [dite_eq_left hy]
          show K (cylinderParam hy, dropBall y.1) = K (cylinderParam y.2, dropBall y.1)
          exact congrArg (⇑K) (Prod.ext (Subtype.ext rfl) rfl)
        rw [heq]
        exact (map_continuous K).comp hι
      rw [← continuousOn_iff_continuous_domRestrict] at hrest
      exact hrest.continuousAt (hsopen.mem_nhds hv0)
    · let f0 : ClosedBall (n + 2) → X := fun y =>
        if hv : ‖dropLast (y : E (n + 2))‖ < 1 then
          K (cylinderParam hv, dropBall y) else x
      change ContinuousAt f0 y0
      have hy0x : f0 y0 = x := dite_eq_right hv0
      suffices Filter.Tendsto f0 (𝓝 y0) (𝓝 x) by
        change Filter.Tendsto f0 (𝓝 y0) (𝓝 (f0 y0))
        exact hy0x.symm ▸ this
      rw [tendsto_nhds]
      intro N hNopen hxN
      let u0 : ClosedBall (n + 1) := dropBall y0
      have hEq : ‖(u0 : E (n + 1))‖ = 1 := by
        have hle : ‖dropLast (y0 : E (n + 2))‖ ≤ 1 := norm_dropLast_le (n := n + 1) y0
        have hEq' : ‖dropLast (y0 : E (n + 2))‖ = 1 := le_antisymm hle (not_lt.mp hv0)
        simpa [u0, dropBall] using hEq'
      have hu0 : u0 ∈ sphereSet (n + 1) := hEq
      have hpre : (Set.univ : Set I) ×ˢ {u0} ⊆ (⇑K) ⁻¹' N := by
        intro p hp
        obtain ⟨-, hp2⟩ := Set.mem_prod.mp hp
        have hp2' : p.2 = u0 := Set.mem_singleton_iff.mp hp2
        have hp_eq : p = (p.1, u0) := Prod.ext rfl hp2'
        rw [Set.mem_preimage, hp_eq, K.eq_fst p.1 hu0, f.2 u0 hu0]
        exact hxN
      obtain ⟨U, W, -, hW, hUuniv, hu0W, hUW⟩ :=
        generalized_tube_lemma isCompact_univ (isCompact_singleton (x := u0))
          (hNopen.preimage (map_continuous K)) hpre
      refine mem_nhds_iff.mpr ⟨dropBall ⁻¹' W, ?_, hW.preimage continuous_dropBall, ?_⟩
      · intro y hy
        rw [Set.mem_preimage] at hy ⊢
        show (if hv : ‖dropLast (y : E (n + 2))‖ < 1 then
          K (cylinderParam hv, dropBall y) else x) ∈ N
        by_cases hyv : ‖dropLast (y : E (n + 2))‖ < 1
        · rw [dite_eq_left hyv]
          exact hUW (Set.mem_prod.mpr ⟨hUuniv (Set.mem_univ (cylinderParam hyv)), hy⟩)
        · rw [dite_eq_right hyv]
          exact hxN
      · rw [Set.mem_preimage]
        exact Set.singleton_subset_iff.mp hu0W

lemma fillerOfHomotopy_apply {n : ℕ} {x : X} {f g : BallPair (n + 1) x}
    (K : f.1.HomotopyRel g.1 (sphereSet (n + 1))) (y : ClosedBall (n + 2)) :
    fillerOfHomotopy K y =
      if hv : ‖dropLast (y : E (n + 2))‖ < 1 then
        K (cylinderParam hv, dropBall y) else x :=
  rfl

lemma filler_hemi_false {n : ℕ} {x : X} {f g : BallPair (n + 1) x}
    (K : f.1.HomotopyRel g.1 (sphereSet (n + 1))) (u : ClosedBall (n + 1)) :
    fillerOfHomotopy K (hemi (n + 1) false u) = f.1 u := by
  by_cases hu : ‖(u : E (n + 1))‖ < 1
  · have hv : ‖dropLast ((hemi (n + 1) false u) : E (n + 2))‖ < 1 := by
      simpa [hemi, dropLast_snocVec] using hu
    have hτ : cylinderParam hv = 0 := by
      apply Subtype.ext
      have hlast : lastCoord ((hemi (n + 1) false u) : E (n + 2)) =
          Real.sqrt (1 - ‖(u : E (n + 1))‖ ^ 2) := by
        simp [hemi, lastCoord_snocVec]
      have hdrop : dropLast ((hemi (n + 1) false u) : E (n + 2)) = (u : E (n + 1)) := by
        simp [hemi, dropLast_snocVec]
      rw [coe_cylinderParam, hlast, hdrop]
      have hpos : 0 < Real.sqrt (1 - ‖(u : E (n + 1))‖ ^ 2) := by
        rw [Real.sqrt_pos]
        nlinarith [norm_nonneg (u : E (n + 1)), hu]
      rw [div_self (ne_of_gt hpos)]
      norm_num
    rw [fillerOfHomotopy_apply, dite_eq_left hv, hτ, dropBall_hemi]
    exact K.map_zero_left u
  · have hsphere : u ∈ sphereSet (n + 1) := by
      have hle : ‖(u : E (n + 1))‖ ≤ 1 := (mem_closedBall_zero_iff).mp u.2
      exact le_antisymm hle (not_lt.mp hu)
    have hv : ¬ ‖dropLast ((hemi (n + 1) false u) : E (n + 2))‖ < 1 := by
      simpa [hemi, dropLast_snocVec] using hu
    rw [fillerOfHomotopy_apply, dite_eq_right hv]
    exact (f.2 u hsphere).symm

lemma filler_hemi_true {n : ℕ} {x : X} {f g : BallPair (n + 1) x}
    (K : f.1.HomotopyRel g.1 (sphereSet (n + 1))) (u : ClosedBall (n + 1)) :
    fillerOfHomotopy K (hemi (n + 1) true u) = g.1 u := by
  by_cases hu : ‖(u : E (n + 1))‖ < 1
  · have hv : ‖dropLast ((hemi (n + 1) true u) : E (n + 2))‖ < 1 := by
      simpa [hemi, dropLast_snocVec] using hu
    have hτ : cylinderParam hv = 1 := by
      apply Subtype.ext
      have hlast : lastCoord ((hemi (n + 1) true u) : E (n + 2)) =
          -Real.sqrt (1 - ‖(u : E (n + 1))‖ ^ 2) := by
        simp [hemi, lastCoord_snocVec]
      have hdrop : dropLast ((hemi (n + 1) true u) : E (n + 2)) = (u : E (n + 1)) := by
        simp [hemi, dropLast_snocVec]
      rw [coe_cylinderParam, hlast, hdrop]
      have hpos : 0 < Real.sqrt (1 - ‖(u : E (n + 1))‖ ^ 2) := by
        rw [Real.sqrt_pos]
        nlinarith [norm_nonneg (u : E (n + 1)), hu]
      rw [neg_div, div_self (ne_of_gt hpos)]
      norm_num
    rw [fillerOfHomotopy_apply, dite_eq_left hv, hτ, dropBall_hemi]
    exact K.map_one_left u
  · have hsphere : u ∈ sphereSet (n + 1) := by
      have hle : ‖(u : E (n + 1))‖ ≤ 1 := (mem_closedBall_zero_iff).mp u.2
      exact le_antisymm hle (not_lt.mp hu)
    have hv : ¬ ‖dropLast ((hemi (n + 1) true u) : E (n + 2))‖ < 1 := by
      simpa [hemi, dropLast_snocVec] using hu
    rw [fillerOfHomotopy_apply, dite_eq_right hv]
    exact (g.2 u hsphere).symm

theorem globeRel_of_homotopic {n : ℕ} {x : X} {f g : BallPair (n + 1) x}
    (h : f.1.HomotopicRel g.1 (sphereSet (n + 1))) : globeRel f g := by
  obtain ⟨K⟩ := h
  refine ⟨fillerOfHomotopy K, ?_, ?_⟩
  · ext u; exact filler_hemi_false K u
  · ext u; exact filler_hemi_true K u

theorem globeRel_iff_homotopic {n : ℕ} {x : X} (f g : BallPair (n + 1) x) :
    globeRel f g ↔ f.1.HomotopicRel g.1 (sphereSet (n + 1)) :=
  ⟨homotopic_of_globeRel, globeRel_of_homotopic⟩

/-! ### The cube and the disk

For `n ≥ 1`, affine coordinates `I → [-1, 1]` followed by the radial map
`x ↦ (‖x‖_∞ / ‖x‖₂) • x` identify the cube with the disk, and the cube boundary
with the sphere.
-/

lemma finNonempty (n : ℕ) [NeZero n] : Nonempty (Fin n) :=
  ⟨⟨0, NeZero.pos n⟩⟩

lemma univNonempty (n : ℕ) [NeZero n] : (Finset.univ : Finset (Fin n)).Nonempty :=
  Finset.univ_nonempty_iff.mpr (finNonempty n)

/-- Supremum norm on `ℝⁿ`. -/
def supNorm {n : ℕ} [NeZero n] (x : E n) : ℝ :=
  Finset.univ.sup' (univNonempty n) fun i => |x i|

lemma supNorm_nonneg {n : ℕ} [NeZero n] (x : E n) : 0 ≤ supNorm x := by
  unfold supNorm
  exact Finset.le_sup' _ (Finset.mem_univ (⟨0, NeZero.pos n⟩ : Fin n)) |>.trans' (abs_nonneg _)

lemma abs_le_supNorm {n : ℕ} [NeZero n] (x : E n) (i : Fin n) : |x i| ≤ supNorm x := by
  unfold supNorm
  exact Finset.le_sup' (fun j => |x j|) (Finset.mem_univ i)

lemma supNorm_le_norm {n : ℕ} [NeZero n] (x : E n) : supNorm x ≤ ‖x‖ := by
  unfold supNorm
  rw [Finset.sup'_le_iff]
  intro i _
  simpa using PiLp.norm_apply_le x i

lemma supNorm_zero {n : ℕ} [NeZero n] : supNorm (0 : E n) = 0 := by
  unfold supNorm
  simp [Finset.sup'_const]

lemma supNorm_eq_zero_iff {n : ℕ} [NeZero n] {x : E n} : supNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext i
    have hi : |x i| ≤ 0 := by simpa [h] using abs_le_supNorm x i
    exact abs_eq_zero.mp (le_antisymm hi (abs_nonneg _))
  · rintro rfl
    exact supNorm_zero

lemma supNorm_smul {n : ℕ} [NeZero n] (c : ℝ) (x : E n) :
    supNorm (c • x) = |c| * supNorm x := by
  unfold supNorm
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul]
  exact (Finset.mul₀_sup' (abs_nonneg c) (fun i => |x i|) Finset.univ (univNonempty n)).symm

lemma continuous_supNorm {n : ℕ} [NeZero n] : Continuous (supNorm (n := n)) := by
  unfold supNorm
  refine Continuous.finset_sup'_apply (univNonempty n) ?_
  intro i _
  exact continuous_abs.comp (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i)

/-- Radial projection sending the cube `‖x‖_∞ ≤ 1` onto the Euclidean disk. -/
def radial {n : ℕ} [NeZero n] (x : E n) : E n :=
  (supNorm x / ‖x‖) • x

/-- Inverse radial projection. -/
def radialInv {n : ℕ} [NeZero n] (y : E n) : E n :=
  (‖y‖ / supNorm y) • y

lemma norm_radial {n : ℕ} [NeZero n] (x : E n) : ‖radial x‖ = supNorm x := by
  by_cases hx : x = 0
  · simp [radial, hx, supNorm_zero]
  · rw [radial, norm_smul]
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hs : 0 ≤ supNorm x / ‖x‖ := div_nonneg (supNorm_nonneg x) (norm_nonneg _)
    rw [Real.norm_of_nonneg hs, div_mul_cancel₀ _ hr.ne']

lemma supNorm_radialInv {n : ℕ} [NeZero n] (y : E n) : supNorm (radialInv y) = ‖y‖ := by
  by_cases hy : y = 0
  · simp [radialInv, hy, supNorm_zero]
  · have hspos : 0 < supNorm y := lt_of_le_of_ne (supNorm_nonneg y)
      (Ne.symm ((supNorm_eq_zero_iff).not.mpr hy))
    rw [radialInv, supNorm_smul]
    have hc : 0 ≤ ‖y‖ / supNorm y := div_nonneg (norm_nonneg _) hspos.le
    rw [abs_of_nonneg hc, div_mul_cancel₀ _ hspos.ne']

lemma norm_le_sqrt_supNorm {n : ℕ} [NeZero n] (x : E n) :
    ‖x‖ ≤ Real.sqrt (n : ℝ) * supNorm x := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hs : 0 ≤ supNorm x := supNorm_nonneg x
  have hsq : ‖x‖ ^ 2 ≤ (n : ℝ) * supNorm x ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hsum : ∑ i : Fin n, |x i| ^ 2 ≤ ∑ _ : Fin n, supNorm x ^ 2 := by
      gcongr
      exact abs_le_supNorm x _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    simpa [sq_abs] using hsum
  calc ‖x‖
      = Real.sqrt (‖x‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt ((n : ℝ) * supNorm x ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (n : ℝ) * supNorm x := by rw [Real.sqrt_mul hn, Real.sqrt_sq hs]

lemma norm_radialInv_le {n : ℕ} [NeZero n] (y : E n) :
    ‖radialInv y‖ ≤ Real.sqrt (n : ℝ) * ‖y‖ := by
  rw [← supNorm_radialInv y]
  exact norm_le_sqrt_supNorm (radialInv y)

lemma continuous_radial {n : ℕ} [NeZero n] : Continuous (radial (n := n)) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have h0 : radial (0 : E n) = 0 := by simp [radial, supNorm_zero]
    change Filter.Tendsto radial (𝓝 (0 : E n)) (𝓝 (radial (0 : E n)))
    rw [h0]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hupper : Filter.Tendsto (fun y : E n => ‖y‖) (𝓝 (0 : E n)) (𝓝 0) := by
      simpa using continuous_norm.tendsto (0 : E n)
    refine squeeze_zero (fun y => norm_nonneg (radial y)) ?_ hupper
    intro y
    rw [norm_radial]
    exact supNorm_le_norm y
  · have hr : ‖x‖ ≠ 0 := (norm_pos_iff.mpr hx).ne'
    unfold radial
    exact (continuous_supNorm.continuousAt.div continuous_norm.continuousAt hr).smul continuousAt_id

lemma continuous_radialInv {n : ℕ} [NeZero n] : Continuous (radialInv (n := n)) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y = 0
  · subst hy
    have h0 : radialInv (0 : E n) = 0 := by simp [radialInv, supNorm_zero]
    change Filter.Tendsto radialInv (𝓝 (0 : E n)) (𝓝 (radialInv (0 : E n)))
    rw [h0]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbase : Filter.Tendsto (fun z : E n => ‖z‖) (𝓝 (0 : E n)) (𝓝 0) := by
      simpa using continuous_norm.tendsto (0 : E n)
    have hupper : Filter.Tendsto (fun z : E n => Real.sqrt (n : ℝ) * ‖z‖) (𝓝 0) (𝓝 0) := by
      simpa using hbase.const_mul (Real.sqrt (n : ℝ))
    exact squeeze_zero (fun z => norm_nonneg (radialInv z)) norm_radialInv_le hupper
  · have hs : supNorm y ≠ 0 := (supNorm_eq_zero_iff).not.mpr hy
    unfold radialInv
    exact (continuous_norm.continuousAt.div continuous_supNorm.continuousAt hs).smul continuousAt_id

lemma radialInv_radial {n : ℕ} [NeZero n] (x : E n) : radialInv (radial x) = x := by
  by_cases hx : x = 0
  · simp [radial, radialInv, hx]
  · have hr : ‖x‖ ≠ 0 := (norm_pos_iff.mpr hx).ne'
    have hspos : 0 < supNorm x :=
      lt_of_le_of_ne (supNorm_nonneg x) (Ne.symm ((supNorm_eq_zero_iff).not.mpr hx))
    have hsup : supNorm (radial x) = supNorm x ^ 2 / ‖x‖ := by
      rw [radial, supNorm_smul, abs_of_nonneg (div_nonneg (supNorm_nonneg x) (norm_nonneg _))]
      ring
    rw [radialInv, norm_radial, hsup, radial, smul_smul]
    have hc : supNorm x / (supNorm x ^ 2 / ‖x‖) * (supNorm x / ‖x‖) = 1 := by
      field_simp [hr, hspos.ne']
    rw [hc, one_smul]

lemma radial_radialInv {n : ℕ} [NeZero n] (y : E n) : radial (radialInv y) = y := by
  by_cases hy : y = 0
  · simp [radial, radialInv, hy]
  · have hspos : 0 < supNorm y :=
      lt_of_le_of_ne (supNorm_nonneg y) (Ne.symm ((supNorm_eq_zero_iff).not.mpr hy))
    have hr : ‖y‖ ≠ 0 := (norm_pos_iff.mpr hy).ne'
    have hnorm : ‖radialInv y‖ = ‖y‖ ^ 2 / supNorm y := by
      rw [radialInv, norm_smul, Real.norm_of_nonneg (div_nonneg (norm_nonneg _) hspos.le)]
      ring
    rw [radial, hnorm, supNorm_radialInv, radialInv, smul_smul]
    have hc : ‖y‖ / (‖y‖ ^ 2 / supNorm y) * (‖y‖ / supNorm y) = 1 := by
      field_simp [hr, hspos.ne']
    rw [hc, one_smul]

/-- Affine identification of the unit interval with `[-1, 1]`. -/
def aff (t : I) : ℝ := 2 * (t : ℝ) - 1

lemma abs_aff (t : I) : |aff t| ≤ 1 := by
  rw [aff, abs_le]
  constructor <;> linarith [t.2.1, t.2.2]

lemma aff_zero : aff 0 = -1 := by simp [aff]

lemma aff_one : aff 1 = 1 := by
  simp [aff]
  norm_num

def unaff (s : ℝ) (hs : |s| ≤ 1) : I :=
  ⟨(s + 1) / 2, by rw [abs_le] at hs; constructor <;> linarith⟩

lemma aff_unaff (s : ℝ) (hs : |s| ≤ 1) : aff (unaff s hs) = s := by
  simp [aff, unaff]
  ring

lemma unaff_aff (t : I) : unaff (aff t) (abs_aff t) = t := by
  apply Subtype.ext
  simp [aff, unaff]

lemma aff_eq_one_iff (t : I) : aff t = 1 ↔ t = 1 := by
  constructor
  · intro h
    apply Subtype.ext
    show (t : ℝ) = 1
    linarith [show 2 * (t : ℝ) - 1 = 1 by simpa [aff] using h]
  · rintro rfl
    exact aff_one

lemma aff_eq_neg_one_iff (t : I) : aff t = -1 ↔ t = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    show (t : ℝ) = 0
    linarith [show 2 * (t : ℝ) - 1 = -1 by simpa [aff] using h]
  · rintro rfl
    exact aff_zero

/-- Send a cube point to the cube `[-1, 1]ⁿ` inside Euclidean space. -/
def boxOfCube {n : ℕ} [NeZero n] (p : Fin n → I) : E n :=
  WithLp.toLp 2 fun i => aff (p i)

lemma boxOfCube_apply {n : ℕ} [NeZero n] (p : Fin n → I) (i : Fin n) :
    boxOfCube p i = aff (p i) := by
  simp [boxOfCube, PiLp.toLp_apply]

lemma continuous_boxOfCube {n : ℕ} [NeZero n] : Continuous (boxOfCube (n := n)) := by
  unfold boxOfCube
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  exact ((continuous_const.mul continuous_subtype_val).sub continuous_const).comp (continuous_apply i)

lemma supNorm_boxOfCube {n : ℕ} [NeZero n] (p : Fin n → I) : supNorm (boxOfCube p) ≤ 1 := by
  unfold supNorm
  rw [Finset.sup'_le_iff]
  intro i _
  rw [boxOfCube_apply]
  exact abs_aff (p i)

/-- The closed disk, as the radial image of the cube. -/
def toBall {n : ℕ} [NeZero n] (p : Fin n → I) : ClosedBall n :=
  ⟨radial (boxOfCube p), (mem_closedBall_zero_iff).mpr <| by
    rw [norm_radial]
    exact supNorm_boxOfCube p⟩

lemma continuous_toBall {n : ℕ} [NeZero n] : Continuous (toBall (n := n)) := by
  unfold toBall
  apply Continuous.subtype_mk
  exact continuous_radial.comp continuous_boxOfCube

lemma abs_radialInv_coord {n : ℕ} [NeZero n] (y : E n) (hy : ‖y‖ ≤ 1) (i : Fin n) :
    |radialInv y i| ≤ 1 := by
  calc |radialInv y i|
      ≤ supNorm (radialInv y) := abs_le_supNorm _ i
    _ = ‖y‖ := supNorm_radialInv y
    _ ≤ 1 := hy

/-- Inverse of `toBall`, reading affine coordinates of the inverse radial image. -/
def cubeOfBall {n : ℕ} [NeZero n] (y : ClosedBall n) : Fin n → I :=
  fun i => unaff (radialInv (y : E n) i)
    (abs_radialInv_coord (y : E n) ((mem_closedBall_zero_iff).mp y.2) i)

lemma continuous_cubeOfBall {n : ℕ} [NeZero n] : Continuous (cubeOfBall (n := n)) := by
  refine continuous_pi fun i => ?_
  unfold cubeOfBall unaff
  apply Continuous.subtype_mk
  have hcoord : Continuous fun y : ClosedBall n => radialInv (y : E n) i :=
    (PiLp.continuous_apply 2 _ i).comp (continuous_radialInv.comp continuous_subtype_val)
  exact (hcoord.add continuous_const).div_const 2

lemma cubeOfBall_toBall {n : ℕ} [NeZero n] (p : Fin n → I) : cubeOfBall (toBall p) = p := by
  funext i
  apply Subtype.ext
  simp only [cubeOfBall, toBall, radialInv_radial, boxOfCube_apply, unaff, aff]
  ring

lemma toBall_cubeOfBall {n : ℕ} [NeZero n] (y : ClosedBall n) : toBall (cubeOfBall y) = y := by
  apply Subtype.ext
  have hbox : boxOfCube (cubeOfBall y) = radialInv (y : E n) := by
    ext i
    simp [boxOfCube_apply, cubeOfBall, aff_unaff]
  simp [toBall, hbox, radial_radialInv]

/-- Homeomorphism between the cube `Iⁿ` and the closed disk. -/
def ballCubeHomeo {n : ℕ} [NeZero n] : (Fin n → I) ≃ₜ ClosedBall n where
  toFun := toBall
  invFun := cubeOfBall
  left_inv := cubeOfBall_toBall
  right_inv := toBall_cubeOfBall
  continuous_toFun := continuous_toBall
  continuous_invFun := continuous_cubeOfBall

lemma toBall_mem_sphere_iff {n : ℕ} [NeZero n] (p : Fin n → I) :
    toBall p ∈ sphereSet n ↔ p ∈ Cube.boundary (Fin n) := by
  rw [sphereSet, Set.mem_setOf]
  have hnorm : ‖(toBall p : E n)‖ = supNorm (boxOfCube p) := by simp [toBall, norm_radial]
  rw [hnorm]
  constructor
  · intro hsup
    have hge : (1 : ℝ) ≤ supNorm (boxOfCube p) := by simp [hsup]
    rw [supNorm, Finset.le_sup'_iff] at hge
    obtain ⟨i, -, hi⟩ := hge
    have habs : |aff (p i)| = 1 :=
      le_antisymm (abs_aff (p i)) (by simpa [boxOfCube_apply] using hi)
    rcases (abs_eq (zero_le_one : (0 : ℝ) ≤ 1)).mp habs with h | h
    · exact ⟨i, Or.inr ((aff_eq_one_iff (p i)).mp h)⟩
    · exact ⟨i, Or.inl ((aff_eq_neg_one_iff (p i)).mp h)⟩
  · intro ⟨i, hi⟩
    apply le_antisymm (supNorm_boxOfCube p)
    have hcoord : |aff (p i)| = 1 := by
      rcases hi with h0 | h1
      · simp [h0, aff_zero]
      · simp [h1, aff_one]
    calc (1 : ℝ)
        = |boxOfCube p i| := by simp [boxOfCube_apply, hcoord]
      _ ≤ supNorm (boxOfCube p) := abs_le_supNorm _ i

/-- The cube-to-disk homeomorphism, as a continuous map. -/
def toBallMap {n : ℕ} [NeZero n] : C(Fin n → I, ClosedBall n) :=
  ⟨toBall, continuous_toBall⟩

/-- The disk-to-cube homeomorphism, as a continuous map. -/
def cubeOfBallMap {n : ℕ} [NeZero n] : C(ClosedBall n, Fin n → I) :=
  ⟨cubeOfBall, continuous_cubeOfBall⟩

lemma toBallMap_cubeOfBallMap {n : ℕ} [NeZero n] :
    toBallMap.comp cubeOfBallMap = ContinuousMap.id (ClosedBall n) := by
  ext y
  simp [toBallMap, cubeOfBallMap, toBall_cubeOfBall]

lemma cubeOfBallMap_toBallMap {n : ℕ} [NeZero n] :
    cubeOfBallMap.comp toBallMap = ContinuousMap.id (Fin n → I) := by
  ext p
  simp [toBallMap, cubeOfBallMap, cubeOfBall_toBall]

lemma toBall_preimage_sphere {n : ℕ} [NeZero n] :
    toBallMap ⁻¹' sphereSet n = Cube.boundary (Fin n) := by
  ext p
  simp [toBallMap, toBall_mem_sphere_iff]

lemma cubeOfBall_preimage_boundary {n : ℕ} [NeZero n] :
    cubeOfBallMap ⁻¹' Cube.boundary (Fin n) = sphereSet n := by
  ext y
  rw [Set.mem_preimage, show cubeOfBallMap y = cubeOfBall y from rfl,
    ← toBall_mem_sphere_iff (cubeOfBall y), toBall_cubeOfBall]

/-- Precompose a homotopy relative to a set. -/
def homotopyRelPrecomp {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f₀ f₁ : C(B, X)} {S : Set B} (F : HomotopyRel f₀ f₁ S) (g : C(A, B)) :
    HomotopyRel (f₀.comp g) (f₁.comp g) (g ⁻¹' S) where
  toFun p := F (p.1, g p.2)
  continuous_toFun :=
    (map_continuous F).comp (continuous_fst.prodMk ((map_continuous g).comp continuous_snd))
  map_zero_left x := F.map_zero_left (g x)
  map_one_left x := F.map_one_left (g x)
  prop' t x hx := F.prop t (g x) hx

/-- Replace the set that a relative homotopy is fixed on. -/
def homotopyRelCastSet {D : Type*} [TopologicalSpace D] {f₀ f₁ : C(D, X)} {S T : Set D}
    (F : HomotopyRel f₀ f₁ S) (h : S = T) : HomotopyRel f₀ f₁ T where
  toFun p := F p
  continuous_toFun := map_continuous F
  map_zero_left := F.map_zero_left
  map_one_left := F.map_one_left
  prop' t x hx := F.prop t x (by simpa [h] using hx)

theorem homotopic_sphere_iff_boundary {n : ℕ} [NeZero n] (f g : C(ClosedBall n, X)) :
    f.HomotopicRel g (sphereSet n) ↔
      (f.comp toBallMap).HomotopicRel (g.comp toBallMap) (Cube.boundary (Fin n)) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨homotopyRelCastSet (homotopyRelPrecomp F toBallMap) toBall_preimage_sphere⟩
  · rintro ⟨G⟩
    let G' := homotopyRelCastSet (homotopyRelPrecomp G cubeOfBallMap)
      cubeOfBall_preimage_boundary
    have hf : (f.comp toBallMap).comp cubeOfBallMap = f := by
      rw [ContinuousMap.comp_assoc, toBallMap_cubeOfBallMap, ContinuousMap.comp_id]
    have hg : (g.comp toBallMap).comp cubeOfBallMap = g := by
      rw [ContinuousMap.comp_assoc, toBallMap_cubeOfBallMap, ContinuousMap.comp_id]
    exact ⟨G'.cast hf hg⟩

/-- Maps of pairs `(𝔻ⁿ, S^{n-1})` are Mathlib's generalized loops on the cube. -/
def ballPairEquivGenLoop {n : ℕ} [NeZero n] (x : X) :
    BallPair n x ≃ GenLoop (Fin n) X x where
  toFun f := ⟨f.1.comp toBallMap, fun y hy =>
    f.2 (toBall y) ((toBall_mem_sphere_iff y).mpr hy)⟩
  invFun g := ⟨g.1.comp cubeOfBallMap, fun y hy =>
    g.2 (cubeOfBall y) ((toBall_mem_sphere_iff (cubeOfBall y)).mp <| by
      simpa [toBall_cubeOfBall] using hy)⟩
  left_inv f := by
    apply Subtype.ext
    ext y
    simp [toBallMap, cubeOfBallMap, toBall_cubeOfBall]
  right_inv g := by
    apply Subtype.ext
    ext y
    simp [toBallMap, cubeOfBallMap, cubeOfBall_toBall]

theorem ballPair_homotopic_iff_genLoop {n : ℕ} [NeZero n] {x : X} (f g : BallPair n x) :
    f.1.HomotopicRel g.1 (sphereSet n) ↔
      GenLoop.Homotopic (ballPairEquivGenLoop x f) (ballPairEquivGenLoop x g) := by
  rw [GenLoop.Homotopic]
  exact homotopic_sphere_iff_boundary f.1 g.1

/-- Postcomposition by a map of spaces commutes with the cube equivalence. -/
lemma ballPairEquivGenLoop_postcomp {n : ℕ} [NeZero n] {Y : Type*} [TopologicalSpace Y]
    (φ : C(X, Y)) (x : X) (f : BallPair n x) :
    (ballPairEquivGenLoop (φ x) ⟨φ.comp f.1, fun y hy => by simp [f.2 y hy]⟩).1 =
      φ.comp (ballPairEquivGenLoop x f).1 := by
  have hL : (ballPairEquivGenLoop (φ x) ⟨φ.comp f.1, fun y hy => by simp [f.2 y hy]⟩).1
      = (φ.comp f.1).comp toBallMap := rfl
  have hR : (ballPairEquivGenLoop x f).1 = f.1.comp toBallMap := rfl
  rw [hL, hR, ContinuousMap.comp_assoc]

end HomotopyHypothesis.Comparison.FundamentalGroupoid.Geom
