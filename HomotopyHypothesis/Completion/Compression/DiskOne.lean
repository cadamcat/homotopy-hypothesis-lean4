import HomotopyHypothesis.Blueprint.Defs
/-
# One-dimensional disks and spheres

The 1-disk is the interval and its boundary is two points. This file records
the norm identity, the sphere and ball descriptions, the coordinate maps of
the interval homeomorphism with their continuity, the roundtrips, the
resulting homeomorphism and TopCat isomorphism, finiteness/discreteness of
the 1-sphere, maps out of it from pairs of points, explicit sphere points,
and backward endpoint identities, toward injectivity on path components.
-/
noncomputable section

namespace HomotopyHypothesis.Completion.Compression

universe u

open CategoryTheory TopCat Topology

lemma norm_fin1 (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), Real.norm_eq_abs]

lemma mem_sphere_fin1 (x : EuclideanSpace ℝ (Fin 1)) :
    x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 ↔ x 0 = 1 ∨ x 0 = -1 := by
  rw [Metric.mem_sphere, dist_zero_right, norm_fin1]
  constructor
  · intro h
    have hsq : (x 0) ^ 2 = 1 := by
      have : |x 0| ^ 2 = 1 := by rw [h, one_pow]
      rwa [sq_abs] at this
    exact sq_eq_one_iff.mp hsq
  · rintro (h | h)
    · rw [h]; simp
    · rw [h]; simp

/-- The 1-disk is the interval `|x| ≤ 1` in the single coordinate. -/
lemma mem_closedBall_fin1 (x : EuclideanSpace ℝ (Fin 1)) :
    x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ↔ |x 0| ≤ 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, norm_fin1]

lemma abs_le_one_of_mem (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    |x.val 0| ≤ 1 := by
  have h : x.val ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 := x.property
  rw [mem_closedBall_fin1] at h
  exact h

/-- Forward coordinate map `𝔻¹ → I`, `x ↦ (x₀+1)/2`. -/
def diskOneToIntervalFun (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    unitInterval :=
  ⟨(x.val 0 + 1) / 2, by
    have h := abs_le_one_of_mem x
    rw [abs_le] at h
    have h0 : (0 : ℝ) ≤ (x.val 0 + 1) / 2 ∧ (x.val 0 + 1) / 2 ≤ 1 := by
      constructor <;> linarith
    exact Set.mem_Icc.mpr h0⟩

/-- Backward coordinate map `I → 𝔻¹`, `t ↦ single 0 (2t-1)`. -/
def intervalToDiskOneFun (t : unitInterval) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
  ⟨EuclideanSpace.single 0 (2 * t.val - 1), by
    rw [Metric.mem_closedBall, dist_zero_right,
      EuclideanSpace.norm_single 0 _, Real.norm_eq_abs]
    have ht : 0 ≤ t.val ∧ t.val ≤ 1 := Set.mem_Icc.mp t.property
    rw [abs_le]
    constructor <;> linarith⟩

/-- Roundtrip on coordinates: forward after backward is the identity. -/
lemma diskOne_roundtrip (t : unitInterval) :
    ((intervalToDiskOneFun t).val 0 + 1) / 2 = t.val := by
  have h : ((intervalToDiskOneFun t).val : EuclideanSpace ℝ (Fin 1)) 0
      = 2 * t.val - 1 := by
    simp [intervalToDiskOneFun]
  rw [h]
  ring

lemma continuous_diskOneToIntervalFun : Continuous diskOneToIntervalFun := by
  unfold diskOneToIntervalFun
  apply Continuous.subtype_mk
  fun_prop

lemma single_zero_cont : Continuous (fun a : ℝ => EuclideanSpace.single (ι := Fin 1) 0 a) := by
  apply Isometry.continuous
  intro x y
  simp

lemma affine_cont : Continuous (fun t : unitInterval => 2 * t.val - 1) := by
  fun_prop

lemma continuous_intervalToDiskOneFun : Continuous intervalToDiskOneFun := by
  unfold intervalToDiskOneFun
  apply Continuous.subtype_mk
  exact single_zero_cont.comp affine_cont

lemma single_coord_id (x : EuclideanSpace ℝ (Fin 1)) :
    EuclideanSpace.single 0 (x 0) = x := by
  ext i
  have hi : i = 0 := Subsingleton.elim i 0
  rw [hi]
  simp

lemma diskOne_left_inv (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    intervalToDiskOneFun (diskOneToIntervalFun x) = x := by
  apply Subtype.ext
  have h1 : (2 * (((x.val 0 + 1) / 2 : ℝ)) - 1) = x.val 0 := by ring
  have h2 : EuclideanSpace.single (ι := Fin 1) 0 (2 * ((x.val 0 + 1) / 2) - 1)
      = x.val := by
    rw [h1]
    exact single_coord_id x.val
  exact h2

lemma diskOne_right_inv (t : unitInterval) :
    diskOneToIntervalFun (intervalToDiskOneFun t) = t := by
  apply Subtype.ext
  exact diskOne_roundtrip t

def diskOneHomeomorph :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ≃ₜ unitInterval where
  toFun := diskOneToIntervalFun
  invFun := intervalToDiskOneFun
  left_inv := diskOne_left_inv
  right_inv := diskOne_right_inv
  continuous_toFun := continuous_diskOneToIntervalFun
  continuous_invFun := continuous_intervalToDiskOneFun

def diskOneULiftHomeomorph :
    ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) ≃ₜ
      ULift (unitInterval) :=
  Homeomorph.ulift.trans (diskOneHomeomorph.trans Homeomorph.ulift.symm)

def diskOneTopIso : TopCat.disk.{u} 1 ≅ TopCat.I.{u} :=
  TopCat.isoOfHomeo diskOneULiftHomeomorph

lemma sphere_fin1_finite :
    Finite (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) := by
  classical
  refine Finite.of_injective (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 =>
    decide (p.val 0 = 1)) ?_
  intro p q hpq
  have hp : p.val 0 = 1 ∨ p.val 0 = -1 := (mem_sphere_fin1 p.val).mp p.property
  have hq : q.val 0 = 1 ∨ q.val 0 = -1 := (mem_sphere_fin1 q.val).mp q.property
  have hcoord : p.val 0 = q.val 0 := by
    by_cases hp1 : p.val 0 = 1
    · by_cases hq1 : q.val 0 = 1
      · rw [hp1, hq1]
      · simp [hp1, hq1] at hpq
    · by_cases hq1 : q.val 0 = 1
      · simp [hp1, hq1] at hpq
      · have hp' : p.val 0 = -1 := hp.resolve_left hp1
        have hq' : q.val 0 = -1 := hq.resolve_left hq1
        rw [hp', hq']
  have hx : p.val = q.val := by
    have hp' : p.val = EuclideanSpace.single 0 (p.val 0) := (single_coord_id p.val).symm
    have hq' : q.val = EuclideanSpace.single 0 (q.val 0) := (single_coord_id q.val).symm
    rw [hp', hq', hcoord]
  exact Subtype.ext hx

instance sphere_fin1_finite_inst :
    Finite (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
  sphere_fin1_finite

/-- A pair of points gives a continuous map out of the 1-sphere, via the
two-point description (`+1 ↦ x₁`, `-1 ↦ x₀`). -/
def spherePairMap (X : TopCat.{u}) (x₀ x₁ : X) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1, X) :=
  ⟨fun p => if p.val 0 = 1 then x₁ else x₀, continuous_of_discreteTopology⟩

lemma spherePairMap_plus_one (X : TopCat.{u}) (x₀ x₁ : X)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) (h : p.val 0 = 1) :
    spherePairMap X x₀ x₁ p = x₁ := by
  simp [spherePairMap, h]

lemma spherePairMap_minus_one (X : TopCat.{u}) (x₀ x₁ : X)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) (h : p.val 0 = -1) :
    spherePairMap X x₀ x₁ p = x₀ := by
  have hne : ¬ p.val 0 = 1 := by linarith
  simp [spherePairMap, hne]

def spherePlusOne : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
  ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_zero_right]
    simp⟩

def sphereMinusOne : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
  ⟨EuclideanSpace.single 0 (-1), by
    rw [Metric.mem_sphere, dist_zero_right]
    simp⟩

lemma backward_zero : (intervalToDiskOneFun ⟨0, by simp⟩).val =
    EuclideanSpace.single 0 (-1 : ℝ) := by
  have h : (2 : ℝ) * 0 - 1 = -1 := by ring
  have h2 : (intervalToDiskOneFun ⟨(0 : ℝ), by simp⟩).val =
      EuclideanSpace.single 0 ((2 : ℝ) * 0 - 1) := rfl
  rw [h2, h]

lemma backward_one : (intervalToDiskOneFun ⟨1, by simp⟩).val =
    EuclideanSpace.single 0 (1 : ℝ) := by
  have h : (2 : ℝ) * 1 - 1 = 1 := by ring
  have h2 : (intervalToDiskOneFun ⟨(1 : ℝ), by simp⟩).val =
      EuclideanSpace.single 0 ((2 : ℝ) * 1 - 1) := rfl
  rw [h2, h]

end HomotopyHypothesis.Completion.Compression
