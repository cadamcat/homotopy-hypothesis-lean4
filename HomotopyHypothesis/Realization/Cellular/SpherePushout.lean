import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge
import HomotopyHypothesis.Realization.Cellular.CompactPushout
import HomotopyHypothesis.Realization.Cellular.DiskCoordinates
noncomputable section

open CategoryTheory Limits Topology

namespace HomotopyHypothesis.Realization.Cellular

universe u

/-- A Euclidean vector is determined by its first coordinates and its last coordinate. -/
theorem euclidean_ext_dropLast_last {n : ℕ} {x y : EuclideanSpace ℝ (Fin (n + 1))}
    (h : dropLast x = dropLast y) (hl : x (Fin.last n) = y (Fin.last n)) : x = y := by
  ext i
  refine Fin.lastCases hl (fun j => ?_) i
  exact congrArg (fun z : EuclideanSpace ℝ (Fin n) => z j) h

/-- The two hemisphere parametrizations of the boundary sphere. -/
def sphereFace (n : ℕ) (b : Bool) : TopCat.disk.{u} n ⟶ TopCat.diskBoundary.{u} (n + 1) :=
  TopCat.ofHom
    { toFun := fun x => ULift.up ⟨faceVec n (n + 1) b x.down.1, by
        rw [mem_sphere_zero_iff_norm]
        have := norm_sq_faceVec (Nat.lt_succ_self n) b x.down.1
          (mem_closedBall_zero_iff.mp x.down.2)
        nlinarith [norm_nonneg (faceVec n (n + 1) b x.down.1)]⟩
      continuous_toFun := continuous_uliftUp.comp
        (((continuous_faceVec n (n + 1) b).comp
          (continuous_subtype_val.comp continuous_uliftDown)).subtype_mk _) }

@[simp] theorem sphereFace_inclusion (n : ℕ) (b : Bool) :
    sphereFace.{u} n b ≫ TopCat.diskBoundaryInclusion (n + 1) =
      Blueprint.oaiTopGlobes.map (OAI.Grothendieck.Globe.face (Nat.lt_succ_self n) b) := by
  apply TopCat.ext
  intro x
  rfl

theorem sphereFace_injective (n : ℕ) (b : Bool) : Function.Injective (sphereFace.{u} n b) := by
  intro x y h
  apply ULift.ext
  apply Subtype.ext
  have hh := congrArg (fun z : TopCat.diskBoundary.{u} (n + 1) => dropLast z.down.1) h
  change dropLast (faceVec n (n + 1) b x.down.1) =
    dropLast (faceVec n (n + 1) b y.down.1) at hh
  simpa only [dropLast_faceVec] using hh

theorem sphereFace_condition (n : ℕ) :
    TopCat.diskBoundaryInclusion n ≫ sphereFace.{u} n false =
      TopCat.diskBoundaryInclusion n ≫ sphereFace.{u} n true := by
  apply TopCat.ext
  intro x
  apply ULift.ext
  apply Subtype.ext
  change faceVec n (n + 1) false x.down.1 = faceVec n (n + 1) true x.down.1
  apply euclidean_ext_dropLast_last
  · simp only [dropLast_faceVec]
  · have hx : ‖x.down.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.down.2
    simp [hx]

theorem sphereFace_cover (n : ℕ) (p : TopCat.diskBoundary.{u} (n + 1)) :
    (∃ b, sphereFace n false b = p) ∨ (∃ b, sphereFace n true b = p) := by
  let x : Ball (n + 1) := ⟨p.down.1, Metric.sphere_subset_closedBall p.down.2⟩
  let b : TopCat.disk.{u} n := ULift.up (diskProject x)
  have hx : ‖p.down.1‖ = 1 := mem_sphere_zero_iff_norm.mp p.down.2
  have heq : (p.down.1 (Fin.last n)) ^ 2 = capHeight x ^ 2 := by
    have := norm_sq_dropLast p.down.1
    have := capHeight_sq x
    dsimp [x] at *
    nlinarith
  have hb (side : Bool)
      (hh : (if side then -1 else 1) * capHeight x = p.down.1 (Fin.last n)) :
      sphereFace n side b = p := by
    apply ULift.ext
    apply Subtype.ext
    apply euclidean_ext_dropLast_last
    · change dropLast (faceVec n (n + 1) side (dropLast p.down.1)) = _
      exact dropLast_faceVec n side _
    · change faceVec n (n + 1) side (dropLast p.down.1) (Fin.last n) = _
      rw [last_faceVec]
      exact hh
  by_cases hp : 0 ≤ p.down.1 (Fin.last n)
  · left
    refine ⟨b, hb false ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    nlinarith [capHeight_nonneg x]
  · right
    refine ⟨b, hb true ?_⟩
    simp only [↓reduceIte, neg_one_mul]
    nlinarith [capHeight_nonneg x]

theorem sphereFace_cross (n : ℕ) (b c : TopCat.disk.{u} n)
    (h : sphereFace n false b = sphereFace n true c) :
    ∃ a : TopCat.diskBoundary.{u} n,
      TopCat.diskBoundaryInclusion n a = b ∧ TopCat.diskBoundaryInclusion n a = c := by
  have heq : b = c := by
    apply ULift.ext
    apply Subtype.ext
    have hh := congrArg (fun z : TopCat.diskBoundary.{u} (n + 1) => dropLast z.down.1) h
    change dropLast (faceVec n (n + 1) false b.down.1) =
      dropLast (faceVec n (n + 1) true c.down.1) at hh
    simpa only [dropLast_faceVec] using hh
  subst c
  have hs := congrArg (fun z : TopCat.diskBoundary.{u} (n + 1) => z.down.1 (Fin.last n)) h
  change faceVec n (n + 1) false b.down.1 (Fin.last n) =
    faceVec n (n + 1) true b.down.1 (Fin.last n) at hs
  simp only [last_faceVec, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] at hs
  have hz : Real.sqrt (1 - ‖b.down.1‖ ^ 2) = 0 := by linarith
  have hb := mem_closedBall_zero_iff.mp b.down.2
  have hsq : (Real.sqrt (1 - ‖b.down.1‖ ^ 2)) ^ 2 = 1 - ‖b.down.1‖ ^ 2 :=
    Real.sq_sqrt (by nlinarith [norm_nonneg b.down.1])
  have hn : ‖b.down.1‖ = 1 := by rw [hz] at hsq; nlinarith [norm_nonneg b.down.1]
  exact ⟨ULift.up ⟨b.down.1, mem_sphere_zero_iff_norm.mpr hn⟩, rfl, rfl⟩

/-- A sphere is the union of two closed disks along their common boundary. -/
theorem sphere_isPushout (n : ℕ) :
    IsPushout (TopCat.diskBoundaryInclusion n) (TopCat.diskBoundaryInclusion n)
      (sphereFace.{u} n false) (sphereFace.{u} n true) := by
  letI : T2Space (TopCat.diskBoundary.{u} (n + 1)) :=
    inferInstanceAs (T2Space (ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))
  exact compactCover_isPushout _ _ _ _ ⟨sphereFace_condition n⟩
    (sphereFace_injective n false) (sphereFace_injective n true)
    (sphereFace_cover n) (sphereFace_cross n)

end HomotopyHypothesis.Realization.Cellular
