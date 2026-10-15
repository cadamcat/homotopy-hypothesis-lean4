import HomotopyHypothesis.Completion.Compression.DiskOne
import HomotopyHypothesis.Completion.Compression.DiskZero
/-
# Path components via the 1-disk

Maps out of the 1-sphere from pairs of points, maps out of the 1-disk from
paths, commutativity of the resulting square, explicit boundary/disk points
with their identifications, and extraction of paths from disk maps. Toward
injectivity on path components from the `n = 1` lifting property.
-/
noncomputable section

namespace HomotopyHypothesis.Completion.Compression

universe u

open CategoryTheory TopCat Topology

/-- Continuous map `ULift α → α`. -/
def uliftContinuousMap (α : Type*) [TopologicalSpace α] :
    C(ULift α, α) :=
  ⟨⇑Homeomorph.ulift, Homeomorph.ulift.continuous_toFun⟩

/-- Continuous map `α → ULift α`. -/
def uliftUpContinuousMap (α : Type*) [TopologicalSpace α] :
    C(α, ULift α) :=
  ⟨⇑Homeomorph.ulift.symm, Homeomorph.ulift.symm.continuous_toFun⟩

/-- The boundary map `∂𝔻¹ → X` from a pair `x₀, x₁` (`-1 ↦ x₀`, `+1 ↦ x₁`). -/
def boundaryOneMap (X : TopCat.{u}) (x₀ x₁ : X) :
    TopCat.diskBoundary.{u} 1 ⟶ X :=
  TopCat.ofHom ((spherePairMap X x₀ x₁).comp (uliftContinuousMap _))

lemma boundaryOneMap_apply (X : TopCat.{u}) (x₀ x₁ : X)
    (p : TopCat.diskBoundary.{u} 1) :
    (boundaryOneMap X x₀ x₁) p =
      if ((p.down.val : EuclideanSpace ℝ (Fin 1)) 0 = 1) then x₁ else x₀ := by
  rfl

/-- Forward interval map as a continuous map. -/
def forwardContinuousMap :
    C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, unitInterval) :=
  ⟨diskOneToIntervalFun, continuous_diskOneToIntervalFun⟩

/-- Backward interval map as a continuous map. -/
def backwardContinuousMap :
    C(unitInterval, Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
  ⟨intervalToDiskOneFun, continuous_intervalToDiskOneFun⟩

/-- The disk map `𝔻¹ → Y` from a path, via the forward interval map. -/
def diskOneMapOfPath {Y : TopCat.{u}} {y₀ y₁ : Y} (γ : Path y₀ y₁) :
    TopCat.disk.{u} 1 ⟶ Y :=
  TopCat.ofHom (γ.toContinuousMap.comp
    (forwardContinuousMap.comp (uliftContinuousMap _)))

lemma inclusion_preserves_vector (p : TopCat.diskBoundary.{u} 1) :
    ((TopCat.diskBoundaryInclusion 1 p).down.val : EuclideanSpace ℝ (Fin 1)) =
      (p.down.val : EuclideanSpace ℝ (Fin 1)) := by
  rfl

/-- The square for `π₀` injectivity commutes: the boundary pair against the
path disk map. -/
lemma comm_one {X Y : TopCat.{u}} (f : X ⟶ Y) {x₀ x₁ : X}
    {y₀ y₁ : Y} (hf0 : f x₀ = y₀) (hf1 : f x₁ = y₁) (γ : Path y₀ y₁) :
    boundaryOneMap X x₀ x₁ ≫ f =
      TopCat.diskBoundaryInclusion 1 ≫ diskOneMapOfPath γ := by
  ext p
  have hcoord : (p.down.val : EuclideanSpace ℝ (Fin 1)) 0 = 1 ∨
      (p.down.val : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
    have hmem : (p.down.val : EuclideanSpace ℝ (Fin 1)) ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := p.down.property
    exact (mem_sphere_fin1 _).mp hmem
  rcases hcoord with h | h
  · have ha : (boundaryOneMap X x₀ x₁) p = x₁ := by
      simp [boundaryOneMap_apply, h]
    have hLHS : (boundaryOneMap X x₀ x₁ ≫ f) p = y₁ := by
      rw [TopCat.comp_app, ha, hf1]
    have hcoord1 : (((TopCat.diskBoundaryInclusion 1 p).down.val :
        EuclideanSpace ℝ (Fin 1)) 0) = 1 := by
      rw [inclusion_preserves_vector, h]
    have hfw : forwardContinuousMap
        ((TopCat.diskBoundaryInclusion 1 p).down :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) =
        ⟨1, by simp⟩ := by
      apply Subtype.ext
      show ((diskOneToIntervalFun _).val : ℝ) = 1
      simp [diskOneToIntervalFun, hcoord1]
    have hRHS : (TopCat.diskBoundaryInclusion 1 ≫ diskOneMapOfPath γ) p = y₁ := by
      rw [TopCat.comp_app]
      have hb : (diskOneMapOfPath γ)
          (TopCat.diskBoundaryInclusion 1 p) = γ ⟨1, by simp⟩ := by
        have h1 : (diskOneMapOfPath γ)
            (TopCat.diskBoundaryInclusion 1 p) =
            γ.toContinuousMap (forwardContinuousMap
              ((TopCat.diskBoundaryInclusion 1 p).down)) := rfl
        rw [h1, hfw]
        rfl
      rw [hb]
      exact γ.target'
    rw [hLHS, hRHS]
  · have hne : ¬ ((p.down.val : EuclideanSpace ℝ (Fin 1)) 0 = 1) := by
      linarith
    have ha : (boundaryOneMap X x₀ x₁) p = x₀ := by
      simp [boundaryOneMap_apply, hne]
    have hLHS : (boundaryOneMap X x₀ x₁ ≫ f) p = y₀ := by
      rw [TopCat.comp_app, ha, hf0]
    have hcoord0 : (((TopCat.diskBoundaryInclusion 1 p).down.val :
        EuclideanSpace ℝ (Fin 1)) 0) = -1 := by
      rw [inclusion_preserves_vector, h]
    have hfw : forwardContinuousMap
        ((TopCat.diskBoundaryInclusion 1 p).down :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) =
        ⟨0, by simp⟩ := by
      apply Subtype.ext
      show ((diskOneToIntervalFun _).val : ℝ) = 0
      simp [diskOneToIntervalFun, hcoord0]
    have hRHS : (TopCat.diskBoundaryInclusion 1 ≫ diskOneMapOfPath γ) p = y₀ := by
      rw [TopCat.comp_app]
      have hb : (diskOneMapOfPath γ)
          (TopCat.diskBoundaryInclusion 1 p) = γ ⟨0, by simp⟩ := by
        have h1 : (diskOneMapOfPath γ)
            (TopCat.diskBoundaryInclusion 1 p) =
            γ.toContinuousMap (forwardContinuousMap
              ((TopCat.diskBoundaryInclusion 1 p).down)) := rfl
        rw [h1, hfw]
        rfl
      rw [hb]
      exact γ.source'
    rw [hLHS, hRHS]

def boundaryMinusOnePt : TopCat.diskBoundary.{u} 1 :=
  ULift.up sphereMinusOne

def boundaryPlusOnePt : TopCat.diskBoundary.{u} 1 :=
  ULift.up spherePlusOne

def diskMinusOnePt : TopCat.disk.{u} 1 :=
  ULift.up (intervalToDiskOneFun ⟨0, by simp⟩)

def diskPlusOnePt : TopCat.disk.{u} 1 :=
  ULift.up (intervalToDiskOneFun ⟨1, by simp⟩)

lemma boundaryMinusOne_vec :
    (boundaryMinusOnePt.{u}.down.val : EuclideanSpace ℝ (Fin 1)) =
      EuclideanSpace.single 0 (-1 : ℝ) := by
  rfl

lemma boundaryPlusOne_vec :
    (boundaryPlusOnePt.{u}.down.val : EuclideanSpace ℝ (Fin 1)) =
      EuclideanSpace.single 0 (1 : ℝ) := by
  rfl

lemma diskMinusOne_vec :
    (diskMinusOnePt.{u}.down.val : EuclideanSpace ℝ (Fin 1)) =
      EuclideanSpace.single 0 (-1 : ℝ) := by
  have h : ((intervalToDiskOneFun ⟨(0 : ℝ), by simp⟩).val :
      EuclideanSpace ℝ (Fin 1)) = EuclideanSpace.single 0 (-1 : ℝ) := by
    rw [backward_zero]
  exact h

lemma diskPlusOne_vec :
    (diskPlusOnePt.{u}.down.val : EuclideanSpace ℝ (Fin 1)) =
      EuclideanSpace.single 0 (1 : ℝ) := by
  have h : ((intervalToDiskOneFun ⟨(1 : ℝ), by simp⟩).val :
      EuclideanSpace ℝ (Fin 1)) = EuclideanSpace.single 0 (1 : ℝ) := by
    rw [backward_one]
  exact h

lemma incl_minus :
    TopCat.diskBoundaryInclusion.{u} 1 boundaryMinusOnePt = diskMinusOnePt := by
  apply ULift.ext
  apply Subtype.ext
  show ((TopCat.diskBoundaryInclusion.{u} 1 boundaryMinusOnePt).down.val :
    EuclideanSpace ℝ (Fin 1)) = (diskMinusOnePt.{u}.down.val : EuclideanSpace ℝ (Fin 1))
  rw [inclusion_preserves_vector, boundaryMinusOne_vec, diskMinusOne_vec]

lemma incl_plus :
    TopCat.diskBoundaryInclusion.{u} 1 boundaryPlusOnePt = diskPlusOnePt := by
  apply ULift.ext
  apply Subtype.ext
  show ((TopCat.diskBoundaryInclusion.{u} 1 boundaryPlusOnePt).down.val :
    EuclideanSpace ℝ (Fin 1)) = (diskPlusOnePt.{u}.down.val : EuclideanSpace ℝ (Fin 1))
  rw [inclusion_preserves_vector, boundaryPlusOne_vec, diskPlusOne_vec]

lemma boundaryMinusOne_coord :
    ((boundaryMinusOnePt.{u}.down.val : EuclideanSpace ℝ (Fin 1)) 0) = -1 := by
  rw [boundaryMinusOne_vec]
  simp

lemma boundaryPlusOne_coord :
    ((boundaryPlusOnePt.{u}.down.val : EuclideanSpace ℝ (Fin 1)) 0) = 1 := by
  rw [boundaryPlusOne_vec]
  simp

lemma boundaryMinusOne_val (X : TopCat.{u}) (x₀ x₁ : X) :
    boundaryOneMap X x₀ x₁ boundaryMinusOnePt.{u} = x₀ := by
  have hcoord : ((boundaryMinusOnePt.{u}.down.val : EuclideanSpace ℝ (Fin 1)) 0) = -1 :=
    boundaryMinusOne_coord.{u}
  have hne : ¬ (((boundaryMinusOnePt.{u}.down.val : EuclideanSpace ℝ (Fin 1)) 0) = 1) := by
    rw [hcoord]
    norm_num
  simp [boundaryOneMap_apply, hne]

lemma boundaryPlusOne_val (X : TopCat.{u}) (x₀ x₁ : X) :
    boundaryOneMap X x₀ x₁ boundaryPlusOnePt.{u} = x₁ := by
  have hcoord : ((boundaryPlusOnePt.{u}.down.val : EuclideanSpace ℝ (Fin 1)) 0) = 1 :=
    boundaryPlusOne_coord.{u}
  simp [boundaryOneMap_apply, hcoord]

lemma unitInterval_zero_eq : (⟨(0 : ℝ), by simp⟩ : unitInterval) = 0 := by
  apply Subtype.ext
  rfl

lemma unitInterval_one_eq : (⟨(1 : ℝ), by simp⟩ : unitInterval) = 1 := by
  apply Subtype.ext
  rfl

lemma hpt0 :
    ((uliftUpContinuousMap
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).comp
      backwardContinuousMap) (0 : unitInterval) = diskMinusOnePt.{u} := by
  have hU : (0 : unitInterval) = (⟨(0 : ℝ), by simp⟩ : unitInterval) :=
    unitInterval_zero_eq.symm
  rw [hU]
  rfl

lemma hpt1 :
    ((uliftUpContinuousMap
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).comp
      backwardContinuousMap) (1 : unitInterval) = diskPlusOnePt.{u} := by
  have hU : (1 : unitInterval) = (⟨(1 : ℝ), by simp⟩ : unitInterval) :=
    unitInterval_one_eq.symm
  rw [hU]
  rfl

/-- Injectivity on path components from the `n = 1` lifting property. -/
lemma henry_one_injective {X Y : TopCat.{u}} (f : X ⟶ Y)
    (H : ∀ (a : TopCat.diskBoundary.{u} 1 ⟶ X) (b : TopCat.disk.{u} 1 ⟶ Y),
      a ≫ f = TopCat.diskBoundaryInclusion.{u} 1 ≫ b →
      ∃ l : TopCat.disk.{u} 1 ⟶ X, TopCat.diskBoundaryInclusion.{u} 1 ≫ l = a ∧
        (l ≫ f).hom.HomotopicRel b.hom
          (Set.range (TopCat.diskBoundaryInclusion.{u} 1)))
    {x₀ x₁ : X} (h : Joined (f x₀) (f x₁)) : Joined x₀ x₁ := by
  obtain ⟨γ⟩ := h
  let a := boundaryOneMap X x₀ x₁
  let b := diskOneMapOfPath γ
  have hcomm : a ≫ f = TopCat.diskBoundaryInclusion.{u} 1 ≫ b :=
    comm_one f rfl rfl γ
  obtain ⟨l, hl, _⟩ := H a b hcomm
  have hl_minus : l diskMinusOnePt.{u} = x₀ := by
    have h1 : (TopCat.diskBoundaryInclusion.{u} 1 ≫ l) boundaryMinusOnePt.{u} =
        a boundaryMinusOnePt.{u} := by rw [hl]
    rw [TopCat.comp_app, incl_minus] at h1
    rw [h1]
    exact boundaryMinusOne_val X x₀ x₁
  have hl_plus : l diskPlusOnePt.{u} = x₁ := by
    have h1 : (TopCat.diskBoundaryInclusion.{u} 1 ≫ l) boundaryPlusOnePt.{u} =
        a boundaryPlusOnePt.{u} := by rw [hl]
    rw [TopCat.comp_app, incl_plus] at h1
    rw [h1]
    exact boundaryPlusOne_val X x₀ x₁
  let δmap : C(unitInterval, X) :=
    l.hom.comp ((uliftUpContinuousMap
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).comp
      backwardContinuousMap)
  have h0 : δmap 0 = x₀ := by
    have hδ : δmap (0 : unitInterval) = l.hom diskMinusOnePt.{u} := by
      show l.hom (((uliftUpContinuousMap _).comp backwardContinuousMap) 0) = _
      rw [hpt0]
    rw [hδ]
    exact hl_minus
  have h1 : δmap 1 = x₁ := by
    have hδ : δmap (1 : unitInterval) = l.hom diskPlusOnePt.{u} := by
      show l.hom (((uliftUpContinuousMap _).comp backwardContinuousMap) 1) = _
      rw [hpt1]
    rw [hδ]
    exact hl_plus
  exact ⟨⟨δmap, h0, h1⟩⟩

end HomotopyHypothesis.Completion.Compression
