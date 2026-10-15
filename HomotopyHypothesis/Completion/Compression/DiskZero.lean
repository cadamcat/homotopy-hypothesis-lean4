import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge
/-
# Zero-dimensional case of the compression criterion

The 0-disk is a point and the 0-sphere is empty. Hence the lifting property
at `n = 0` is surjectivity on path components. This file establishes the
point/empty identifications and derives surjectivity on `π₀` from the
lifting property.
-/
noncomputable section

namespace HomotopyHypothesis.Completion.Compression

universe u

open CategoryTheory TopCat

instance diskBoundary_zero_empty_inst : IsEmpty (TopCat.diskBoundary.{u} 0) := by
  unfold TopCat.diskBoundary
  constructor
  intro x
  let y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 0)) 1 := x.down
  have hy : dist (y.val : EuclideanSpace ℝ (Fin 0)) 0 = 1 := y.property
  have hnorm : ‖(y.val : EuclideanSpace ℝ (Fin 0))‖ = 0 := by
    have h : y.val = 0 := Subsingleton.elim _ _
    rw [h, norm_zero]
  rw [dist_zero_right] at hy
  rw [hnorm] at hy
  exact zero_ne_one hy

instance disk_zero_nonempty_inst : Nonempty (TopCat.disk.{u} 0) := by
  unfold TopCat.disk
  constructor
  exact ⟨⟨(0 : EuclideanSpace ℝ (Fin 0)), by simp⟩⟩

instance disk_zero_subsingleton_inst : Subsingleton (TopCat.disk.{u} 0) := by
  unfold TopCat.disk
  constructor
  intro a b
  have hval : a.down.val = b.down.val := Subsingleton.elim _ _
  have hdown : a.down = b.down := Subtype.ext hval
  exact ULift.ext _ _ hdown

/-- The unique point of the 0-disk. -/
def diskZeroPt : TopCat.disk.{u} 0 :=
  Classical.choice disk_zero_nonempty_inst

lemma boundary_zero_subsingleton (X : TopCat.{u})
    (a a' : TopCat.diskBoundary.{u} 0 ⟶ X) : a = a' := by
  ext x
  exact False.elim (IsEmpty.false x)

/-- The map from the 0-disk picking a point. -/
def diskZeroMap (Y : TopCat.{u}) (y : Y) : TopCat.disk.{u} 0 ⟶ Y :=
  TopCat.ofHom ⟨fun _ => y, continuous_const⟩

lemma homotopic_diskZero_joined {Y : TopCat.{u}} {g₀ g₁ : C(TopCat.disk.{u} 0, Y)}
    (h : g₀.Homotopic g₁) (p : TopCat.disk.{u} 0) : Joined (g₀ p) (g₁ p) := by
  obtain ⟨H⟩ := h
  refine ⟨⟨⟨fun t => H (t, p), H.continuous.comp (by fun_prop)⟩, ?_, ?_⟩⟩
  · simp
  · simp

/-- The unique map from the empty 0-sphere. -/
def boundaryZeroMap (X : TopCat.{u}) : TopCat.diskBoundary.{u} 0 ⟶ X :=
  TopCat.ofHom ⟨fun x => False.elim (IsEmpty.false x), by continuity⟩

lemma range_inclusion_zero_empty :
    Set.range (TopCat.diskBoundaryInclusion.{u} 0).hom = ∅ := by
  ext y
  simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
  rintro ⟨x, _⟩
  exact IsEmpty.false x

/-- The lifting property at `n = 0` gives a preimage up to a path. -/
lemma henry_zero_surjective {X Y : TopCat.{u}} (f : X ⟶ Y)
    (H : ∀ (a : TopCat.diskBoundary.{u} 0 ⟶ X) (b : TopCat.disk.{u} 0 ⟶ Y),
      a ≫ f = TopCat.diskBoundaryInclusion 0 ≫ b →
      ∃ l : TopCat.disk.{u} 0 ⟶ X, TopCat.diskBoundaryInclusion 0 ≫ l = a ∧
        (l ≫ f).hom.HomotopicRel b.hom
          (Set.range (TopCat.diskBoundaryInclusion.{u} 0)))
    (y : Y) : ∃ x : X, Joined (f x) y := by
  let a := boundaryZeroMap X
  let b := diskZeroMap Y y
  have hcomm : a ≫ f = TopCat.diskBoundaryInclusion 0 ≫ b :=
    boundary_zero_subsingleton _ _ _
  obtain ⟨l, _, hlift⟩ := H a b hcomm
  refine ⟨l diskZeroPt, ?_⟩
  have hrange : Set.range (TopCat.diskBoundaryInclusion.{u} 0).hom = ∅ :=
    range_inclusion_zero_empty
  rw [hrange] at hlift
  have hhom : (l ≫ f).hom.Homotopic b.hom :=
    ContinuousMap.homotopicRel_empty.mp hlift
  have hjoin := homotopic_diskZero_joined hhom diskZeroPt
  have hb : (b.hom : C(TopCat.disk.{u} 0, Y)) diskZeroPt = y := rfl
  have hlf : ((l ≫ f).hom : C(TopCat.disk.{u} 0, Y)) diskZeroPt = f (l diskZeroPt) := rfl
  rw [hlf, hb] at hjoin
  exact hjoin

/-- A pointwise-up-to-path surjectivity gives surjectivity on path components. -/
lemma zeroth_surjective_of_joined {X Y : TopCat.{u}} (f : X ⟶ Y)
    (h : ∀ y : Y, ∃ x : X, Joined (f x) y) :
    Function.Surjective (HomotopyHypothesis.zerothHomotopyMap f) := by
  intro q
  obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective (X := Y) q
  obtain ⟨x, hj⟩ := h y
  exact ⟨ZerothHomotopy.mk x, Quotient.sound hj⟩

/-- Join-reflecting on points gives injectivity on path components. -/
lemma zeroth_injective_of_joined {X Y : TopCat.{u}} (f : X ⟶ Y)
    (h : ∀ {x₀ x₁ : X}, Joined (f x₀) (f x₁) → Joined x₀ x₁) :
    Function.Injective (HomotopyHypothesis.zerothHomotopyMap f) := by
  intro p q hpq
  obtain ⟨x₀, rfl⟩ := ZerothHomotopy.mk_surjective (X := X) p
  obtain ⟨x₁, rfl⟩ := ZerothHomotopy.mk_surjective (X := X) q
  have hmap : ZerothHomotopy.mk (f x₀) = ZerothHomotopy.mk (f x₁) := hpq
  have hjoin : Joined (f x₀) (f x₁) := Quotient.exact hmap
  have hjoin' : Joined x₀ x₁ := h hjoin
  exact Quotient.sound hjoin'

end HomotopyHypothesis.Completion.Compression
