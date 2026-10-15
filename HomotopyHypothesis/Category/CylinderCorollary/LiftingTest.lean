import HomotopyHypothesis.Blueprint.Defs
noncomputable section

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint

variable {C : GlobularTheory.{u}}

theorem boundary_rlp_iff {X Y : C.Model} (p : X ⟶ Y) :
    (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp p ↔
      ∀ n, HasLiftingProperty (I C n) p := by
  constructor
  · intro h n
    exact h _ (MorphismProperty.ofHoms.mk n)
  · intro h
    rintro A B i ⟨n⟩
    exact h n

theorem source_rlp_iff {X Y : C.Model} (p : X ⟶ Y) :
    (MorphismProperty.ofHoms (fun n : ℕ => J C n)).rlp p ↔
      ∀ n, HasLiftingProperty (J C n) p := by
  constructor
  · intro h n
    exact h _ (MorphismProperty.ofHoms.mk n)
  · intro h
    rintro A B i ⟨n⟩
    exact h n

theorem exactBoundaryTest_of_boundary_rlp (hC : C.IsCoherator) {X Y : C.Model}
    (p : X ⟶ Y) (hp : (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp p) :
    GlobularSet.ExactBoundaryTest (underlyingMap p) := by
  intro n b y hy
  obtain ⟨x, hx, hpx⟩ := (hasLiftingProperty_I_iff n p).1
    ((boundary_rlp_iff p).1 hp n) b y hy
  refine ⟨x, hx, ?_⟩
  rw [hpx]
  exact Y.joined_refl hC n y

theorem weakEquivalence_of_boundary_rlp (hC : C.IsCoherator) {X Y : C.Model}
    (p : X ⟶ Y) (hp : (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp p) :
    W hC p :=
  weakEquivalence_of_exactBoundaryTest hC p (exactBoundaryTest_of_boundary_rlp hC p hp)

theorem source_rlp_of_boundary_rlp {X Y : C.Model} (p : X ⟶ Y)
    (hp : (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp p) :
    (MorphismProperty.ofHoms (fun n : ℕ => J C n)).rlp p := by
  apply (source_rlp_iff p).2
  intro n
  exact hasLiftingProperty_J_of_I n p
    ((boundary_rlp_iff p).1 hp n) ((boundary_rlp_iff p).1 hp (n + 1))

theorem boundary_rlp_of_exactBoundaryTest {X Y : C.Model} (p : X ⟶ Y)
    (hptest : GlobularSet.ExactBoundaryTest (underlyingMap p))
    (hp : (MorphismProperty.ofHoms (fun n : ℕ => J C n)).rlp p) :
    (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp p := by
  apply (boundary_rlp_iff p).2
  intro n
  apply (hasLiftingProperty_I_iff n p).2
  intro b y hy
  obtain ⟨x, hx, c, hc₀, hc₁⟩ := hptest n b y hy
  obtain ⟨d, hd₀, hpd⟩ := (hasLiftingProperty_J_iff n p).1
    ((source_rlp_iff p).1 hp n) x c hc₀
  refine ⟨X.underlying.target n d, ?_, ?_⟩
  · have h := (GlobularSet.parallel_iff_boundary_eq X.underlying n
      (X.underlying.source n d) (X.underlying.target n d)).1
        (GlobularSet.Joined.parallel ⟨d, rfl, rfl⟩)
    rw [hd₀, hx] at h
    exact h.symm
  · rw [(underlyingMap p).target_app, hpd, hc₁]

theorem lifting_test_forward (hC : C.IsCoherator) :
    (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp ≤
      W hC ⊓ (MorphismProperty.ofHoms (fun n : ℕ => J C n)).rlp := by
  intro X Y p hp
  exact ⟨weakEquivalence_of_boundary_rlp hC p hp, source_rlp_of_boundary_rlp p hp⟩

theorem lifting_test_of_weakEquivalence_test (hC : C.IsCoherator)
    (htest : ∀ {X Y : C.Model} (p : X ⟶ Y),
      WeakEquivalence hC p → GlobularSet.ExactBoundaryTest (underlyingMap p)) :
    (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp =
      W hC ⊓ (MorphismProperty.ofHoms (fun n : ℕ => J C n)).rlp := by
  apply le_antisymm (lifting_test_forward hC)
  intro X Y p hp
  exact boundary_rlp_of_exactBoundaryTest p (htest p hp.1) hp.2

#print axioms lifting_test_forward
#print axioms lifting_test_of_weakEquivalence_test

end HomotopyHypothesis.Category.CylinderCorollary
