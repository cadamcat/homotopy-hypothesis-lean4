import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Cylinder.FiniteCellCategory.FiniteCells
import HomotopyHypothesis.Cylinder.FiniteCellCategory.WeakEquivalences
noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Cylinder.FiniteCellCategory

universe u

variable {C : GlobularTheory.{u}}

@[reassoc (attr := simp)]
 theorem boundary_inl_I (n : ℕ) :
    pushout.inl (I C n) (I C n) ≫ I C (n+1) = J C n := by
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
 theorem boundary_inr_I (n : ℕ) :
    pushout.inr (I C n) (I C n) ≫ I C (n+1) = targetDisk C n := by
  exact pushout.inr_desc _ _ _

 theorem finiteCellMaps_I (n : ℕ) : finiteCellMaps C (I C n) :=
  .of _ (Or.inl ((boundaryMaps C).le_pushouts _ (MorphismProperty.ofHoms.mk n)))

 theorem finiteCellMaps_J (n : ℕ) : finiteCellMaps C (J C n) := by
  rw [← boundary_inl_I n]
  exact (finiteCellMaps C).comp_mem _ _
    ((finiteCellMaps C).pushout_inl _ _ (finiteCellMaps_I n)) (finiteCellMaps_I (n+1))

 theorem boundary_test_lift (hC : C.IsCoherator) {Z X : C.Model} (p : Z ⟶ X)
    (hp : W hC p) (hZ : ModelCofibrant Z) (n : ℕ)
    (a : boundaryDisk C n ⟶ Z) (x : disk C n ⟶ X)
    (hx : a ≫ p = I C n ≫ x) :
    ∃ (b : disk C n ⟶ Z) (H : disk C (n+1) ⟶ X),
      I C n ≫ b = a ∧ J C n ≫ H = b ≫ p ∧ targetDisk C n ≫ H = x := by
  let R := boundaryRepresentation C n
  have hb : X.underlying.boundary n (cellEquiv X n x) =
      (underlyingMap p).boundaryMap n (R.equiv Z a) := by
    rw [← R.inclusion_boundary, ← R.naturality, hx]
  obtain ⟨z, hz, H, hs, ht⟩ := weakEquivalence_exactBoundaryTest hC p hp hZ n
    (R.equiv Z a) (cellEquiv X n x) hb
  let b := (cellEquiv Z n).symm z
  let h := (cellEquiv X (n+1)).symm H
  refine ⟨b, h, ?_, ?_, ?_⟩
  · apply (R.equiv Z).injective
    rw [R.inclusion_boundary, Equiv.apply_symm_apply]
    exact hz
  · apply (cellEquiv X n).injective
    rw [cellEquiv_J, cellEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hs
  · apply (cellEquiv X n).injective
    rw [cellEquiv_targetDisk, Equiv.apply_symm_apply]
    exact ht

end HomotopyHypothesis.Cylinder.FiniteCellCategory
