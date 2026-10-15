import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge
import HomotopyHypothesis.Comparison.FundamentalGroupoid.Cells
/-!
# Comparing weak equivalences

A map of spaces is a weak homotopy equivalence exactly when the induced map of fundamental
∞-groupoids is a weak equivalence. The two sides are bijections on path components and on
homotopy groups; the cell identifications of `Cells` intertwine them.
-/

noncomputable section

namespace HomotopyHypothesis.Comparison.FundamentalGroupoid

open CategoryTheory
open OAI.Grothendieck
open OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint
open HomotopyHypothesis.Comparison.FundamentalGroupoid.Cells
open HomotopyHypothesis

universe u

/-- Bijectivity passes across a commuting square of equivalences. -/
lemma bijective_of_commute {α β γ δ : Type*} {eX : α ≃ γ} {eY : β ≃ δ} {f : α → β} {g : γ → δ}
    (h : eY ∘ f = g ∘ eX) : Function.Bijective f ↔ Function.Bijective g := by
  constructor
  · intro hf
    have hg : g = eY ∘ f ∘ eX.symm := by
      ext x
      simpa using (congrFun h (eX.symm x)).symm
    rw [hg]
    exact eY.bijective.comp (hf.comp eX.symm.bijective)
  · intro hg
    have hf : f = eY.symm ∘ g ∘ eX := by
      ext x
      apply eY.injective
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
      exact congrFun h x
    rw [hf]
    exact eY.symm.bijective.comp (hg.comp eX.bijective)

/-- Replacing the base point by an equal point preserves bijectivity on homotopy groups. -/
lemma homotopyGroupMap_bijective_congr {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ} {a b : X}
    (h : a = b) :
    Function.Bijective (homotopyGroupMap (Fin (n + 1)) f a) ↔
      Function.Bijective (homotopyGroupMap (Fin (n + 1)) f b) := by
  cases h
  rfl

/-- Path components and homotopy groups of `Π_R X` agree with those of `X`. -/
theorem pi_comparison_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator) (R : OAIRealization C)
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    W hC (R.Pi.map f) ↔ weakHomotopyEquivalences f := by
  unfold W weakHomotopyEquivalences WeakEquivalence
  constructor
  · intro h
    refine ⟨(bijective_of_commute (componentsMap_comm R f)).mp h.1, ?_⟩
    intro n p
    have hb := (bijective_of_commute
      (homotopyMap_comm R f hC (cellOfPoint R p) n)).mp (h.2 (cellOfPoint R p) n)
    exact (homotopyGroupMap_bijective_congr f (pointOfCell_cellOfPoint R p)).mp hb
  · intro h
    refine ⟨(bijective_of_commute (componentsMap_comm R f)).mpr h.1, ?_⟩
    intro x n
    exact (bijective_of_commute (homotopyMap_comm R f hC x n)).mpr (h.2 n (pointOfCell R x))

#print axioms pi_comparison_proof

end HomotopyHypothesis.Comparison.FundamentalGroupoid
