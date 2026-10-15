import HomotopyHypothesis.Blueprint.Defs
noncomputable section

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

variable {C : GlobularTheory.{u}}

theorem underlyingMap_id (X : C.Model) :
    underlyingMap (𝟙 X) = GlobularSet.Hom.id X.underlying := by
  ext
  rfl

theorem underlyingMap_comp {X Y Z : C.Model} (f : X ⟶ Y) (g : Y ⟶ Z) :
    underlyingMap (f ≫ g) = (underlyingMap f).comp (underlyingMap g) := by
  ext
  rfl

theorem boundaryMap_id (X : GlobularSet.{u}) (n : ℕ) (b : X.Boundary n) :
    (GlobularSet.Hom.id X).boundaryMap n b = b := by
  cases n <;> rfl

theorem componentsMap_id (X : C.Model) : componentsMap (𝟙 X) = id := by
  funext a
  induction a using Quot.inductionOn with
  | h a => rfl

theorem componentsMap_comp {X Y Z : C.Model} (f : X ⟶ Y) (g : Y ⟶ Z) :
    componentsMap (f ≫ g) = componentsMap g ∘ componentsMap f := by
  funext a
  induction a using Quot.inductionOn with
  | h a => rfl

theorem homotopyMap_id (hC : C.IsCoherator) (X : C.Model)
    (x : X.underlying.Cell 0) (n : ℕ) : homotopyMap (𝟙 X) hC x n = id := by
  funext a
  induction a using Quot.inductionOn with
  | h a =>
    apply congrArg (Quot.mk _)
    exact Subtype.ext rfl

theorem homotopyMap_comp (hC : C.IsCoherator) {X Y Z : C.Model}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.underlying.Cell 0) (n : ℕ) :
    homotopyMap (f ≫ g) hC x n =
      homotopyMap g hC ((underlyingMap f).app 0 x) n ∘ homotopyMap f hC x n := by
  funext a
  induction a using Quot.inductionOn with
  | h a =>
    apply congrArg (Quot.mk _)
    exact Subtype.ext rfl

theorem weakEquivalence_id (hC : C.IsCoherator) (X : C.Model) :
    WeakEquivalence hC (𝟙 X) := by
  constructor
  · rw [componentsMap_id]
    exact Function.bijective_id
  · intro x n
    rw [homotopyMap_id]
    exact Function.bijective_id

theorem weakEquivalence_comp (hC : C.IsCoherator) {X Y Z : C.Model}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : WeakEquivalence hC f) (hg : WeakEquivalence hC g) :
    WeakEquivalence hC (f ≫ g) := by
  constructor
  · rw [componentsMap_comp]
    exact hg.1.comp hf.1
  · intro x n
    rw [homotopyMap_comp]
    exact (hg.2 _ n).comp (hf.2 x n)

theorem weakEquivalence_of_isIso (hC : C.IsCoherator) {X Y : C.Model}
    (f : X ⟶ Y) [IsIso f] : WeakEquivalence hC f := by
  apply weakEquivalence_of_exactBoundaryTest hC
  intro n b y hy
  refine ⟨(underlyingMap (inv f)).app n y, ?_, ?_⟩
  · rw [← (underlyingMap (inv f)).boundary_app, hy,
      ← GlobularSet.Hom.boundaryMap_comp, ← underlyingMap_comp,
      IsIso.hom_inv_id, underlyingMap_id, boundaryMap_id]
  · have h : (underlyingMap f).app n ((underlyingMap (inv f)).app n y) = y := by
      change (underlyingMap (inv f ≫ f)).app n y = y
      rw [IsIso.inv_hom_id, underlyingMap_id]
      rfl
    rw [h]
    exact Y.joined_refl hC n y

end HomotopyHypothesis.Category.CylinderCorollary

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory OAI.Grothendieck

theorem weakEquivalence_closure_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    MorphismProperty.isomorphisms C.Model ≤ W hC ∧ (W hC).IsMultiplicative := by
  constructor
  · intro X Y f hf
    letI : IsIso f := hf
    exact Category.CylinderCorollary.weakEquivalence_of_isIso hC f
  · exact {
      id_mem := Category.CylinderCorollary.weakEquivalence_id hC
      comp_mem := fun f g hf hg => Category.CylinderCorollary.weakEquivalence_comp hC f g hf hg }

#print axioms weakEquivalence_closure_proof

end HomotopyHypothesis.Blueprint.Packages
