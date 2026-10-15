import Mathlib.CategoryTheory.Limits.Presheaf
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Prism
import HomotopyHypothesis.Approximation.Zeeman.SubdivisionPrismCompositionStatement
/-!
# Composition of relative subdivision prisms

We construct the composite prism of two successive relative subdivisions by
pushing out their prisms along the intermediate semi-simplicial set.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.PrismComposition

open Henry Henry.SemiSSet Approximation.Zeeman

/-- Composition of anodyne maps is anodyne. -/
theorem anodyne_comp {A B C : SemiSSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : anodyne f) (hg : anodyne g) : anodyne (f ≫ g) := by
  unfold anodyne at hf hg ⊢
  exact (hornInclusions.pushouts ⊔ MorphismProperty.isomorphisms SemiSSet.{u}).multiplicativeClosure.comp_mem
    _ _ hf hg

/-- Composition of relative subdivision prisms. -/
theorem subdivisionPrismCompositionStatement_proof :
    SubdivisionPrismCompositionStatement.{u} := by
  intro Y J S₁ S₂
  have : PreservesColimitsOfSize.{0, 0} realization.{u} := by
    change PreservesColimitsOfSize.{0, 0} (uliftYoneda.{u}.leftKanExtension toTop.{u})
    exact Presheaf.preservesColimitsOfSize_leftKanExtension.{u, 0, u, 0, 0, u + 1, 0}
      (C := Henry.SemiSimplexCategory) (ℰ := TopCat.{u}) toTop.{u}
  let C : SemiSSet.{u} := pushout S₁.c₀ S₂.c₁
  let a : S₂.Y' ⟶ C := S₂.c₀ ≫ pushout.inr S₁.c₀ S₂.c₁
  let b : Y ⟶ C := S₁.c₁ ≫ pushout.inl S₁.c₀ S₂.c₁
  have P := IsPushout.of_hasPushout S₁.c₀ S₂.c₁
  have H := realization.map_isPushout P
  have h_glue : realization.map S₁.c₀ ≫ (S₁.ρ ≫ S₂.h.inv) =
      realization.map S₂.c₁ ≫ S₂.ρ := by
    rw [← Category.assoc, S₁.hρ₀, Category.id_comp, S₂.hρ₁]
  let ρ : realization.obj C ⟶ realization.obj S₂.Y' :=
    H.desc (S₁.ρ ≫ S₂.h.inv) S₂.ρ h_glue
  refine ⟨C, a, b, ρ, ?_, ?_, ?_, ?_⟩
  · calc
      (Subfunctor.toRange S₁.j ≫ S₂.j) ≫ a
        = Subfunctor.toRange S₁.j ≫ (S₂.j ≫ S₂.c₀) ≫ pushout.inr S₁.c₀ S₂.c₁ := by
        simp only [a, Category.assoc]
      _ = Subfunctor.toRange S₁.j ≫ ((Subfunctor.range S₁.j).ι ≫ S₂.c₁) ≫ pushout.inr S₁.c₀ S₂.c₁ := by
        rw [S₂.hc]
      _ = (Subfunctor.toRange S₁.j ≫ (Subfunctor.range S₁.j).ι) ≫ S₂.c₁ ≫ pushout.inr S₁.c₀ S₂.c₁ := by
        simp only [Category.assoc]
      _ = S₁.j ≫ S₂.c₁ ≫ pushout.inr S₁.c₀ S₂.c₁ := by
        rw [Subfunctor.toRange_ι]
      _ = S₁.j ≫ S₁.c₀ ≫ pushout.inl S₁.c₀ S₂.c₁ := by
        rw [← pushout.condition]
      _ = (S₁.j ≫ S₁.c₀) ≫ pushout.inl S₁.c₀ S₂.c₁ := by
        simp only [Category.assoc]
      _ = (J.ι ≫ S₁.c₁) ≫ pushout.inl S₁.c₀ S₂.c₁ := by
        rw [S₁.hc]
      _ = J.ι ≫ b := by
        simp only [b, Category.assoc]
  · have h_inr : anodyne (pushout.inr S₁.c₀ S₂.c₁) :=
      anodyne_of_isPushout P.flip S₁.anodyne_c₀
    exact anodyne_comp S₂.c₀ (pushout.inr S₁.c₀ S₂.c₁) S₂.anodyne_c₀ h_inr
  · change realization.map (S₂.c₀ ≫ pushout.inr S₁.c₀ S₂.c₁) ≫ ρ = 𝟙 _
    rw [Functor.map_comp, Category.assoc]
    have hinr_desc : realization.map (pushout.inr S₁.c₀ S₂.c₁) ≫ ρ = S₂.ρ :=
      H.inr_desc (S₁.ρ ≫ S₂.h.inv) S₂.ρ h_glue
    rw [hinr_desc, S₂.hρ₀]
  · change realization.map (S₁.c₁ ≫ pushout.inl S₁.c₀ S₂.c₁) ≫ ρ = S₁.h.inv ≫ S₂.h.inv
    rw [Functor.map_comp, Category.assoc]
    have hinl_desc : realization.map (pushout.inl S₁.c₀ S₂.c₁) ≫ ρ = S₁.ρ ≫ S₂.h.inv :=
      H.inl_desc (S₁.ρ ≫ S₂.h.inv) S₂.ρ h_glue
    rw [hinl_desc, ← Category.assoc, S₁.hρ₁]

example : SubdivisionPrismCompositionStatement.{u} :=
  subdivisionPrismCompositionStatement_proof

#print axioms subdivisionPrismCompositionStatement_proof

end HomotopyHypothesis.Approximation.PrismComposition
