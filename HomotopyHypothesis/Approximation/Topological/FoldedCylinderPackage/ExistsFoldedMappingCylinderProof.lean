import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder
import HomotopyHypothesis.Approximation.Topological.FoldedCylinderPackage.AnodyneCylJBase
import HomotopyHypothesis.Approximation.Topological.FoldedCylinderPackage.AnodyneCylRestrictMap

/-!
# `exists_foldedMappingCylinder_proof`

One declaration of `HomotopyHypothesis.Approximation.Topological.FoldedCylinderPackage`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

end HomotopyHypothesis.Approximation.Topological

namespace HomotopyHypothesis.Henry.Packages

open HomotopyHypothesis.Approximation.Topological HomotopyHypothesis.Henry.SemiSSet

/-- `exists_foldedMappingCylinder`, from the glued derived double cylinders. Inputs:
`anodyne_cylJ_base`, `anodyne_cyl_restrictMap` (collapse), `sharp_exists_normalForm`,
`sharp_normalForm_unique`, `sharp_normalForm_face`, `vertexMap_simplexChar_eq_of_sharpMk_eq`
(normal forms). -/
theorem exists_foldedMappingCylinder_proof {W X J : SemiSSet.{u}} (hW : W.IsFinite) (j : J ⟶ W)
    [Mono j] (g : J ⟶ X) (F : realization.obj W ⟶ realization.obj X) (φ : W ⟶ sharp X)
    (hφ : ∀ (n : ℕ) (y : stdSimplex.obj (SemiSimplexCategory.mk n) ⟶ W),
      ∃ (m : ℕ) (x : stdSimplex.obj (SemiSimplexCategory.mk m) ⟶ X)
        (v : Fin (n + 1) → Fin (m + 1)),
        φ.app (op (SemiSimplexCategory.mk n)) (uliftYonedaEquiv y) =
            sharpMk v (uliftYonedaEquiv x) ∧
          simplexChar y ≫ F = vertexMap v ≫ simplexChar x)
    (hφJ : ∀ (n : ℕ) (z : stdSimplex.obj (SemiSimplexCategory.mk n) ⟶ J),
      φ.app (op (SemiSimplexCategory.mk n)) (uliftYonedaEquiv (z ≫ j)) =
        sharpMk id (uliftYonedaEquiv (z ≫ g))) :
    ∃ (P₂ P M : SemiSSet.{u}) (b₂ : X ⟶ P₂) (V : P ⟶ P₂) (i : P ⟶ M) (a : W ⟶ M) (t : J ⟶ P)
      (ρ₂ : realization.obj P₂ ⟶ realization.obj X) (ρ : realization.obj M ⟶ realization.obj X),
      anodyne b₂ ∧ anodyne i ∧ j ≫ a = t ≫ i ∧ t ≫ V = g ≫ b₂ ∧
        realization.map b₂ ≫ ρ₂ = 𝟙 _ ∧ realization.map i ≫ ρ = realization.map V ≫ ρ₂ ∧
          realization.map a ≫ ρ = F := by
  have hφJ' : ∀ y : J.Elements, φ.app y.obj (j.app y.obj y.val) =
      sharpMk (n := elDim y) id (g.app y.obj y.val) := by
    intro y
    have := hφJ (elDim y) (uliftYonedaEquiv.symm y.val)
    rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_comp, Equiv.apply_symm_apply] at this
    exact this
  have hRJ : (cylJ j φ).botN ≫ Functor.whiskerLeft (elMap j) (rhoN φ) =
      (cylJ j φ).xN ≫ (Functor.const _).map (unitX X) := by
    apply NatTrans.ext
    funext i
    exact congrArg (fun τ => τ.app ((elMap j).obj i)) (botN_rhoN φ)
  refine ⟨(cylJ j φ).obj, (cylJ j φ).obj, (cylDatum φ).obj, (cylJ j φ).base,
    foldMap j g φ hφJ', (cylDatum φ).restrictMap (elMap j), topW φ, topJ j φ,
    (cylJ j φ).proj _ hRJ, (cylDatum φ).proj (rhoN φ) (botN_rhoN φ),
    anodyne_cylJ_base hW j φ, anodyne_cyl_restrictMap hW j φ, j_topW j φ,
    topJ_fold j g φ hφJ', (cylJ j φ).base_proj _ hRJ, ?_, ?_⟩
  · unfold CylDatum.proj
    rw [realization_map_homEquiv_symm, realization_map_homEquiv_symm]
    congr 1
    exact ((cylDatum φ).restrictMap_toSing (elMap j) (rhoN φ) (botN_rhoN φ)).trans
      (foldMap_toSing j g φ hφJ').symm
  · unfold CylDatum.proj
    rw [realization_map_homEquiv_symm, topW_toSing φ F hφ]
    exact Equiv.symm_apply_apply _ F
