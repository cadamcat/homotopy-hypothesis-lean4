import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellSingular
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
/-!
# Projection of the derived-cylinder realization

The cell projections descend over the simplices of a semi-simplicial set by the universal
property of the left Kan extension defining the derived cylinder.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismTop

open HomotopyHypothesis.Approximation.Topological HomotopyHypothesis.Henry.SemiSSet

private theorem realization_preserves_dprismCos :
    realization.{u}.PreservesPointwiseLeftKanExtension dprismCos.{u} stdSimplex.{u} := by
  intro X
  letI : PreservesColimit
      (CategoryTheory.CostructuredArrow.proj stdSimplex.{u} X ⋙ dprismCos.{u}) realization.{u} :=
    (realAdj.{u}).leftAdjoint_preservesColimits.preservesColimitsOfShape.preservesColimit
  infer_instance

/-- The affine cell projections glued over all simplices of a semi-simplicial set. -/
noncomputable def dprismLanProjection : dprismLan.{u} ⋙ realization.{u} ⟶ realization.{u} := by
  let η := stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}
  let α := Functor.whiskerRight η realization.{u} ≫ (Functor.associator _ _ _).hom
  letI := realization_preserves_dprismCos.{u}
  letI : (dprismLan.{u} ⋙ realization.{u}).IsLeftKanExtension α := by
    let h := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
      (F' := dprismLan.{u}) η
    exact h.postcompose realization.{u} |>.isLeftKanExtension
  exact (dprismLan.{u} ⋙ realization.{u}).descOfIsLeftKanExtension α realization.{u}
    (dprismCosProjection.{u} ≫ stdSimplex.{u}.leftKanExtensionUnit toTop.{u})

/-- The glued projection restricts to the affine projection on each derived-cylinder cell. -/
@[reassoc (attr := simp)]
theorem dprismLanProjection_cell (k : ℕ) :
    realization.{u}.map ((stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
      (Henry.SemiSimplexCategory.mk k)) ≫
        dprismLanProjection.{u}.app (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) =
      dprismCellProjection.{u} k ≫
        (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) := by
  let η := stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}
  let α := Functor.whiskerRight η realization.{u} ≫ (Functor.associator _ _ _).hom
  let β := dprismCosProjection.{u} ≫ stdSimplex.{u}.leftKanExtensionUnit toTop.{u}
  letI := realization_preserves_dprismCos.{u}
  letI : (dprismLan.{u} ⋙ realization.{u}).IsLeftKanExtension α := by
    let h := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
      (F' := dprismLan.{u}) η
    exact h.postcompose realization.{u} |>.isLeftKanExtension
  have h := Functor.descOfIsLeftKanExtension_fac_app
    (F' := dprismLan.{u} ⋙ realization.{u}) α realization.{u} β
    (Henry.SemiSimplexCategory.mk k)
  have h' :
      realization.{u}.map (η.app (Henry.SemiSimplexCategory.mk k)) ≫
        ((dprismLan.{u} ⋙ realization.{u}).descOfIsLeftKanExtension
          α realization.{u} β).app (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) =
      dprismCosProjection.{u}.app (Henry.SemiSimplexCategory.mk k) ≫
        (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) := by
    simpa only [α, β, Functor.whiskerRight_app, Functor.associator_hom_app,
      NatTrans.comp_app, Category.comp_id, Category.id_comp] using h
  rw [← dprismCellProjectionAt_mk.{u} k]
  change realization.{u}.map (η.app (Henry.SemiSimplexCategory.mk k)) ≫
      ((dprismLan.{u} ⋙ realization.{u}).descOfIsLeftKanExtension α
        realization.{u} β).app (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) =
    dprismCellProjectionAt.{u} (Henry.SemiSimplexCategory.mk k) ≫
      (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
        (Henry.SemiSimplexCategory.mk k)
  exact h'

end HomotopyHypothesis.Approximation.DerivedPrismTop
