import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellSingular
import HomotopyHypothesis.Approximation.DerivedPrismTop.LastVertex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
/-!
# The last-vertex projection of the derived cylinder

The affine last-vertex maps on standard derived-cylinder cells glue over the simplices of a
semi-simplicial set.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismTop

open HomotopyHypothesis.Approximation.Topological HomotopyHypothesis.Henry.SemiSSet

/-- The canonical identification of any semi-simplex with the standard object of its length is
represented by the identity arrow. -/
theorem semiSimplexMkEqToHom_any (j : Henry.SemiSimplexCategory) :
    eqToHom (semiSimplexMkEq j) = 𝟙 _ := by
  apply WideSubcategory.hom_ext
  rfl

/-- The affine last-vertex projection on the derived cylinder of an arbitrary semi-simplex. -/
noncomputable def dprismLastVertexCellProjectionAt (j : Henry.SemiSimplexCategory) :
    realization.obj (dprismCos.{u}.obj j) ⟶ toTop.{u}.obj j :=
  dprismLastVertexCellProjection j.obj.len ≫
    toTop.{u}.map (eqToHom (semiSimplexMkEq j))

/-- The object transport in the cell projection is the identity on the underlying simplex. -/
theorem dprismLastVertexCellProjectionAt_eq (j : Henry.SemiSimplexCategory) :
    dprismLastVertexCellProjectionAt.{u} j =
      dprismLastVertexCellProjection.{u} j.obj.len := by
  unfold dprismLastVertexCellProjectionAt
  change dprismLastVertexCellProjection j.obj.len ≫
      toTop.{u}.map (eqToHom (semiSimplexMkEq j)) =
    dprismLastVertexCellProjection j.obj.len
  rw [semiSimplexMkEqToHom_any, HomotopyHypothesis.Henry.SemiSSet.toTop.map_id]
  rfl

@[simp]
theorem dprismLastVertexCellProjectionAt_mk (k : ℕ) :
    dprismLastVertexCellProjectionAt.{u} (Henry.SemiSimplexCategory.mk k) =
      dprismLastVertexCellProjection.{u} k := by
  simpa using dprismLastVertexCellProjectionAt_eq (Henry.SemiSimplexCategory.mk k)

/-- The affine last-vertex cell maps form a natural transformation. -/
noncomputable def dprismLastVertexCosProjection :
    dprismCos.{u} ⋙ realization.{u} ⟶ toTop.{u} where
  app j := dprismLastVertexCellProjectionAt j
  naturality j j' θ := by
    rw [dprismLastVertexCellProjectionAt_eq, dprismLastVertexCellProjectionAt_eq]
    exact dprismLastVertexCellProjection_naturality θ

private theorem realization_preserves_dprismCos_lastVertex :
    realization.{u}.PreservesPointwiseLeftKanExtension dprismCos.{u} stdSimplex.{u} := by
  intro X
  letI : PreservesColimit
      (CategoryTheory.CostructuredArrow.proj stdSimplex.{u} X ⋙ dprismCos.{u}) realization.{u} :=
    (realAdj.{u}).leftAdjoint_preservesColimits.preservesColimitsOfShape.preservesColimit
  infer_instance

/-- The last-vertex projection glued over the simplices of a semi-simplicial set. -/
noncomputable def dprismLanLastVertexProjection :
    dprismLan.{u} ⋙ realization.{u} ⟶ realization.{u} := by
  let η := stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}
  let α := Functor.whiskerRight η realization.{u} ≫ (Functor.associator _ _ _).hom
  letI := realization_preserves_dprismCos_lastVertex.{u}
  letI : (dprismLan.{u} ⋙ realization.{u}).IsLeftKanExtension α := by
    let h := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
      (F' := dprismLan.{u}) η
    exact h.postcompose realization.{u} |>.isLeftKanExtension
  exact (dprismLan.{u} ⋙ realization.{u}).descOfIsLeftKanExtension α realization.{u}
    (dprismLastVertexCosProjection.{u} ≫ stdSimplex.{u}.leftKanExtensionUnit toTop.{u})

/-- The glued last-vertex projection restricts to the stated affine map on each cell. -/
@[reassoc (attr := simp)]
theorem dprismLanLastVertexProjection_cell (k : ℕ) :
    realization.{u}.map ((stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
      (Henry.SemiSimplexCategory.mk k)) ≫
        dprismLanLastVertexProjection.{u}.app (stdSimplex.{u}.obj
          (Henry.SemiSimplexCategory.mk k)) =
      dprismLastVertexCellProjection.{u} k ≫
        (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) := by
  let η := stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}
  let α := Functor.whiskerRight η realization.{u} ≫ (Functor.associator _ _ _).hom
  let β := dprismLastVertexCosProjection.{u} ≫
    stdSimplex.{u}.leftKanExtensionUnit toTop.{u}
  letI := realization_preserves_dprismCos_lastVertex.{u}
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
          α realization.{u} β).app (stdSimplex.{u}.obj
            (Henry.SemiSimplexCategory.mk k)) =
      dprismLastVertexCosProjection.{u}.app (Henry.SemiSimplexCategory.mk k) ≫
        (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) := by
    simpa only [α, β, Functor.whiskerRight_app, Functor.associator_hom_app,
      NatTrans.comp_app, Category.comp_id, Category.id_comp] using h
  rw [← dprismLastVertexCellProjectionAt_mk.{u} k]
  change realization.{u}.map (η.app (Henry.SemiSimplexCategory.mk k)) ≫
      ((dprismLan.{u} ⋙ realization.{u}).descOfIsLeftKanExtension α
        realization.{u} β).app (stdSimplex.{u}.obj
          (Henry.SemiSimplexCategory.mk k)) =
    dprismLastVertexCellProjectionAt.{u} (Henry.SemiSimplexCategory.mk k) ≫
      (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
        (Henry.SemiSimplexCategory.mk k)
  exact h'

end HomotopyHypothesis.Approximation.DerivedPrismTop
