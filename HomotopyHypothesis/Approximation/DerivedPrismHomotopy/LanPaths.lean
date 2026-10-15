import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellSingular
import HomotopyHypothesis.Approximation.DerivedPrismTop.LanProjection
import HomotopyHypothesis.Approximation.DerivedPrismTop.LastVertex
import HomotopyHypothesis.Approximation.DerivedPrismTop.LastVertexLanProjection
import HomotopyHypothesis.Approximation.DerivedPrismHomotopy.CellHomotopy
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
/-!
# Gluing the straight-line paths of the derived cylinder
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismHomotopy

open HomotopyHypothesis.Approximation.Topological HomotopyHypothesis.Approximation.DerivedPrismTop
  HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- Evaluation of a path at a fixed time. -/
noncomputable def pathEvaluation (t : unitInterval) :
    pathSpaceFunctor.{u} ⟶ 𝟭 TopCat.{u} where
  app X := TopCat.ofHom ⟨fun p => p t, continuous_eval_const t⟩
  naturality X Y f := by ext p; rfl

/-- Constant paths vary continuously with their value. -/
noncomputable def constantPaths : 𝟭 TopCat.{u} ⟶ pathSpaceFunctor.{u} where
  app X := TopCat.ofHom ContinuousMap.const'
  naturality X Y f := by ext x t; rfl

/-- The unit for the realized derived-cylinder left Kan extension. -/
noncomputable def dprismRealizationUnit : dprismCos.{u} ⋙ realization.{u} ⟶
    stdSimplex.{u} ⋙ (dprismLan.{u} ⋙ realization.{u}) :=
  Functor.whiskerRight (stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}) realization.{u} ≫
    (Functor.associator _ _ _).hom

theorem dprismLanRealization_isLeftKanExtension :
    (dprismLan.{u} ⋙ realization.{u}).IsLeftKanExtension dprismRealizationUnit.{u} := by
  letI : realization.{u}.PreservesPointwiseLeftKanExtension dprismCos.{u} stdSimplex.{u} := by
    intro V
    letI : PreservesColimit (CostructuredArrow.proj stdSimplex.{u} V ⋙ dprismCos.{u})
        realization.{u} :=
      (realAdj.{u}).leftAdjoint_preservesColimits.preservesColimitsOfShape.preservesColimit
    infer_instance
  exact (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    (F' := dprismLan.{u}) (stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u})).postcompose
      realization.{u} |>.isLeftKanExtension

/-- Natural transformations on semi-simplex objects are determined by standard objects. -/
theorem natTrans_ext_standard {F G : Henry.SemiSimplexCategory ⥤ TopCat.{u}}
    {f g : F ⟶ G}
    (h : ∀ k, f.app (Henry.SemiSimplexCategory.mk k) =
      g.app (Henry.SemiSimplexCategory.mk k)) : f = g := by
  apply NatTrans.ext
  funext j
  let e := eqToHom (semiSimplexMkEq j)
  apply (cancel_epi (F.map e)).1
  rw [f.naturality, g.naturality, h j.obj.len]

/-- Maps out of the realized derived cylinder are determined by their cell restrictions. -/
theorem dprismLan_hom_ext {F : SemiSSet.{u} ⥤ TopCat.{u}}
    {f g : dprismLan.{u} ⋙ realization.{u} ⟶ F}
    (h : ∀ k, realization.{u}.map
        ((stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
          (Henry.SemiSimplexCategory.mk k)) ≫
        f.app (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) =
      realization.{u}.map
        ((stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
          (Henry.SemiSimplexCategory.mk k)) ≫
        g.app (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k))) : f = g := by
  letI := dprismLanRealization_isLeftKanExtension.{u}
  apply Functor.hom_ext_of_isLeftKanExtension
    (F' := dprismLan.{u} ⋙ realization.{u}) (α := dprismRealizationUnit.{u})
  apply natTrans_ext_standard
  intro k
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, dprismRealizationUnit,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id] using h k

/-- The cell paths descend through realization of the derived-cylinder colimit. -/
noncomputable def dprismLanPaths :
    dprismLan.{u} ⋙ realization.{u} ⟶ realization.{u} ⋙ pathSpaceFunctor.{u} := by
  letI := dprismLanRealization_isLeftKanExtension.{u}
  exact (dprismLan.{u} ⋙ realization.{u}).descOfIsLeftKanExtension
    dprismRealizationUnit.{u} (realization.{u} ⋙ pathSpaceFunctor.{u})
    (dprismCellStraightPath.{u} ≫
      Functor.whiskerRight (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}) pathSpaceFunctor.{u} ≫
      (Functor.associator _ _ _).hom)

@[reassoc]
theorem dprismLanPaths_cell (k : ℕ) :
    realization.{u}.map ((stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
      (Henry.SemiSimplexCategory.mk k)) ≫
      dprismLanPaths.{u}.app (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) =
    dprismCellStraightPath.{u}.app (Henry.SemiSimplexCategory.mk k) ≫
      pathSpaceFunctor.{u}.map ((stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
        (Henry.SemiSimplexCategory.mk k)) := by
  letI := dprismLanRealization_isLeftKanExtension.{u}
  have h := Functor.descOfIsLeftKanExtension_fac_app
    (F' := dprismLan.{u} ⋙ realization.{u}) dprismRealizationUnit.{u}
    (realization.{u} ⋙ pathSpaceFunctor.{u})
    (dprismCellStraightPath.{u} ≫
      Functor.whiskerRight (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}) pathSpaceFunctor.{u} ≫
      (Functor.associator _ _ _).hom) (Henry.SemiSimplexCategory.mk k)
  have h' := h
  simp only [dprismRealizationUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id] at h'
  exact h'

/-- Evaluation of the descended paths is natural in the semi-simplicial set. -/
noncomputable def dprismLanPathAt (t : unitInterval) :
    dprismLan.{u} ⋙ realization.{u} ⟶ realization.{u} where
  app V := dprismLanPaths.{u}.app V ≫ (pathEvaluation.{u} t).app (realization.{u}.obj V)
  naturality V W f := by
    have h₁ := dprismLanPaths.{u}.naturality f
    have h₂ := (pathEvaluation.{u} t).naturality (realization.{u}.map f)
    simp only [Category.assoc]
    erw [reassoc_of% h₁, h₂]

theorem dprismLanPathAt_zero :
    dprismLanPathAt.{u} 0 = dprismLanLastVertexProjection.{u} := by
  apply dprismLan_hom_ext
  intro k
  change _ ≫ (dprismLanPaths.{u}.app _ ≫ (pathEvaluation.{u} 0).app _) = _
  erw [dprismLanPaths_cell_assoc, Category.assoc, (pathEvaluation.{u} 0).naturality]
  have h : dprismCellStraightPath.{u}.app (Henry.SemiSimplexCategory.mk k) ≫
      (pathEvaluation.{u} 0).app _ = dprismLastVertexCellProjection.{u} k := by
    ext x
    exact (dprismCellStraightHomotopyStd.{u} k).apply_zero x
  erw [← Category.assoc, h, dprismLanLastVertexProjection_cell]
  rfl

theorem dprismLanPathAt_one :
    dprismLanPathAt.{u} 1 = dprismLanProjection.{u} := by
  apply dprismLan_hom_ext
  intro k
  change _ ≫ (dprismLanPaths.{u}.app _ ≫ (pathEvaluation.{u} 1).app _) = _
  erw [dprismLanPaths_cell_assoc, Category.assoc, (pathEvaluation.{u} 1).naturality]
  have h : dprismCellStraightPath.{u}.app (Henry.SemiSimplexCategory.mk k) ≫
      (pathEvaluation.{u} 1).app _ = dprismCellProjection.{u} k := by
    ext x
    exact (dprismCellStraightHomotopyStd.{u} k).apply_one x
  erw [← Category.assoc, h, dprismLanProjection_cell]
  rfl

end HomotopyHypothesis.Approximation.DerivedPrismHomotopy
