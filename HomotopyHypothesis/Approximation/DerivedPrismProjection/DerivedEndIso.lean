import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.FiniteRealization.Proofs
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellSingular
import HomotopyHypothesis.Approximation.DerivedPrismTop.LanProjection
import HomotopyHypothesis.Approximation.DerivedPrismProjection.PerSimplexProjection
import HomotopyHypothesis.Approximation.Topological.BaryCell.BaryCellBijective
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLanToDprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdToDprismCos
/-!
# The realization of a derived simplex
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismProjection

open HomotopyHypothesis.Approximation.Topological HomotopyHypothesis.Approximation.DerivedPrismTop HomotopyHypothesis.Henry
  HomotopyHypothesis.Henry.SemiSSet

/-- The derived simplex has finitely many simplices. -/
theorem sdComplex_isFinite (m : ℕ) : (sdComplex m).toSemiSSet.{u}.IsFinite := by
  classical
  letI : Finite (Finset (Fin (m + 1))) := inferInstance
  letI : Finite (PV m) := Finite.of_injective
    (fun x : PV m => match x with
      | .top i => Sum.inl i
      | .mid S => Sum.inr S)
    (by intro a b h; cases a <;> cases b <;> simp_all)
  letI : Fintype (PV m) := Fintype.ofFinite (PV m)
  constructor
  · intro n
    change Finite (ULift.{u} ((sdComplex m).Simplex n))
    letI : Finite ((sdComplex m).Simplex n) :=
      Finite.of_injective (fun x => x.1) Subtype.val_injective
    infer_instance
  · refine ⟨Fintype.card (PV m), ?_⟩
    intro n hn
    change IsEmpty (ULift.{u} ((sdComplex m).Simplex n))
    refine ⟨fun x => ?_⟩
    have hcard : Fintype.card (Fin (n + 1)) ≤ Fintype.card (PV m) :=
      Fintype.card_le_of_injective x.down.1 x.down.2.1.injective
    simp only [Fintype.card_fin] at hcard
    omega

/-- The cellwise barycentric map on a derived simplex is a homeomorphism. -/
theorem sdCosBaryProjection_isIso (m : ℕ) :
    IsIso (realization.{u}.map
      (sdToDprismCos.{u}.app (Henry.SemiSimplexCategory.mk m)) ≫
        Approximation.DerivedPrismTop.dprismCellProjection.{u} m) := by
  let f := realization.{u}.map
    (sdToDprismCos.{u}.app (Henry.SemiSimplexCategory.mk m)) ≫
      Approximation.DerivedPrismTop.dprismCellProjection.{u} m
  have hbij : Function.Bijective f.hom := by
    change Function.Bijective
      (realization.{u}.map (sdToDprism m).toSemiSSet ≫
        Approximation.DerivedPrismTop.dprismCellProjection.{u} m).hom
    exact baryCell_bijective.{u} m
  letI : CompactSpace (realization.{u}.obj
      (sdCos.{u}.obj (Henry.SemiSimplexCategory.mk m))) := by
    change CompactSpace (realization.{u}.obj ((sdComplex m).toSemiSSet.{u}))
    exact HomotopyHypothesis.Approximation.FiniteRealization.compactSpace_realization_of_isFinite'_proof
      (sdComplex_isFinite.{u} m)
  letI : T2Space (Convexity.StdSimplex ℝ (Fin (m + 1))) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (m + 1))).t2Space
  letI : T2Space (ULift.{u} (Convexity.StdSimplex ℝ (Fin (m + 1)))) := inferInstance
  letI : T2Space (toTop.{u}.obj (Henry.SemiSimplexCategory.mk m)) := by
    change T2Space (ULift.{u} (Convexity.StdSimplex ℝ (Fin (m + 1))))
    infer_instance
  have hhomeo : IsHomeomorph f.hom :=
    (isHomeomorph_iff_continuous_bijective).2 ⟨f.hom.continuous, hbij⟩
  exact (TopCat.isIso_iff_isHomeomorph f).2 hhomeo

/-- The barycentric projections from the derived-simplex cells form a natural transformation. -/
noncomputable def sdCosBaryProjection : sdCos.{u} ⋙ realization.{u} ⟶ toTop.{u} :=
  Functor.whiskerRight sdToDprismCos.{u} realization.{u} ≫
    Approximation.DerivedPrismTop.dprismCosProjection.{u}

/-- Each component of the cellwise barycentric transformation is an isomorphism. -/
theorem sdCosBaryProjection_isIso_at (j : Henry.SemiSimplexCategory) :
    IsIso (sdCosBaryProjection.{u}.app j) := by
  cases j with
  | mk jObj =>
    cases jObj with
    | mk m =>
      simpa [sdCosBaryProjection, Approximation.DerivedPrismTop.dprismCosProjection,
        Approximation.DerivedPrismTop.dprismCellProjectionAt_mk] using sdCosBaryProjection_isIso.{u} m

/-- The cellwise barycentric transformation is a natural isomorphism. -/
noncomputable def sdCosBaryIso : sdCos.{u} ⋙ realization.{u} ≅ toTop.{u} := by
  letI : ∀ j : Henry.SemiSimplexCategory, IsIso (sdCosBaryProjection.{u}.app j) :=
    sdCosBaryProjection_isIso_at.{u}
  exact NatIso.ofComponents (fun j => asIso (sdCosBaryProjection.{u}.app j))
    (by
      intro i j f
      exact sdCosBaryProjection.{u}.naturality f)

@[simp]
theorem sdCosBaryIso_hom : sdCosBaryIso.{u}.hom = sdCosBaryProjection.{u} := rfl

/-- The unit map for realizing the left Kan extension that defines the derived end. -/
private noncomputable def sdLanRealizationUnit :
    sdCos.{u} ⋙ realization.{u} ⟶
      Henry.SemiSSet.stdSimplex.{u} ⋙ (sdLan.{u} ⋙ realization.{u}) :=
  Functor.whiskerRight
      (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u}) realization.{u} ≫
    (Functor.associator _ _ _).hom

private theorem realization_preserves_sdCos :
    realization.{u}.PreservesPointwiseLeftKanExtension sdCos.{u}
      Henry.SemiSSet.stdSimplex.{u} := by
  intro X
  letI : PreservesColimit
      (CategoryTheory.CostructuredArrow.proj Henry.SemiSSet.stdSimplex.{u} X ⋙ sdCos.{u})
      realization.{u} :=
    (realAdj.{u}).leftAdjoint_preservesColimits.preservesColimitsOfShape.preservesColimit
  infer_instance

/-- Realization of the derived end is the left Kan extension of its realized cells. -/
theorem sdLanRealization_isLeftKanExtension :
    (sdLan.{u} ⋙ realization.{u}).IsLeftKanExtension sdLanRealizationUnit.{u} := by
  letI := realization_preserves_sdCos.{u}
  let h := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    (F' := sdLan.{u}) (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u})
  exact h.postcompose realization.{u} |>.isLeftKanExtension

/-- The global barycentric map from the derived end to the original realization. -/
noncomputable def sdLanBarycentricProjection :
    sdLan.{u} ⋙ realization.{u} ⟶ realization.{u} where
  app V := realization.{u}.map (sdLanToDprism.{u}.app V) ≫
    dprismLanProjection.{u}.app V
  naturality V V' f := by
    change realization.{u}.map (sdLan.{u}.map f) ≫
        (realization.{u}.map (sdLanToDprism.{u}.app V') ≫
          dprismLanProjection.{u}.app V') =
      (realization.{u}.map (sdLanToDprism.{u}.app V) ≫
        dprismLanProjection.{u}.app V) ≫ realization.{u}.map f
    rw [← Category.assoc, ← Functor.map_comp, sdLanToDprism.naturality,
      Functor.map_comp, Category.assoc, Category.assoc]
    congr 1
    exact dprismLanProjection.naturality f

/-- On each representable cell, the global barycentric map is the cell map. -/
theorem sdLanBarycentricProjection_cell (m : ℕ) :
    realization.{u}.map
        ((Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u}).app
          (Henry.SemiSimplexCategory.mk m)) ≫
      sdLanBarycentricProjection.{u}.app
        (Henry.SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)) =
      sdCosBaryProjection.{u}.app (Henry.SemiSimplexCategory.mk m) ≫
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk m) := by
  conv_lhs =>
    simp only [sdLanBarycentricProjection, Functor.comp_obj]
    rw [← Category.assoc]
    rw [← realization.map_comp]
    rw [sdLanToDprism_cell]
    erw [realization.map_comp]
    erw [Category.assoc, dprismLanProjection_cell.{u} m]
  simpa only [Henry.SemiSSet.realization, sdCosBaryProjection,
    Functor.whiskerRight_app, NatTrans.comp_app,
    Approximation.DerivedPrismTop.dprismCosProjection, Approximation.DerivedPrismTop.dprismCellProjectionAt_mk] using (Category.assoc
      (realization.{u}.map
        (sdToDprismCos.{u}.app (Henry.SemiSimplexCategory.mk m)))
      (dprismCellProjection.{u} m)
      ((Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
        (Henry.SemiSimplexCategory.mk m))).symm

/-- The canonical isomorphism of the two left Kan extensions induced by the cell maps. -/
noncomputable def sdLanRealizationIso :
    sdLan.{u} ⋙ realization.{u} ≅ realization.{u} := by
  letI : (sdLan.{u} ⋙ realization.{u}).IsLeftKanExtension
      sdLanRealizationUnit.{u} := sdLanRealization_isLeftKanExtension.{u}
  letI : realization.{u}.IsLeftKanExtension
      (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u}) := by
    change (Henry.SemiSSet.stdSimplex.{u}.leftKanExtension toTop.{u}).IsLeftKanExtension
      (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u})
    infer_instance
  exact Functor.leftKanExtensionUniqueOfIso
    (F' := sdLan.{u} ⋙ realization.{u}) (α := sdLanRealizationUnit.{u})
    sdCosBaryIso.{u} realization.{u}
    (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u})

/-- The canonical left Kan extension isomorphism has the prescribed map on every cell. -/
theorem sdLanRealizationIso_cell (m : ℕ) :
    sdLanRealizationUnit.{u}.app (Henry.SemiSimplexCategory.mk m) ≫
      sdLanRealizationIso.{u}.hom.app
        (Henry.SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)) =
      sdCosBaryIso.{u}.hom.app (Henry.SemiSimplexCategory.mk m) ≫
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk m) := by
  letI : (sdLan.{u} ⋙ realization.{u}).IsLeftKanExtension
      sdLanRealizationUnit.{u} := sdLanRealization_isLeftKanExtension.{u}
  letI : realization.{u}.IsLeftKanExtension
      (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u}) := by
    change (Henry.SemiSSet.stdSimplex.{u}.leftKanExtension toTop.{u}).IsLeftKanExtension
      (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u})
    infer_instance
  change sdLanRealizationUnit.{u}.app (Henry.SemiSimplexCategory.mk m) ≫
      (Functor.leftKanExtensionUniqueOfIso
        (F' := sdLan.{u} ⋙ realization.{u}) (α := sdLanRealizationUnit.{u})
        sdCosBaryIso.{u} realization.{u}
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u})).hom.app
          (Henry.SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)) = _
  exact Functor.descOfIsLeftKanExtension_fac_app
    (F' := sdLan.{u} ⋙ realization.{u}) (α := sdLanRealizationUnit.{u})
    realization.{u}
    (sdCosBaryIso.{u}.hom ≫ Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u})
    (Henry.SemiSimplexCategory.mk m)

private theorem natTrans_eq_of_standard_components
    {F G : Henry.SemiSimplexCategory ⥤ TopCat.{u}} {α β : F ⟶ G}
    (h : ∀ m, α.app (Henry.SemiSimplexCategory.mk m) =
      β.app (Henry.SemiSimplexCategory.mk m)) : α = β := by
  apply NatTrans.ext
  funext j
  let j₀ := Henry.SemiSimplexCategory.mk j.obj.len
  let e : j₀ ⟶ j := eqToHom (Approximation.DerivedPrismTop.semiSimplexMkEq j)
  have hcancel : F.map e ≫ α.app j = F.map e ≫ β.app j := by
    calc
      F.map e ≫ α.app j = α.app j₀ ≫ G.map e := α.naturality e
      _ = β.app j₀ ≫ G.map e := by rw [h j.obj.len]
      _ = F.map e ≫ β.app j := (β.naturality e).symm
  exact (cancel_epi (F.map e)).1 hcancel

/-- The explicit glued barycentric map is the isomorphism induced by Kan extension uniqueness. -/
theorem sdLanBarycentricProjection_eq_iso_hom :
    sdLanBarycentricProjection.{u} = sdLanRealizationIso.{u}.hom := by
  letI : (sdLan.{u} ⋙ realization.{u}).IsLeftKanExtension
      sdLanRealizationUnit.{u} := sdLanRealization_isLeftKanExtension.{u}
  apply Functor.hom_ext_of_isLeftKanExtension
    (F' := sdLan.{u} ⋙ realization.{u}) (α := sdLanRealizationUnit.{u})
    sdLanBarycentricProjection.{u} sdLanRealizationIso.{u}.hom
  apply natTrans_eq_of_standard_components
  intro m
  let j := Henry.SemiSimplexCategory.mk m
  have hα : sdLanRealizationUnit.{u}.app j = realization.{u}.map
      ((Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u}).app j) := by
    simp [sdLanRealizationUnit]
  have hq₁ :
      (sdLanRealizationUnit.{u} ≫ Functor.whiskerLeft Henry.SemiSSet.stdSimplex.{u}
        sdLanBarycentricProjection.{u}).app j =
      sdCosBaryProjection.{u}.app j ≫
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app j := by
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, hα] using
      sdLanBarycentricProjection_cell.{u} m
  have hq₂ :
      (sdLanRealizationUnit.{u} ≫ Functor.whiskerLeft Henry.SemiSSet.stdSimplex.{u}
        sdLanRealizationIso.{u}.hom).app j =
      sdCosBaryIso.{u}.hom.app j ≫
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app j := by
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app] using
      sdLanRealizationIso_cell.{u} m
  rw [hq₁, ← sdCosBaryIso_hom, ← hq₂]

/-- The glued barycentric map is an isomorphism at every semi-simplicial set. -/
theorem sdLanBarycentricProjection_isIso (V : SemiSSet.{u}) :
    IsIso (sdLanBarycentricProjection.{u}.app V) := by
  rw [sdLanBarycentricProjection_eq_iso_hom.{u}]
  infer_instance

end HomotopyHypothesis.Approximation.DerivedPrismProjection
