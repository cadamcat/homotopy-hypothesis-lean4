import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellAffine
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellSingular
import HomotopyHypothesis.Approximation.DerivedPrismTop.DerivedPositions
import HomotopyHypothesis.Approximation.DerivedPrismTop.GlobalTopRestriction
import HomotopyHypothesis.Approximation.DerivedPrismTop.LanProjection
import HomotopyHypothesis.Approximation.DerivedPrismTop.LastVertex
import HomotopyHypothesis.Approximation.DerivedPrismTop.LastVertexLanProjection
import HomotopyHypothesis.Approximation.DerivedPrismTop.TopCellRestriction
import HomotopyHypothesis.Approximation.DerivedPrismProjection.PerSimplexProjection
import HomotopyHypothesis.Approximation.DerivedPrismHomotopy.CellHomotopy
import HomotopyHypothesis.Approximation.DerivedPrismHomotopy.LanPaths
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLanTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismTopCos
import HomotopyHypothesis.Approximation.Topological.Projection
/-!
# The relative homotopy between the derived-cylinder projections
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismHomotopy

open HomotopyHypothesis.Approximation.Topological HomotopyHypothesis.Approximation.DerivedPrismTop
  HomotopyHypothesis.Approximation.DerivedPrismProjection HomotopyHypothesis.Henry
  HomotopyHypothesis.Henry.SemiSSet

/-- Both cell projections are the identity on the top characteristic simplex. -/
theorem cellProjections_top (k : ℕ) :
    simplexChar (dprismTop.{u} k) ≫ dprismLastVertexCellProjection.{u} k = 𝟙 _ ∧
    simplexChar (dprismTop.{u} k) ≫ dprismCellProjection.{u} k = 𝟙 _ := by
  constructor
  · erw [dprismLastVertexCellProjection_simplex]
    change affineMap.{u} (X := Henry.SemiSimplexCategory.mk k)
      (Y := Henry.SemiSimplexCategory.mk k) id = 𝟙 _
    exact affineMap_id_simplex k
  · erw [dprismCellProjection_simplexChar]
    change simplexMapOfPoints.{u} k k (fun i => Convexity.StdSimplex.single i) = 𝟙 _
    rw [simplexMapOfPoints_single, affineMap_id_simplex]

/-- The straight-line path is constant on the top simplex of each cell. -/
theorem cellPaths_top (k : ℕ) :
    simplexChar (dprismTop.{u} k) ≫
      dprismCellStraightPath.{u}.app (Henry.SemiSimplexCategory.mk k) =
      constantPaths.{u}.app (toTop.{u}.obj (Henry.SemiSimplexCategory.mk k)) := by
  have hp := (cellProjections_top.{u} k).1
  have hq := (cellProjections_top.{u} k).2
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro t
  have hp' := congrArg (fun f => f.hom x) hp
  have hq' := congrArg (fun f => f.hom x) hq
  change (dprismLastVertexCellProjection.{u} k).hom
    ((simplexChar (dprismTop.{u} k)).hom x) = x at hp'
  change (dprismCellProjection.{u} k).hom
    ((simplexChar (dprismTop.{u} k)).hom x) = x at hq'
  change ULift.up (simplexStraightLine k t
    ((dprismLastVertexCellProjection.{u} k).hom
      ((simplexChar (dprismTop.{u} k)).hom x)).down
    ((dprismCellProjection.{u} k).hom
      ((simplexChar (dprismTop.{u} k)).hom x)).down) = x
  rw [hp', hq']
  simp [simplexStraightLine]
  rfl

/-- On a representable, the top inclusion is the top of the derived-cylinder cell. -/
theorem dprismLanTop_cell (k : ℕ) :
    dprismLanTop.{u}.app (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) =
      dprismTop.{u} k ≫ (stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
        (Henry.SemiSimplexCategory.mk k) := by
  letI : (Functor.id SemiSSet.{u}).IsLeftKanExtension
      (Iso.refl (stdSimplex.{u} ⋙ Functor.id SemiSSet.{u})).hom :=
    Presheaf.isLeftKanExtension_of_preservesColimits.{u} (Functor.id SemiSSet.{u})
      (Iso.refl (stdSimplex.{u} ⋙ Functor.id SemiSSet.{u}))
  have h := Functor.descOfIsLeftKanExtension_fac_app
    (F' := Functor.id SemiSSet.{u})
    (Iso.refl (stdSimplex.{u} ⋙ Functor.id SemiSSet.{u})).hom dprismLan.{u}
    (dprismTopCos.{u} ≫ stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u})
    (Henry.SemiSimplexCategory.mk k)
  have h' := h
  simp only [Functor.id_obj, Iso.refl_hom, NatTrans.id_app, NatTrans.comp_app,
    Category.id_comp] at h'
  exact h'

/-- The realized top inclusions form a natural transformation. -/
noncomputable def realizedDprismTop : realization.{u} ⟶ dprismLan.{u} ⋙ realization.{u} where
  app V := realization.{u}.map (dprismLanTop.{u}.app V)
  naturality V W f := by
    change realization.{u}.map f ≫ realization.{u}.map (dprismLanTop.{u}.app W) =
      realization.{u}.map (dprismLanTop.{u}.app V) ≫ realization.{u}.map (dprismLan.{u}.map f)
    rw [← realization.map_comp, ← realization.map_comp]
    exact congrArg realization.{u}.map (dprismLanTop.{u}.naturality f)

/-- Constant paths on the realizations of semi-simplicial sets. -/
noncomputable def realizationConstantPaths :
    realization.{u} ⟶ realization.{u} ⋙ pathSpaceFunctor.{u} where
  app V := constantPaths.{u}.app (realization.{u}.obj V)
  naturality V W f := (constantPaths.{u}).naturality (realization.{u}.map f)

/-- The descended paths are constant on the top end. -/
theorem dprismLanPaths_top :
    realizedDprismTop.{u} ≫ dprismLanPaths.{u} = realizationConstantPaths.{u} := by
  letI : realization.{u}.IsLeftKanExtension
      (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}) := by
    change (stdSimplex.{u}.leftKanExtension toTop.{u}).IsLeftKanExtension
      (stdSimplex.{u}.leftKanExtensionUnit toTop.{u})
    infer_instance
  apply Functor.hom_ext_of_isLeftKanExtension
    (F' := realization.{u}) (α := stdSimplex.{u}.leftKanExtensionUnit toTop.{u})
  apply natTrans_ext_standard
  intro k
  change (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
      (Henry.SemiSimplexCategory.mk k) ≫
      (realization.{u}.map (dprismLanTop.{u}.app
        (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k))) ≫
        dprismLanPaths.{u}.app _) =
    (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
      (Henry.SemiSimplexCategory.mk k) ≫ constantPaths.{u}.app _
  have e₁ : realization.{u}.map (dprismLanTop.{u}.app
        (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k))) =
      realization.{u}.map (dprismTop.{u} k) ≫
        realization.{u}.map ((stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
          (Henry.SemiSimplexCategory.mk k)) := by
    rw [dprismLanTop_cell]
    exact realization.{u}.map_comp _ _
  rw [e₁]
  erw [Category.assoc, dprismLanPaths_cell]
  have e₂ : (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app (Henry.SemiSimplexCategory.mk k) ≫
      realization.{u}.map (dprismTop.{u} k) ≫
        dprismCellStraightPath.{u}.app (Henry.SemiSimplexCategory.mk k) =
      constantPaths.{u}.app (toTop.{u}.obj (Henry.SemiSimplexCategory.mk k)) :=
    cellPaths_top.{u} k
  erw [← Category.assoc, ← Category.assoc, Category.assoc _ _ (dprismCellStraightPath.{u}.app _), e₂]
  exact (constantPaths.{u}.naturality _).symm

/-- The natural straight-line homotopy, relative to the top end. -/
noncomputable def dprismProjectionHomotopy (V : SemiSSet.{u}) :
    ContinuousMap.HomotopyRel (dprismLanLastVertexProjection.{u}.app V).hom
      (dprismLanProjection.{u}.app V).hom
      (Set.range (realization.{u}.map (dprismLanTop.{u}.app V)).hom) where
  toFun z := (show C(unitInterval, realization.{u}.obj V) from
    (dprismLanPaths.{u}.app V).hom z.2) z.1
  continuous_toFun :=
    ((show C(realization.{u}.obj (dprismLan.{u}.obj V), C(unitInterval, realization.{u}.obj V))
      from (dprismLanPaths.{u}.app V).hom).uncurry.comp ContinuousMap.prodSwap).continuous
  map_zero_left x := by
    have h := congrArg (fun f => (f.app V).hom x) dprismLanPathAt_zero.{u}
    exact h
  map_one_left x := by
    have h := congrArg (fun f => (f.app V).hom x) dprismLanPathAt_one.{u}
    exact h
  prop' t x hx := by
    obtain ⟨y, rfl⟩ := hx
    have h := congrArg (fun f => (show C(unitInterval, realization.{u}.obj V) from
      (f.app V).hom y) t) dprismLanPaths_top.{u}
    have hp := congrArg (fun f => f.hom y) (dprismLanLastVertexProjection_top.{u} V)
    exact h.trans hp.symm

/-- The relative homotopies commute with all maps of semi-simplicial sets. -/
theorem dprismProjectionHomotopy_naturality {V W : SemiSSet.{u}} (f : V ⟶ W)
    (t : unitInterval) (x : realization.{u}.obj (dprismLan.{u}.obj V)) :
    dprismProjectionHomotopy.{u} W
      (t, (realization.{u}.map (dprismLan.{u}.map f)).hom x) =
      (realization.{u}.map f).hom (dprismProjectionHomotopy.{u} V (t, x)) :=
  congrArg (fun g => (show C(unitInterval, realization.{u}.obj W) from g.hom x) t)
    (dprismLanPaths.{u}.naturality f)

end HomotopyHypothesis.Approximation.DerivedPrismHomotopy
