import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellAffine
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellSingular
import HomotopyHypothesis.Approximation.DerivedPrismTop.DerivedPositions
import HomotopyHypothesis.Approximation.DerivedPrismTop.LastVertex
import HomotopyHypothesis.Approximation.DerivedPrismTop.LastVertexLanProjection
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismTop
import HomotopyHypothesis.Approximation.Topological.Projection
/-!
# The top face of the derived-cylinder projections

Both affine projections restrict to the identity on the top simplex of each standard
derived-cylinder cell.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismTop

open HomotopyHypothesis.Approximation.Topological HomotopyHypothesis.Henry.SemiSSet

/-- The affine map of a simplex induced by its identity vertex map is the identity. -/
theorem affineMap_id_simplex (k : ℕ) :
    affineMap.{u} (X := Henry.SemiSimplexCategory.mk k)
      (Y := Henry.SemiSimplexCategory.mk k) (id : Fin (k + 1) → Fin (k + 1)) = 𝟙 _ := by
  ext x
  obtain ⟨x⟩ := x
  change ULift.up (Convexity.StdSimplex.map (R := ℝ) id x) = ULift.up x
  rw [Convexity.StdSimplex.map_id]

/-- The affine map determined by the standard vertices is the identity. -/
theorem simplexMapOfPoints_single (k : ℕ) :
    simplexMapOfPoints.{u} k k (fun i => Convexity.StdSimplex.single i) =
      affineMap.{u} (X := Henry.SemiSimplexCategory.mk k)
        (Y := Henry.SemiSimplexCategory.mk k) (id : Fin (k + 1) → Fin (k + 1)) := by
  ext x
  obtain ⟨x⟩ := x
  change ULift.up (Convexity.StdSimplex.affineMapMk (R := ℝ)
      (fun i => Convexity.StdSimplex.single i) x) =
    ULift.up (Convexity.StdSimplex.map (R := ℝ) id x)
  rw [Convexity.StdSimplex.affineMapMk_apply,
    Convexity.StdSimplex.iConvexComb_single, Convexity.StdSimplex.map_id]

/-- The adjoint cell projection evaluated on a simplex is its assigned affine simplex map. -/
theorem dprismCellProjection_unit {k n : ℕ}
    (σ : (dprismCos.{u}.obj (Henry.SemiSimplexCategory.mk k)).obj
      (op (Henry.SemiSimplexCategory.mk n))) :
    (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app (Henry.SemiSimplexCategory.mk n) ≫
      realization.{u}.map (uliftYonedaEquiv.symm σ) ≫ dprismCellProjection.{u} k =
        dprismCellMap σ.down := by
  have h := Presheaf.uliftYonedaAdjunction_homEquiv_app.{u}
    (stdSimplex.{u}.leftKanExtension toTop.{u})
    (stdSimplex.{u}.leftKanExtensionUnit toTop.{u})
    (dprismCellProjection.{u} k) (Z := op (Henry.SemiSimplexCategory.mk n)) σ
  rw [dprismCellProjection, Equiv.apply_symm_apply] at h
  change ULift.up (dprismCellMap σ.down) =
    ULift.up ((stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
      (Henry.SemiSimplexCategory.mk n) ≫
      realization.{u}.map (uliftYonedaEquiv.symm σ) ≫ dprismCellProjection.{u} k) at h
  exact (congrArg ULift.down h).symm

private theorem dprismTop_simplex_vertices (k : ℕ) :
    (uliftYonedaEquiv (dprismTop.{u} k)).down.1 = fun i => PV.top i := by
  rfl

/-- The barycentric cell projection is the identity on the top simplex. -/
theorem dprismTop_cellProjection (k : ℕ) :
    (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
        (Henry.SemiSimplexCategory.mk k) ≫
      realization.{u}.map (dprismTop.{u} k) ≫ dprismCellProjection.{u} k ≫
      (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
        (Henry.SemiSimplexCategory.mk k) =
      (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
        (Henry.SemiSimplexCategory.mk k) := by
  let σ := uliftYonedaEquiv (dprismTop.{u} k)
  have hσ : uliftYonedaEquiv.symm σ = dprismTop.{u} k :=
    Equiv.symm_apply_apply _ _
  have hvertices : σ.down.1 = fun i => PV.top i := by
    exact dprismTop_simplex_vertices.{u} k
  have hpos : dprismPosition ∘ σ.down.1 =
      (fun i => Convexity.StdSimplex.single i) := by
    funext i
    rw [hvertices]
    rfl
  have hcell : dprismCellMap σ.down =
      affineMap.{u} (X := Henry.SemiSimplexCategory.mk k)
        (Y := Henry.SemiSimplexCategory.mk k) (id : Fin (k + 1) → Fin (k + 1)) := by
    unfold dprismCellMap
    rw [hpos]
    exact simplexMapOfPoints_single k
  have htop := dprismCellProjection_unit (k := k) (n := k)
    σ
  have htopMap :
      (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) ≫ realization.{u}.map (dprismTop.{u} k) ≫
        dprismCellProjection.{u} k =
      (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) ≫
        realization.{u}.map (uliftYonedaEquiv.symm σ) ≫ dprismCellProjection.{u} k :=
    congrArg (fun f => (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
      (Henry.SemiSimplexCategory.mk k) ≫ realization.{u}.map f ≫ dprismCellProjection.{u} k)
      hσ.symm
  have htopWithUnit := congrArg (fun f => f ≫
    (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
      (Henry.SemiSimplexCategory.mk k)) htopMap
  have hcellWithUnit := congrArg (fun f => f ≫
    (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
      (Henry.SemiSimplexCategory.mk k)) hcell
  calc
    _ = ((stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) ≫ realization.{u}.map (dprismTop.{u} k) ≫
          dprismCellProjection.{u} k) ≫
        (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) := by cat_disch
    _ = ((stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) ≫ realization.{u}.map
            (uliftYonedaEquiv.symm σ) ≫ dprismCellProjection.{u} k) ≫
        (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) := htopWithUnit
    _ = dprismCellMap σ.down ≫
        (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) := congrArg (fun f => f ≫
            (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
              (Henry.SemiSimplexCategory.mk k)) htop
    _ = (affineMap.{u} (X := Henry.SemiSimplexCategory.mk k)
          (Y := Henry.SemiSimplexCategory.mk k) (id : Fin (k + 1) → Fin (k + 1))) ≫
        (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) := hcellWithUnit
    _ = _ := by rw [affineMap_id_simplex]; cat_disch

/-- The last-vertex cell projection is the identity on the top simplex. -/
theorem dprismTop_lastVertexCellProjection (k : ℕ) :
    (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
        (Henry.SemiSimplexCategory.mk k) ≫
      realization.{u}.map (dprismTop.{u} k) ≫ dprismLastVertexCellProjection.{u} k ≫
      (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
        (Henry.SemiSimplexCategory.mk k) =
      (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
        (Henry.SemiSimplexCategory.mk k) := by
  let σ := uliftYonedaEquiv (dprismTop.{u} k)
  have hσ : uliftYonedaEquiv.symm σ = dprismTop.{u} k :=
    Equiv.symm_apply_apply _ _
  have hvertices : σ.down.1 = fun i => PV.top i := by
    exact dprismTop_simplex_vertices.{u} k
  have hpos : dprismLastVertex ∘ σ.down.1 = id := by
    funext i
    rw [hvertices]
    rfl
  have hcell := Complex.unit_map_affineProj (dprismComplex k) dprismLastVertex σ
  have htopMap :
      (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) ≫ realization.{u}.map (dprismTop.{u} k) ≫
        dprismLastVertexCellProjection.{u} k =
      (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) ≫
        realization.{u}.map (uliftYonedaEquiv.symm σ) ≫
          (dprismComplex k).affineProj dprismLastVertex := by
    rw [dprismLastVertexCellProjection]
    exact congrArg (fun f => (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
      (Henry.SemiSimplexCategory.mk k) ≫ realization.{u}.map f ≫
        (dprismComplex k).affineProj dprismLastVertex) hσ.symm
  have htopWithUnit := congrArg (fun f => f ≫
    (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
      (Henry.SemiSimplexCategory.mk k)) htopMap
  have hcellWithUnit := congrArg (fun f => f ≫
    (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
      (Henry.SemiSimplexCategory.mk k)) hcell
  calc
    _ = ((stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) ≫ realization.{u}.map (dprismTop.{u} k) ≫
          dprismLastVertexCellProjection.{u} k) ≫
        (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) := by cat_disch
    _ = ((stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) ≫ realization.{u}.map
            (uliftYonedaEquiv.symm σ) ≫
          (dprismComplex k).affineProj dprismLastVertex) ≫
        (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) := htopWithUnit
    _ = affineMap (dprismLastVertex ∘ σ.down.1) ≫
        (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) := hcellWithUnit
    _ = (affineMap.{u} (X := Henry.SemiSimplexCategory.mk k)
          (Y := Henry.SemiSimplexCategory.mk k) (id : Fin (k + 1) → Fin (k + 1))) ≫
        (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk k) := congrArg (fun f => f ≫
            (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
              (Henry.SemiSimplexCategory.mk k)) (congrArg affineMap hpos)
    _ = _ := by rw [affineMap_id_simplex]; cat_disch

end HomotopyHypothesis.Approximation.DerivedPrismTop
