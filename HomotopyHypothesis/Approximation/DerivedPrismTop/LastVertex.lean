import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismTop.DerivedPositions
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismHom
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map
import HomotopyHypothesis.Approximation.Topological.Projection
/-!
# Last-vertex positions on derived-cylinder cells

The last-vertex projection sends a top vertex to itself and a middle vertex to the last vertex of
its face.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismTop

open HomotopyHypothesis.Approximation.Topological HomotopyHypothesis.Approximation.Topological.Complex
  HomotopyHypothesis.Henry.SemiSSet PV

/-- The vertex position defining the last-vertex projection. -/
noncomputable def dprismLastVertex {k : ℕ} : PV k → Fin (k + 1)
  | .top i => i
  | .mid S => if h : S.Nonempty then S.max' h else 0

/-- Last-vertex positions commute with injective face maps on every derived-cylinder simplex. -/
theorem dprismLastVertex_map_of_mem {k l : ℕ}
    (t : Fin (k + 1) → Fin (l + 1)) (ht : StrictMono t)
    (A : Finset (PV k)) (hA : (dprismComplex k).S A) {a : PV k} (ha : a ∈ A) :
    dprismLastVertex (PV.map t a) = t (dprismLastVertex a) := by
  cases a with
  | top i => rfl
  | mid S =>
      have hS : S.Nonempty := hA.1 S (by simpa using ha)
      have hS' : (S.image t).Nonempty := hS.image t
      simp only [PV.map, dprismLastVertex, dif_pos hS, dif_pos hS']
      have hmax : (S.image t).max' hS' = t (S.max' hS) := by
        exact Finset.max'_image ht.monotone S hS'
      exact hmax

/-- Postcomposing an affine projection by a simplex vertex map composes its vertex assignment. -/
theorem complex_affineProj_comp_affineMap {V : Type} [LinearOrder V]
    (K : Complex V) {m l : ℕ} (π : V → Fin (m + 1))
    (t : Fin (m + 1) → Fin (l + 1)) :
    K.affineProj.{u} π ≫ affineMap t = K.affineProj (t ∘ π) := by
  dsimp [realization]
  change ((realAdj.{u}.homEquiv K.toSemiSSet
      (toTop.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m))).symm
        (K.affineNatTrans π)) ≫ affineMap t =
    ((realAdj.{u}.homEquiv K.toSemiSSet
      (toTop.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk l))).symm
        (K.affineNatTrans (t ∘ π)))
  rw [← (realAdj.{u}).homEquiv_naturality_right_symm]
  apply congrArg ((realAdj.{u}.homEquiv K.toSemiSSet
    (toTop.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk l))).symm)
  ext d σ
  change ULift.up
      (affineMap (X := d.unop) (Y := HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)
        (π ∘ σ.down.1) ≫ affineMap t) =
    ULift.up (affineMap (X := d.unop)
      (Y := HomotopyHypothesis.Henry.SemiSimplexCategory.mk l)
      ((t ∘ π) ∘ σ.down.1))
  rw [affineMap_comp]
  rfl

/-- The affine last-vertex projection on the realization of a derived-cylinder simplex. -/
noncomputable def dprismLastVertexCellProjection (k : ℕ) :
    realization.{u}.obj (dprism.{u} k) ⟶
      toTop.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk k) :=
  (dprismComplex k).affineProj dprismLastVertex

/-- The last-vertex cell projections commute with face maps. -/
theorem dprismLastVertexCellProjection_naturality {k l : ℕ}
    (θ : HomotopyHypothesis.Henry.SemiSimplexCategory.mk k ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk l) :
    realization.{u}.map (dprismCos.{u}.map θ) ≫ dprismLastVertexCellProjection l =
      dprismLastVertexCellProjection k ≫ toTop.{u}.map θ := by
  let t := θ.1.toOrderHom
  let ht : StrictMono t := SemiSimplexCategory.strictMono θ
  let ψ := dprismHom ht
  have hvertex : ∀ (n : ℕ) (σ : (dprismComplex k).Simplex n),
      dprismLastVertex ∘ PV.map t ∘ σ.1 = t ∘ dprismLastVertex ∘ σ.1 := by
    intro n σ
    funext i
    change dprismLastVertex (PV.map t (σ.1 i)) = t (dprismLastVertex (σ.1 i))
    exact dprismLastVertex_map_of_mem t ht (Finset.univ.image σ.1) σ.2.2
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have h₁ :
      realization.{u}.map (dprismCos.{u}.map θ) ≫ dprismLastVertexCellProjection l =
        (dprismComplex k).affineProj (dprismLastVertex ∘ PV.map t) := by
    change realization.{u}.map ψ.toSemiSSet ≫
      (dprismComplex l).affineProj dprismLastVertex = _
    rw [Complex.map_affineProj]
    dsimp [ψ, dprismHom, t]
  have h₂ :
      (dprismComplex k).affineProj (dprismLastVertex ∘ PV.map t) =
        (dprismComplex k).affineProj (t ∘ dprismLastVertex) := by
    apply Complex.affineProj_congr
    intro n σ
    exact hvertex n σ
  have h₃ :
      (dprismComplex k).affineProj (t ∘ dprismLastVertex) =
        dprismLastVertexCellProjection k ≫ toTop.{u}.map θ := by
    rw [dprismLastVertexCellProjection, toTop_map_eq_affineMap]
    exact (complex_affineProj_comp_affineMap (dprismComplex k) dprismLastVertex t).symm
  exact h₁.trans h₂ |>.trans h₃

end HomotopyHypothesis.Approximation.DerivedPrismTop
