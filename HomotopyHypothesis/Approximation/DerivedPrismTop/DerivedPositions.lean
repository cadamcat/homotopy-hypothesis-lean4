import Mathlib.LinearAlgebra.AffineSpace.Centroid
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellAffine
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map
/-!
# Barycentric positions in a simplex

The derived cylinder vertices are sent to the original vertices or to the barycentres of their
faces.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismTop

open HomotopyHypothesis.Approximation.Topological PV HomotopyHypothesis.Henry.SemiSSet

/-- The barycentre of a nonempty face as a point of the standard simplex. -/
noncomputable def barycentricPoint {k : ℕ} (S : Finset (Fin (k + 1))) (hS : S.Nonempty) :
    Convexity.StdSimplex ℝ (Fin (k + 1)) where
  weights := Finsupp.equivFunOnFinite.symm (S.centroidWeightsIndicator ℝ)
  nonneg := by
    intro i
    rw [Finsupp.coe_equivFunOnFinite_symm]
    by_cases hi : i ∈ S
    · simp [Finset.centroidWeightsIndicator, Finset.centroidWeights, hi]
    · simp [Finset.centroidWeightsIndicator, hi]
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simpa [Finsupp.coe_equivFunOnFinite_symm] using
      S.sum_centroidWeightsIndicator_eq_one_of_nonempty ℝ hS

/-- The barycentric position assigned to each vertex of the derived cylinder. -/
noncomputable def dprismPosition {k : ℕ} : PV k → Convexity.StdSimplex ℝ (Fin (k + 1))
  | .top i => Convexity.StdSimplex.single i
  | .mid S => if hS : S.Nonempty then barycentricPoint S hS
    else Convexity.StdSimplex.single 0

private theorem barycentricPoint_weights {k : ℕ} (S : Finset (Fin (k + 1)))
    (hS : S.Nonempty) :
    (barycentricPoint S hS).weights =
      ∑ i ∈ S, Finsupp.single i ((S.card : ℝ)⁻¹) := by
  ext i
  simp [barycentricPoint, Finsupp.equivFunOnFinite,
    Finset.centroidWeightsIndicator, Finset.centroidWeights, Set.indicator,
    Finsupp.single_apply]

/-- Barycentres commute with injective maps of vertices. -/
theorem barycentricPoint_map {k l : ℕ} (t : Fin (k + 1) → Fin (l + 1))
    (ht : Function.Injective t) (S : Finset (Fin (k + 1))) (hS : S.Nonempty) :
    (barycentricPoint S hS).map t = barycentricPoint (S.image t) (hS.image t) := by
  apply Convexity.StdSimplex.ext
  rw [Convexity.StdSimplex.weights_map, barycentricPoint_weights S hS,
    barycentricPoint_weights (S.image t) (hS.image t)]
  rw [Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single, Finset.card_image_of_injective S ht]
  exact (Finset.sum_image (s := S) (g := t)
    (f := fun j : Fin (l + 1) => Finsupp.single j ((S.card : ℝ)⁻¹)) ht.injOn).symm

/-- The assigned positions commute with the vertex map on every simplex of the derived cylinder. -/
theorem dprismPosition_map_of_mem {k l : ℕ} (t : Fin (k + 1) → Fin (l + 1))
    (ht : StrictMono t) (A : Finset (PV k)) (hA : (dprismComplex k).S A)
    {a : PV k} (ha : a ∈ A) :
    dprismPosition (PV.map t a) = (dprismPosition a).map t := by
  cases a with
  | top i => simp [PV.map, dprismPosition]
  | mid S =>
      have hS : S.Nonempty := hA.1 S (by simpa using ha)
      simp only [PV.map, dprismPosition, dif_pos hS, dif_pos (hS.image t)]
      exact (barycentricPoint_map t ht.injective S hS).symm

/-- The affine projection of a simplex in the derived cylinder, determined by its vertex positions.
-/
noncomputable def dprismCellMap {k n : ℕ} (σ : (dprismComplex k).Simplex n) :
    toTop.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) ⟶
      toTop.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk k) :=
  simplexMapOfPoints n k (dprismPosition ∘ σ.1)

/-- Restricting a derived-cylinder simplex along a face restricts its affine cell map. -/
theorem dprismCellMap_face {k n m : ℕ}
    (θ : HomotopyHypothesis.Henry.SemiSimplexCategory.mk n ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)
    (σ : (dprismComplex k).Simplex m) (τ : (dprismComplex k).Simplex n)
    (hτ : τ.1 = σ.1 ∘ θ.1.toOrderHom) :
    dprismCellMap τ = toTop.{u}.map θ ≫ dprismCellMap σ := by
  calc
    dprismCellMap τ = simplexMapOfPoints n k (dprismPosition ∘ τ.1) := rfl
    _ = simplexMapOfPoints n k ((dprismPosition ∘ σ.1) ∘ θ.1.toOrderHom) := by
      rw [hτ]
      rfl
    _ = toTop.{u}.map θ ≫ dprismCellMap σ := by
      rw [dprismCellMap]
      exact (simplexMapOfPoints_naturality θ (dprismPosition ∘ σ.1)).symm

end HomotopyHypothesis.Approximation.DerivedPrismTop
