import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellAffine
import HomotopyHypothesis.Approximation.DerivedPrismTop.DerivedPositions
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map
import HomotopyHypothesis.Approximation.Topological.Projection
/-!
# Naturality of derived-cylinder cell maps

The barycentric affine maps on the cells of a derived cylinder commute with face maps.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismTop

open HomotopyHypothesis.Approximation.Topological PV HomotopyHypothesis.Henry.SemiSSet

/-- A derived-cylinder cell map commutes with an injective face map of its target simplex. -/
theorem dprismCellMap_postcompose {k l n : ℕ}
    (t : Fin (k + 1) → Fin (l + 1)) (ht : StrictMono t)
    (σ : (dprismComplex k).Simplex n) (τ : (dprismComplex l).Simplex n)
    (hτ : τ.1 = PV.map t ∘ σ.1) :
    dprismCellMap σ ≫ affineMap t = dprismCellMap τ := by
  change simplexMapOfPoints n k (dprismPosition ∘ σ.1) ≫ affineMap t =
    simplexMapOfPoints n l (dprismPosition ∘ τ.1)
  calc
    simplexMapOfPoints n k (dprismPosition ∘ σ.1) ≫ affineMap t =
        simplexMapOfPoints n l (fun i => (dprismPosition (σ.1 i)).map t) :=
      simplexMapOfPoints_comp_affineMap (dprismPosition ∘ σ.1) t
    _ = simplexMapOfPoints n l (dprismPosition ∘ τ.1) := by
      congr 1
      funext i
      rw [hτ]
      exact (dprismPosition_map_of_mem t ht (Finset.univ.image σ.1) σ.2.2 (by simp)).symm

end HomotopyHypothesis.Approximation.DerivedPrismTop
