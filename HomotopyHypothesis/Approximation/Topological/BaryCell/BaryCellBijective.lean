import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.BarycentricCell.Proof
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellSingular
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdToDprism

/-!
# `baryCell_bijective`

One declaration of `HomotopyHypothesis.Approximation.Topological.BaryCell`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- **The barycentric map `‖Δ_k'‖ ⟶ ‖Δ_k‖` is bijective**: every point of `Δ_k` is uniquely a
convex combination, with positive weights, of the barycentres of a strictly increasing chain of
faces. Frozen helper statement. -/
theorem baryCell_bijective (k : ℕ) :
    Function.Bijective (realization.map (sdToDprism k).toSemiSSet.{u} ≫
      Approximation.DerivedPrismTop.dprismCellProjection.{u} k).hom := _root_.HomotopyHypothesis.Approximation.BarycentricCell.baryCell_bijective_proof ..
