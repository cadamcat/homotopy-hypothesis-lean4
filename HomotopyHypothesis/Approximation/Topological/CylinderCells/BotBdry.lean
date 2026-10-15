import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundary
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundaryComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Rank
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder

/-!
# `botBdry`

One declaration of `HomotopyHypothesis.Approximation.Topological.CylinderCells`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

variable {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)

/-- The bottom `Δ_m` in the boundary of the derived double cylinder. -/
def botBdry {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ dcylDBoundary.{u} v :=
  (dcylDBoundaryComplex v).simplexMap (fun c => DV.bot c)
    (fun _ _ h => by
      change DV.rank _ < DV.rank _
      simpa [DV.rank, Prod.Lex.toLex_lt_toLex] using h)
    ⟨⟨by simp, by simp, by simp, by simp, by simp⟩, Or.inl (by simp)⟩
