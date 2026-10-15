import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV

/-!
# `sdComplex`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

end PV

/-- The derived simplex `Δ_k'`: the simplices of the derived cylinder without top vertices. -/
def sdComplex (k : ℕ) : Complex (PV k) where
  S A := (dprismComplex k).S A ∧ ∀ i, top i ∉ A
  down _ _ hAB hB := ⟨(dprismComplex k).down hAB hB.1, fun i h => hB.2 i (hAB h)⟩
