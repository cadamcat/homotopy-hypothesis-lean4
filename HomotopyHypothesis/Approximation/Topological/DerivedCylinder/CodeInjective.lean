import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Code

/-!
# `code_injective`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedCylinder`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

namespace DV

variable {n m : ℕ}

theorem code_injective : Function.Injective (code : Finset (Fin (n + 1)) → ℕ) := by
  intro S S' h
  exact Finset.map_injective Fin.valEmbedding (Finset.equivBitIndices.symm.injective h)
