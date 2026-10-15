import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.FiniteRealization.Proofs

/-!
# `isSimplicial_realization_map`

One declaration of `HomotopyHypothesis.Approximation.Topological.A7Statements`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- The realization of a semi-simplicial map is simplicial. -/
theorem isSimplicial_realization_map {Y X : SemiSSet.{u}} (φ : Y ⟶ X) :
    IsSimplicial (realization.map φ) := _root_.HomotopyHypothesis.Approximation.FiniteRealization.isSimplicial_realization_map_proof ..
