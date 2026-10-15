import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.FiniteRealization.Proofs

/-!
# `compactSpace_realization_of_isFinite'`

One declaration of `HomotopyHypothesis.Approximation.Topological.A7Statements`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- The realization of a finite semi-simplicial set is compact. -/
theorem compactSpace_realization_of_isFinite' {K : SemiSSet.{u}} (hK : K.IsFinite) :
    CompactSpace (realization.obj K) := by apply @_root_.HomotopyHypothesis.Approximation.FiniteRealization.compactSpace_realization_of_isFinite'_proof <;> assumption
