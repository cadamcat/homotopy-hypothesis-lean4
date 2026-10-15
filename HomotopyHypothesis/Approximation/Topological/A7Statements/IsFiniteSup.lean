import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.FiniteRealization.Proofs

/-!
# `isFinite_sup`

One declaration of `HomotopyHypothesis.Approximation.Topological.A7Statements`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- The union of two finite semi-simplicial subsets is finite. -/
theorem isFinite_sup {B : SemiSSet.{u}} (S T : Subfunctor B) (hS : SemiSSet.IsFinite S.toFunctor)
    (hT : SemiSSet.IsFinite T.toFunctor) : SemiSSet.IsFinite (S ⊔ T).toFunctor := by apply @_root_.HomotopyHypothesis.Approximation.FiniteRealization.isFinite_sup_proof <;> assumption
