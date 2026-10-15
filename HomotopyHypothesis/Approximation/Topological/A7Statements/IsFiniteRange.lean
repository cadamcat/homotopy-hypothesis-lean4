import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.FiniteRealization.Proofs

/-!
# `isFinite_range`

One declaration of `HomotopyHypothesis.Approximation.Topological.A7Statements`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- The image of a finite semi-simplicial set is finite. -/
theorem isFinite_range {A B : SemiSSet.{u}} (f : A ⟶ B) (hA : A.IsFinite) :
    SemiSSet.IsFinite (Subfunctor.range f).toFunctor := by apply @_root_.HomotopyHypothesis.Approximation.FiniteRealization.isFinite_range_proof <;> assumption
