import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.FiniteRealization.Proofs

/-!
# `isFinite_of_mono`

One declaration of `HomotopyHypothesis.Approximation.Topological.A7Statements`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- A semi-simplicial subset of a finite semi-simplicial set is finite. -/
theorem isFinite_of_mono {A B : SemiSSet.{u}} (i : A ⟶ B) [Mono i] (hB : B.IsFinite) :
    A.IsFinite := by apply (config := {allowSynthFailures := true}) @_root_.HomotopyHypothesis.Approximation.FiniteRealization.isFinite_of_mono_proof <;> assumption
