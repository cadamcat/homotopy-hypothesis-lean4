import HomotopyHypothesis.Approximation.DerivedPrismNaturality.Proofs.Part1
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map

/-!
# `map_S`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

/-- An injective vertex map sends simplices of the derived cylinder to simplices. Frozen helper
statement. -/
theorem map_S {t : Fin (k + 1) → Fin (l + 1)} (ht : StrictMono t) (A : Finset (PV k))
    (hA : (dprismComplex k).S A) : (dprismComplex l).S (A.image (map t)) := by apply (config := {allowSynthFailures := true}) @_root_.HomotopyHypothesis.Approximation.DerivedPrismNaturality.map_S_proof <;> assumption
