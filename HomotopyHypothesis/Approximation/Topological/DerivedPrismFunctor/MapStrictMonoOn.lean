import HomotopyHypothesis.Approximation.DerivedPrismNaturality.Proofs.Part1
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map

/-!
# `map_strictMonoOn`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

/-- A strictly increasing vertex map is strictly increasing on the simplices of the derived
cylinder. Frozen helper statement. -/
theorem map_strictMonoOn {t : Fin (k + 1) → Fin (l + 1)} (ht : StrictMono t) (A : Finset (PV k))
    (hA : (dprismComplex k).S A) : StrictMonoOn (map t) A := by apply (config := {allowSynthFailures := true}) @_root_.HomotopyHypothesis.Approximation.DerivedPrismNaturality.map_strictMonoOn_proof <;> assumption
