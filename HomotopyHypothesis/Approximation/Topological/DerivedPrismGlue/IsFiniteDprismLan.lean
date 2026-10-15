import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.PrismGluing.Proofs
import HomotopyHypothesis.Simplicial.BarycentricSubdivision.DerivedSubdivision
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan

/-!
# `isFinite_dprismLan`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- The derived cylinder of a finite semi-simplicial set is finite. Frozen helper statement. -/
theorem isFinite_dprismLan {W : SemiSSet.{u}} (hW : W.IsFinite) : (dprismLan.obj W).IsFinite :=
  by apply @_root_.HomotopyHypothesis.Approximation.PrismGluing.isFinite_dprismLan_proof <;> assumption
