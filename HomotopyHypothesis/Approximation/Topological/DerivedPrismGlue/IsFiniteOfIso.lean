import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.PrismGluing.Proofs
import HomotopyHypothesis.Simplicial.BarycentricSubdivision.DerivedSubdivision
import HomotopyHypothesis.Approximation.Topological.CylinderGlue

/-!
# `isFinite_of_iso`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- Isomorphic semi-simplicial sets are finite together. Frozen helper statement. -/
theorem isFinite_of_iso {A B : SemiSSet.{u}} (e : A ≅ B) (hB : B.IsFinite) : A.IsFinite := by apply (config := {allowSynthFailures := true}) @_root_.HomotopyHypothesis.Approximation.PrismGluing.isFinite_of_iso_proof <;> assumption
