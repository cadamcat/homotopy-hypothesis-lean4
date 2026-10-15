import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.PrismGluing.Proofs
import HomotopyHypothesis.Simplicial.BarycentricSubdivision.DerivedSubdivision
import HomotopyHypothesis.Approximation.Topological.CylinderGlue

/-!
# `isSimplicialComplex_of_iso`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- Isomorphic semi-simplicial sets are ordered simplicial complexes together. Frozen helper
statement. -/
theorem isSimplicialComplex_of_iso {A B : SemiSSet.{u}} (e : A ≅ B) (hB : B.IsSimplicialComplex) :
    A.IsSimplicialComplex := by apply (config := {allowSynthFailures := true}) @_root_.HomotopyHypothesis.Approximation.PrismGluing.isSimplicialComplex_of_iso_proof <;> assumption
