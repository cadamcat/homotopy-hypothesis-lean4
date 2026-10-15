import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Realization.Boundary.RealizationBoundaryPackage

/-!
# `realization_boundary_relativeFiniteCellComplex`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Classical`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial

namespace HomotopyHypothesis.Henry.Packages

/-- The realized boundary inclusion `‖∂Δ_n‖ ⟶ ‖Δ_n‖` of semi-simplicial sets is a relative
finite cell complex between finite cell complexes: `‖∂Δ_n‖` is built from the realized faces by
the skeletal pushouts (one cell per simplex, Ebert–Randal-Williams, Example 1.6 and §1.2), and
`(‖Δ_n‖, ‖∂Δ_n‖) ≅ (𝔻 n, ∂𝔻 n)` (Hatcher, Example 0.3). Used to apply the homotopy extension
property to realized simplices. -/
theorem realization_boundary_relativeFiniteCellComplex (n : ℕ) :
    Top.relativeFiniteCellComplexes (SemiSSet.realization.{u}.map (SemiSSet.boundary.{u} n).ι) ∧
      Top.IsFiniteCellComplex (SemiSSet.realization.{u}.obj (SemiSSet.boundary.{u} n).toFunctor) :=
  _root_.HomotopyHypothesis.Realization.Boundary.realization_boundary_relativeFiniteCellComplex_proof ..
