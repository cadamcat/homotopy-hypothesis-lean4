import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.CellComplex.Basic.DiskBoundary

/-!
# `diskBoundary_isFiniteCellComplex`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Topology`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat

namespace HomotopyHypothesis.Henry.Packages

/-- The boundary sphere `∂𝔻 n` is a finite cell complex: it is empty for `n = 0`, and for `n ≥ 1`
it is obtained from `∂𝔻 (n - 1)` by attaching the two hemispheres, i.e. two cells of dimension
`n - 1` along the equator (Hatcher, Example 0.3; Ara, Example 1.5.2 for the hemisphere maps). -/
theorem diskBoundary_isFiniteCellComplex (n : ℕ) :
    Top.IsFiniteCellComplex (diskBoundary.{u} n) := _root_.HomotopyHypothesis.CellComplex.Basic.diskBoundary_isFiniteCellComplex_proof ..
