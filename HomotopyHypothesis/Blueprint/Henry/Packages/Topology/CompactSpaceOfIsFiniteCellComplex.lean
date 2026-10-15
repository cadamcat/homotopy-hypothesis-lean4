import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.CellComplex.Basic.Proofs

/-!
# `compactSpace_of_isFiniteCellComplex`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Topology`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat

namespace HomotopyHypothesis.Henry.Packages

/-- A finite cell complex is compact (induction on the cells: a pushout of compact spaces along
`∂𝔻 n ⟶ 𝔻 n` is compact, being the image of a compact space). -/
theorem compactSpace_of_isFiniteCellComplex {X : TopCat.{u}} (hX : Top.IsFiniteCellComplex X) :
    CompactSpace X := by apply @_root_.HomotopyHypothesis.CellComplex.Basic.compactSpace_of_isFiniteCellComplex_proof <;> assumption
