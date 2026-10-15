import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.CellComplex.Basic.Proofs

/-!
# `finCell_essentiallySmall`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Topology`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat

namespace HomotopyHypothesis.Henry.Packages

/-- Finite cell complexes form an essentially small category: a finite cell complex is determined
up to homeomorphism by a finite sequence of attaching data `(n, ∂𝔻 n ⟶ X_k)`, and these codes form
a type in the universe of the spaces. -/
theorem finCell_essentiallySmall : EssentiallySmall.{u} FinCell.{u} := @_root_.HomotopyHypothesis.CellComplex.Basic.finCell_essentiallySmall_proof
