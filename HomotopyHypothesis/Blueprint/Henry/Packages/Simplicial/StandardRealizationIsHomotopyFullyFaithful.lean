import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Realization.SemisimplicialComparison.FullyFaithful

/-!
# `standardRealization_isHomotopyFullyFaithful`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

/-- H Prop 5.2.8 (H:2938–2953): a standard realization is homotopy fully faithful (induction over
the cells of a cofibration from `standardRealization_relative_cells`, proved in
`Blueprint/Henry/RelativeCells.lean`, using homotopy extension for relative finite cell
complexes, `relativeFiniteCellComplex_homotopyExtension`). -/
theorem standardRealization_isHomotopyFullyFaithful {R : CDelta.{u} ⥤ TopCat.{u}}
    (hR : IsStandardRealization R) :
    IsHomotopyFullyFaithful hR.isCellularRealization.toFinCell := by apply @_root_.HomotopyHypothesis.Realization.SemisimplicialComparison.standardRealization_isHomotopyFullyFaithful_proof <;> assumption
