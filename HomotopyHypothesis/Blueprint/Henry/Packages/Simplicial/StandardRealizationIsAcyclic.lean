import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Realization.SemisimplicialComparison.Acyclic

/-!
# `standardRealization_isAcyclic`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

/-- H Thm 5.2.10 (H:2986–2991): a standard realization `C^Δ ⥤ FinCell` is acyclic (homotopy
surjectivity by induction on the cells of a finite cell complex, attaching maps being homotopic to
realized cell boundaries by `standardRealization_isHomotopyFullyFaithful`). -/
theorem standardRealization_isAcyclic {R : CDelta.{u} ⥤ TopCat.{u}}
    (hR : IsStandardRealization R) : IsAcyclic hR.isCellularRealization.toFinCell := by apply @_root_.HomotopyHypothesis.Realization.SemisimplicialComparison.standardRealization_isAcyclic_proof <;> assumption
