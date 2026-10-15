import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.SemisimplicialComparison.Standard

/-!
# `exists_standardRealization`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

/-- H Def 5.2.5 (H:2880): a standard realization of `C^Δ` exists: send `Δ_n` to the topological
simplex and each freely added horn filler to a chosen retraction `|Δ^n| ⟶ |Λ^n_k|` (any such
retraction is cellular, H:2876), extending along cell attachments by the universal property of the
free construction. -/
theorem exists_standardRealization : ∃ R : CDelta.{u} ⥤ TopCat.{u}, IsStandardRealization R :=
  @_root_.HomotopyHypothesis.Realization.SemisimplicialComparison.exists_standardRealization_proof
