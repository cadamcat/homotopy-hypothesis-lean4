import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.FiniteCategory.Subcategory.DiskFinitelyCellular

/-!
# `disk_finitelyCellular`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- Every disk is finitely cellular (`∂Dₙ₊₁ = Dₙ ⊔_{∂Dₙ} Dₙ`, OA:01:105–110). -/
theorem disk_finitelyCellular (C : GlobularTheory.{u}) (n : ℕ) :
    IsFinitelyCellular C (disk C n) := _root_.HomotopyHypothesis.FiniteCategory.Subcategory.disk_finitelyCellular_proof ..
