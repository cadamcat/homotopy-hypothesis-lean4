import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Category.CylinderCorollary.Fibrant

/-!
# `fibrant`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **Every model is fibrant** (OA:04:116–119): the unit of a `j`-cell extends it along `J j`. -/
theorem fibrant {C : GlobularTheory.{u}} (hC : C.IsCoherator) (X : C.Model) :
    (MorphismProperty.ofHoms (fun n : ℕ => J C n)).rlp (terminal.from X) := by apply @_root_.HomotopyHypothesis.Blueprint.Packages.fibrant_proof <;> assumption
