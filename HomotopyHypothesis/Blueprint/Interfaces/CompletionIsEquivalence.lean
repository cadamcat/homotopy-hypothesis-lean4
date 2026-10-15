import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Interfaces.Restriction
import HomotopyHypothesis.Completion.FinitelyCellular.Equiv

/-!
# `completion_isEquivalence`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **The completion of `A_fin` is the category of models** (H:3091–3108, Prop. 5.3.7; gap
review B §1.3: every finitely cellular model is an iterated pushout of globular sums along
cofibrations, so restriction is an equivalence onto presheaves sending cofibration pushouts to
pullbacks). -/
theorem completion_isEquivalence {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    (restriction hC).IsEquivalence := _root_.HomotopyHypothesis.Completion.FinitelyCellular.completion_isEquivalence_proof ..
