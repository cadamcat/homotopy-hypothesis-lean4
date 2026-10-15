import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.FiniteCategory.Subcategory.CompletionWeakEquivalencesRespectsIso

/-!
# `completion_weakEquivalences_respectsIso`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- Weak equivalences of the completion are invariant under isomorphism of arrows. -/
theorem completion_weakEquivalences_respectsIso {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    (Completion.weakEquivalences.{u} (Afin C hC)).RespectsIso := _root_.HomotopyHypothesis.FiniteCategory.Subcategory.completion_weakEquivalences_respectsIso_proof ..
