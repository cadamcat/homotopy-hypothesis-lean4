import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Category.CylinderCorollary.Closure

/-!
# `weakEquivalence_closure`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **Closure of weak equivalences** (OA:01:363–392, Lemma `weak-closure`): isomorphisms are
weak equivalences, and weak equivalences are closed under composition. -/
theorem weakEquivalence_closure {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    MorphismProperty.isomorphisms C.Model ≤ W hC ∧ (W hC).IsMultiplicative := _root_.HomotopyHypothesis.Blueprint.Packages.weakEquivalence_closure_proof ..
