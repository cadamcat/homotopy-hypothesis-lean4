import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.FiniteRealization.Proofs

/-!
# `isFinite_of_finite_obj`

One declaration of `HomotopyHypothesis.Approximation.Topological.A7Statements`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- A semi-simplicial subset with finitely many simplices, none above some dimension, is finite. -/
theorem isFinite_of_finite_obj {B : SemiSSet.{u}} (S : Subfunctor B)
    (h₁ : ∀ n : ℕ, (S.obj (op (Henry.SemiSimplexCategory.mk n))).Finite)
    (h₂ : ∃ N : ℕ, ∀ n : ℕ, N < n → S.obj (op (Henry.SemiSimplexCategory.mk n)) = ∅) :
    SemiSSet.IsFinite S.toFunctor := by apply @_root_.HomotopyHypothesis.Approximation.FiniteRealization.isFinite_of_finite_obj_proof <;> assumption
