import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Gluing.Simplicial.Glue

/-!
# `pushout_simplex_cases`

One declaration of `HomotopyHypothesis.Approximation.Topological.GlueStatements`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- Every simplex of a pushout of semi-simplicial sets comes from one of the two sides. -/
theorem pushout_simplex_cases {A B C D : SemiSSet.{u}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D}
    {k : C ⟶ D} (sq : IsPushout f g h k) (n : ℕ)
    (d : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ D) :
    (∃ b, b ≫ h = d) ∨ ∃ c, c ≫ k = d := by apply @_root_.HomotopyHypothesis.Gluing.Simplicial.pushout_simplex_cases_proof <;> assumption
