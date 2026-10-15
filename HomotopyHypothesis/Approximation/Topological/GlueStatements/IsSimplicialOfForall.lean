import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Gluing.Simplicial.Glue

/-!
# `isSimplicial_of_forall`

One declaration of `HomotopyHypothesis.Approximation.Topological.GlueStatements`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- A map of realizations which on every simplex is the affine extension of a vertex map into a
simplex of the target is simplicial (the coherent choice of formal degeneracies is forced by
`sharpMk_eq_of_vertexMap`). -/
theorem isSimplicial_of_forall {Y X : SemiSSet.{u}} (f : realization.obj Y ⟶ realization.obj X)
    (hf : ∀ (n : ℕ) (y : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ Y),
      ∃ (m : ℕ) (x : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ X)
        (v : Fin (n + 1) → Fin (m + 1)), simplexChar y ≫ f = vertexMap v ≫ simplexChar x) :
    IsSimplicial f := by apply @_root_.HomotopyHypothesis.Gluing.Simplicial.isSimplicial_of_forall_proof <;> assumption
