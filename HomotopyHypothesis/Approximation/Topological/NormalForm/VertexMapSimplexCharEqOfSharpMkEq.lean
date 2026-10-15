import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.NormalForms.NormalForm
import HomotopyHypothesis.Approximation.Topological.Complex

/-!
# `vertexMap_simplexChar_eq_of_sharpMk_eq`

One declaration of `HomotopyHypothesis.Approximation.Topological.NormalForm`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- **Representatives of the same simplex realize to the same map** (frozen helper statement;
the realization of `X♯`-simplices is well defined). -/
theorem vertexMap_simplexChar_eq_of_sharpMk_eq {X : SemiSSet.{u}} {n m m' : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (x : stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ X)
    (v' : Fin (n + 1) → Fin (m' + 1)) (x' : stdSimplex.obj (Henry.SemiSimplexCategory.mk m') ⟶ X)
    (h : sharpMk v (uliftYonedaEquiv x) = sharpMk v' (uliftYonedaEquiv x')) :
    vertexMap v ≫ simplexChar x = vertexMap v' ≫ simplexChar x' := by apply @_root_.HomotopyHypothesis.Simplicial.NormalForms.vertexMap_simplexChar_eq_of_sharpMk_eq_proof <;> assumption
