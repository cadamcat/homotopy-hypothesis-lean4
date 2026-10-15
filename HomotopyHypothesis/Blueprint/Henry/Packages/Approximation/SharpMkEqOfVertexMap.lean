import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.PointStructure.RealizationPoints

/-!
# `sharpMk_eq_of_vertexMap`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Approximation`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Henry.Packages

open SemiSSet

/-- **Formal degeneracies are detected by their realizations.** If two vertex maps into simplices
of `X` give the same map `|Δ^n| ⟶ ‖X‖`, they represent the same simplex of `X♯`. (Each point of
`‖X‖` lies in the open cell of a unique simplex and the characteristic map of a simplex is injective
on its interior; the minimal representative, with surjective vertex map, of a simplex of `X♯` is
therefore determined by the map.) -/
theorem sharpMk_eq_of_vertexMap {X : SemiSSet.{u}} {n m m' : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (x : stdSimplex.obj (SemiSimplexCategory.mk m) ⟶ X) (v' : Fin (n + 1) → Fin (m' + 1))
    (x' : stdSimplex.obj (SemiSimplexCategory.mk m') ⟶ X)
    (h : vertexMap v ≫ simplexChar x = vertexMap v' ≫ simplexChar x') :
    sharpMk v (uliftYonedaEquiv x) = sharpMk v' (uliftYonedaEquiv x') := by apply @_root_.HomotopyHypothesis.Henry.Packages.sharpMk_eq_of_vertexMap_proof <;> assumption
