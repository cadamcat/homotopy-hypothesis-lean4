import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Faces
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
/-!
# Coherence of a global vertex map

Local affine vertex maps into a simplicial complex are coherent when they
have the same global map on raw vertices. Their simplex representatives
then define a map into the formal degeneracies of the target.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A global vertex map and compatible affine simplex formulas give a coherent simplicial map. -/
def SimplicialVertexMapStatement : Prop :=
  ∀ {W K : SemiSSet.{u}}, K.IsSimplicialComplex →
    ∀ (F : realization.obj W ⟶ realization.obj K)
      (q : W.obj (op (Henry.SemiSimplexCategory.mk 0)) →
        K.obj (op (Henry.SemiSimplexCategory.mk 0))),
      (∀ (n : ℕ) (y : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ W),
        ∃ (m : ℕ) (x : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ K)
          (v : Fin (n + 1) → Fin (m + 1)),
          (∀ i, vertex (uliftYonedaEquiv x) (v i) = q (vertex (uliftYonedaEquiv y) i)) ∧
            simplexChar y ≫ F = vertexMap v ≫ simplexChar x) →
      IsSimplicial F

end HomotopyHypothesis.Approximation.Zeeman
