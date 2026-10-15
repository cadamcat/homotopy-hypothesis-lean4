import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.SemisimplicialComparison.TopSimplex
/-!
# Faces and generalized horns of a standard simplex

For a set `V` of vertices of `Δ_N`, `faceSub V` is the face spanned by `V` (the simplices whose
vertices lie in `V`), and for `J ⊆ V`, `hornSub V J` is the union of the faces `V ∖ {j}`,
`j ∈ J`. The horn `Λ^{n+1}_k` is `hornSub univ (univ ∖ {k})`.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Realization.SemisimplicialComparison

open HomotopyHypothesis.Henry

variable {N : ℕ}

/-- The face of `Δ_N` spanned by a set `V` of vertices. -/
def faceSub (V : Finset (Fin (N + 1))) :
    Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)) where
  obj _ f := ∀ x, (ULift.down f).hom.toOrderHom x ∈ V
  map _ _ := by
    intro hf x
    exact hf _

/-- The union of the faces `V ∖ {j}` of `Δ_N`, `j ∈ J`. -/
def hornSub (V J : Finset (Fin (N + 1))) :
    Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)) where
  obj _ f := ∃ j ∈ J, ∀ x, (ULift.down f).hom.toOrderHom x ∈ V.erase j
  map _ _ := by
    rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, fun x => hf _⟩

end HomotopyHypothesis.Realization.SemisimplicialComparison
