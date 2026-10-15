import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.GlobalStars
import HomotopyHypothesis.Approximation.Zeeman.PointwiseCarrierHomotopyStatement
/-!
# Simplicial approximation from the vertex star condition

A global vertex map satisfying the star condition gives a coherent
simplicial approximation. It agrees with an already simplicial restriction,
and common pointwise carriers supply the relative straight-line homotopy.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The star condition gives simplicial approximation relative to a simplicial subcomplex. -/
def VertexStarApproximationStatement : Prop :=
  PointwiseCarrierHomotopyStatement.{u} →
    ∀ {W M : SemiSSet.{u}}, M.IsFinite → M.IsSimplicialComplex →
      ∀ (F : realization.obj W ⟶ realization.obj M)
        (q : W.obj (op (Henry.SemiSimplexCategory.mk 0)) →
          M.obj (op (Henry.SemiSimplexCategory.mk 0))),
        IsVertexStarMap F q → ∀ (J : Subfunctor W),
          IsSimplicial (realization.map J.ι ≫ F) →
            ∃ g : realization.obj W ⟶ realization.obj M,
              IsSimplicial g ∧ realization.map J.ι ≫ g = realization.map J.ι ≫ F ∧
                g.hom.HomotopicRel F.hom (Set.range (realization.map J.ι).hom)

end HomotopyHypothesis.Approximation.Zeeman
