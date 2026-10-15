import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.CarrierHomotopyStatement
/-!
# Pointwise straight-line carrier homotopies

A common target simplex for the two images of each point suffices for
a straight-line homotopy. The carrier may vary with the point, as is
needed for simplicial approximations of nonlinear continuous maps.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Pointwise common carriers give a relative homotopy into a finite complex. -/
def PointwiseCarrierHomotopyStatement : Prop :=
  ∀ {W K : SemiSSet.{u}}, K.IsFinite → K.IsSimplicialComplex →
    ∀ (f g : realization.obj W ⟶ realization.obj K) (A : Set (realization.obj W)),
      (∀ z ∈ A, f.hom z = g.hom z) →
      (∀ z : realization.obj W,
        ∃ (m : ℕ) (x : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ K)
          (p q : toTop.obj (Henry.SemiSimplexCategory.mk m)),
          f.hom z = (simplexChar x).hom p ∧ g.hom z = (simplexChar x).hom q) →
      f.hom.HomotopicRel g.hom A

end HomotopyHypothesis.Approximation.Zeeman
