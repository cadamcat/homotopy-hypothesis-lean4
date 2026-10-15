import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.ComplexTopology.ComplexRealizationTopology
import HomotopyHypothesis.Approximation.Zeeman.RelativeLinear
/-!
# Straight-line homotopies in common simplex carriers

Two continuous maps into a finite complex are homotopic when, on every
source simplex, both maps take values in a common target simplex. The
straight-line homotopy fixes any subset on which the maps agree.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A relative straight-line homotopy from common simplex carriers. -/
def CarrierHomotopyStatement : Prop :=
  ∀ {W K : SemiSSet.{u}}, K.IsFinite → K.IsSimplicialComplex →
    ∀ (f g : realization.obj W ⟶ realization.obj K) (A : Set (realization.obj W)),
      (∀ z ∈ A, f.hom z = g.hom z) →
      (∀ (n : ℕ) (y : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ W),
        ∃ (m : ℕ) (x : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ K)
          (e₀ e₁ : toTop.obj (Henry.SemiSimplexCategory.mk n) ⟶
            toTop.obj (Henry.SemiSimplexCategory.mk m)),
          simplexChar y ≫ f = e₀ ≫ simplexChar x ∧
            simplexChar y ≫ g = e₁ ≫ simplexChar x) →
      f.hom.HomotopicRel g.hom A

end HomotopyHypothesis.Approximation.Zeeman
