import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.LocalAffine
import HomotopyHypothesis.Approximation.Zeeman.LocalEmbedding
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeRealization
/-!
# Linear factorization of the relative derived realization map

Each characteristic map of the relative derived subdivision factors through
an original simplex by a linear embedding. This is the linearity condition
for a relative subdivision, prior to identifying its realization map as an
isomorphism.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The relative derived realization map is linear on every simplex. -/
theorem relativeRealizationMap_linear {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K)
    (n : ℕ) (y' : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶
      relativeDerived K L) :
    ∃ (m : ℕ) (y : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ K)
      (e : toTop.obj (Henry.SemiSimplexCategory.mk n) ⟶
        toTop.obj (Henry.SemiSimplexCategory.mk m)),
      IsLinearEmbedding e ∧ simplexChar y' ≫ relativeRealizationMap hK L =
        e ≫ simplexChar y := by
  let a := uliftYonedaEquiv y'
  refine ⟨(leastRelativeCarrier hK a).1,
    uliftYonedaEquiv.symm (leastRelativeCarrier hK a).2,
    relativeLocalTopMap hK a, relativeLocalTopMap_isLinearEmbedding hK a, ?_⟩
  simpa only [a, Equiv.symm_apply_apply] using relativeRealizationMap_simplex hK a

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeRealizationMap_linear
