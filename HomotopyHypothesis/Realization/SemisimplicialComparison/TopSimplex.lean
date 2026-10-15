import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
/-!
# Counting simplices

The number of simplices of bounded dimension of a semi-simplicial set, the measure for the
induction over the top simplices of semi-simplicial subsets of standard simplices.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Realization.SemisimplicialComparison

open HomotopyHypothesis.Henry

/-- The number of simplices of `T` of dimension at most `N`. -/
noncomputable def simplexCount (T : SemiSSet.{u}) (N : ℕ) : ℕ :=
  Nat.card (Σ p : Fin (N + 1), T.obj (op (Henry.SemiSimplexCategory.mk p)))

end HomotopyHypothesis.Realization.SemisimplicialComparison
