import HomotopyHypothesis.Approximation.Zeeman.Positions
/-!
# Contraction between averages of nested faces

For scalar values in an interval, the average over a nonempty face differs
from the average over its containing simplex by at most the simplex
dimension divided by its number of vertices, times the interval length.
This is the coordinate estimate for barycentric mesh contraction.
-/

open scoped BigOperators

namespace HomotopyHypothesis.Approximation.Zeeman

/-- The scalar contraction estimate for barycentres of nested nonempty faces. -/
def FiniteAverageContractionStatement : Prop :=
  ∀ (n m : ℕ) (e : Fin (m + 1) ↪ Fin (n + 1))
    (x : Fin (n + 1) → ℝ) (a b : ℝ),
    (∀ i, a ≤ x i ∧ x i ≤ b) →
      |(∑ j : Fin (m + 1), x (e j)) / ((m : ℝ) + 1) -
        (∑ i : Fin (n + 1), x i) / ((n : ℝ) + 1)| ≤
          (n : ℝ) / ((n : ℝ) + 1) * (b - a)

end HomotopyHypothesis.Approximation.Zeeman
