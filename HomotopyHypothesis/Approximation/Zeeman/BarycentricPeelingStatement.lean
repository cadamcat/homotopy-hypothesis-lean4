import Mathlib.Basic.Real.Basic
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
/-!
# Barycentric decomposition towards the boundary

Every point of a finite standard simplex is its barycentre or a convex
combination of that barycentre with a boundary point. The coordinate
formulation allows the boundary point to be factored through its support.
-/

open Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

/-- Peeling off a uniform part of a probability distribution reaches the boundary. -/
def BarycentricPeelingStatement : Prop :=
  ∀ (n : ℕ) (t : StdSimplex ℝ (Fin (n + 1))),
    t = StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1)) ∨
      ∃ (c : ℝ) (q : StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)),
        0 ≤ c ∧ c < 1 ∧ q.weights i = 0 ∧
          ∀ j, t.weights j =
            c * (StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))).weights j +
              (1 - c) * q.weights j

end HomotopyHypothesis.Approximation.Zeeman
