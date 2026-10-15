import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Code
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV

/-!
# `rank`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedCylinder`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

namespace DV

variable {n m : ℕ}

/-- The order of the vertices: middle by decreasing size, then top, then bottom (so that folding
the top onto the bottom along an increasing vertex map preserves the order). -/
def rank : DV n m → ℕ ×ₗ ℕ ×ₗ ℕ
  | mid S => toLex (0, toLex (n + 1 - S.card, code S))
  | top i => toLex (1, toLex (0, (i : ℕ)))
  | bot c => toLex (2, toLex (0, (c : ℕ)))
