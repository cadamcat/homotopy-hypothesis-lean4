import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Code
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV

/-!
# `rank`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrism`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

namespace PV

variable {k : ℕ}

/-- The order of the vertices: top first, then middle by increasing size. -/
def rank : PV k → ℕ ×ₗ ℕ ×ₗ ℕ
  | top i => toLex (0, toLex (0, (i : ℕ)))
  | mid S => toLex (1, toLex (S.card, DV.code S))
