import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV

/-!
# `map`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

/-- The vertex map induced by a map of vertices. -/
def map (t : Fin (k + 1) → Fin (l + 1)) : PV k → PV l
  | top i => top (t i)
  | mid S => mid (S.image t)
