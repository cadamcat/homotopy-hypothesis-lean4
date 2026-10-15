import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder

/-!
# `elOf`

One declaration of `HomotopyHypothesis.Approximation.Topological.CylinderCells`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

variable {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)

/-- The simplex `y` as an element of `W`. -/
abbrev elOf {n : ℕ} (y : W.obj (op (Henry.SemiSimplexCategory.mk n))) : W.Elements :=
  W.elementsMk _ y
