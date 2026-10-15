import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.CylinderCells.CylSub
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder

/-!
# `cylSubMap`

One declaration of `HomotopyHypothesis.Approximation.Topological.CylinderCells`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

variable {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)

/-- The map between the glued cylinders over two nested semi-simplicial subsets. -/
noncomputable def cylSubMap {A A' : Subfunctor W} (h : A ≤ A') :
    (cylSub φ A).obj ⟶ (cylSub φ A').obj :=
  (cylSub φ A').restrictMap (elMap (Subfunctor.homOfLe h))
