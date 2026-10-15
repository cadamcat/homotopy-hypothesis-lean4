import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Cylinder.AnodyneCells.Proofs
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder

/-!
# `anodyne_cyl_restrictMap`

One declaration of `HomotopyHypothesis.Approximation.Topological.FoldedCylinderPackage`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- **The glued cylinder over `W` collapses onto the one over a subobject `J`** (frozen helper
statement; same argument, over the cells of `W` not in `J`). -/
theorem anodyne_cyl_restrictMap {X W J : SemiSSet.{u}} (hW : W.IsFinite) (j : J ⟶ W) [Mono j]
    (φ : W ⟶ sharp X) : anodyne ((cylDatum φ).restrictMap (elMap j)) := by apply @_root_.HomotopyHypothesis.Cylinder.AnodyneCells.anodyne_cyl_restrictMap_proof <;> assumption
