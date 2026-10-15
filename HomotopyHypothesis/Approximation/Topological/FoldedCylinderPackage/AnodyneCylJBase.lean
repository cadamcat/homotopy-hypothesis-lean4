import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Cylinder.AnodyneCells.Proofs
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder

/-!
# `anodyne_cylJ_base`

One declaration of `HomotopyHypothesis.Approximation.Topological.FoldedCylinderPackage`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- **The glued cylinder over a subobject collapses onto its base** (frozen helper statement).
Built from `X` by attaching, cell by cell over the finite semi-simplicial set `J`, derived double
cylinders along their boundaries (`anodyne_dcylDBoundaryι`; the cylinders over two faces meet in
the cylinder over their intersection, so each attachment is a pushout of the boundary inclusion). -/
theorem anodyne_cylJ_base {X W J : SemiSSet.{u}} (hW : W.IsFinite) (j : J ⟶ W) [Mono j]
    (φ : W ⟶ sharp X) : anodyne (cylJ j φ).base := by apply @_root_.HomotopyHypothesis.Cylinder.AnodyneCells.anodyne_cylJ_base_proof <;> assumption
