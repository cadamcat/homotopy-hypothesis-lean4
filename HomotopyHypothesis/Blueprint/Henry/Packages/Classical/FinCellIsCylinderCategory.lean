import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.FiniteCategory.Cylinder.Classical

/-!
# `finCell_isCylinderCategory`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Classical`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial

namespace HomotopyHypothesis.Henry.Packages

/-- Finite cell complexes, with relative finite cell complexes as cofibrations and homotopy
equivalences as weak equivalences, form a cylinder category (H:418, with finite cell complexes in
place of finite CW complexes): pushouts along relative finite cell complexes are computed in spaces,
cylinders `X × [0, 1]` are finite cell complexes, trivial cofibrations are strong deformation
retracts (homotopy extension property). -/
theorem finCell_isCylinderCategory : IsCylinderCategory FinCell.{u} := @_root_.HomotopyHypothesis.FiniteCategory.Cylinder.finCell_isCylinderCategory_proof
