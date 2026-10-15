import HomotopyHypothesis.Approximation.Topological.CylinderCells.CylSub
import HomotopyHypothesis.Approximation.Topological.CylinderCells.CylSubMap
import HomotopyHypothesis.Approximation.Topological.CylinderCells.AnodyneCylSubMapCell
import HomotopyHypothesis.Approximation.Topological.CylinderCells.ElOf
import HomotopyHypothesis.Approximation.Topological.CylinderCells.ElFaceHom
import HomotopyHypothesis.Approximation.Topological.CylinderCells.FaceBdryGen
import HomotopyHypothesis.Approximation.Topological.CylinderCells.FaceBdry
import HomotopyHypothesis.Approximation.Topological.CylinderCells.BotBdry
import HomotopyHypothesis.Approximation.Topological.CylinderCells.ExistsDcylDBoundaryDesc
import HomotopyHypothesis.Approximation.Topological.CylinderCells.DcylDBoundaryHomExt

/-!
# Cell structure of the glued cylinders

For a map `φ : W ⟶ X♯` and a semi-simplicial subset `A ⊆ W`, the glued cylinder over `A` is the
restriction of the glued cylinder over `W`. Adding one simplex `y` of `W` whose proper faces lie in
`A` attaches the derived double cylinder of `y` along its boundary (`anodyne_cylSubMap_cell`); by
induction, the cylinder over `A'` collapses onto the cylinder over `A ⊆ A'` when `W` is finite.
-/

/-! The declarations of this file that the development uses are in the modules `HomotopyHypothesis.Approximation.Topological.CylinderCells.*`, one declaration per module. -/
