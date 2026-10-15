import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderCells.ElFaceHom
import HomotopyHypothesis.Approximation.Topological.CylinderCells.ElOf
import HomotopyHypothesis.Approximation.Topological.CylinderCells.FaceBdryGen
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundaryComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder
import HomotopyHypothesis.Approximation.Topological.NormalForm.NF

/-!
# `faceBdry`

One declaration of `HomotopyHypothesis.Approximation.Topological.CylinderCells`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

variable {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)

/-- The cylinder over the face of `y` along `θ`, mapped into the boundary of the cylinder of
`y`. -/
noncomputable abbrev faceBdry {n k : ℕ} (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n) (hk : k ≠ n) :
    (dcylDComplex (elNF φ (elOf (W.map θ.op y))).v).Hom
      (dcylDBoundaryComplex (elNF φ (elOf y)).v) :=
  faceBdryGen φ y (elFaceHom y θ) hk
