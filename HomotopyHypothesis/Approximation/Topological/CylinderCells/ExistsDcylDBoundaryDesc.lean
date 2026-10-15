import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Cylinder.BoundaryDescription.BoundaryDesc
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderCells.BotBdry
import HomotopyHypothesis.Approximation.Topological.CylinderCells.CylSub
import HomotopyHypothesis.Approximation.Topological.CylinderCells.ElOf
import HomotopyHypothesis.Approximation.Topological.CylinderCells.FaceBdryGen
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundary
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundaryComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder
import HomotopyHypothesis.Approximation.Topological.NormalForm.NF

/-!
# `exists_dcylDBoundary_desc`

One declaration of `HomotopyHypothesis.Approximation.Topological.CylinderCells`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

variable {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)

/-- **The boundary of the cylinder of a cell maps to the glued cylinder over its faces** (frozen
helper statement). If all proper faces of `y` lie in `A`, there is a map from the boundary of the
derived double cylinder of `y` to the glued cylinder over `A`, equal on the cylinder over each
proper face `e` of `y` (any element of `A` with a morphism from `y`) to that cylinder's inclusion and on the bottom to the carrier of `y` followed by the
inclusion of `X`. (Each non-bottom simplex of the boundary has a least face of `Δ_n` carrying it,
the largest middle vertex or else its top face; send it through the cylinder of that face.) -/
theorem exists_dcylDBoundary_desc (A : Subfunctor W) {n : ℕ}
    (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hfaces : ∀ (k : ℕ) (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n),
      k ≠ n → W.map θ.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk k))) :
    ∃ κ : dcylDBoundary.{u} (elNF φ (elOf y)).v ⟶ (cylSub φ A).obj,
      (∀ (e : A.toFunctor.Elements) (f : elOf y ⟶ W.elementsMk e.obj e.val.1)
        (hk : elDim (W.elementsMk e.obj e.val.1) ≠ n),
        (faceBdryGen φ y f hk).toSemiSSet ≫ κ =
          colimit.ι (cylSub φ A).DC (op e) ≫ (cylSub φ A).incl) ∧
      botBdry (elNF φ (elOf y)).v ≫ κ =
        uliftYonedaEquiv.symm (elNF φ (elOf y)).x ≫ (cylSub φ A).base := by apply @_root_.HomotopyHypothesis.Cylinder.BoundaryDescription.exists_dcylDBoundary_desc_proof <;> assumption
