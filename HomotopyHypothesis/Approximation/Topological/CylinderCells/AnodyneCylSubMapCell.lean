import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.CylinderCellProof.Part2
import HomotopyHypothesis.Approximation.Topological.CylinderCells.CylSub
import HomotopyHypothesis.Approximation.Topological.CylinderCells.CylSubMap
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder

/-!
# `anodyne_cylSubMap_cell`

One declaration of `HomotopyHypothesis.Approximation.Topological.CylinderCells`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

variable {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)

/-- **Attaching one cell** (frozen helper statement). If `A'` is obtained from `A` by adding one
`n`-simplex `y` of `W` whose proper faces lie in `A`, the glued cylinder over `A'` is the pushout of
the one over `A` along the boundary of the derived double cylinder of `y`
(`dcylDBoundaryι`), hence collapses onto it (`anodyne_dcylDBoundaryι`, `anodyne_of_isPushout`).
The boundary map sends the cylinder over a proper face `θ` of `y` to the cylinder of `W.map θ y`
and the bottom to `X`; it is well defined because cylinders over two faces of the derived double
cylinder meet in the cylinder over their intersection. -/
theorem anodyne_cylSubMap_cell {A A' : Subfunctor W} (h : A ≤ A') (n : ℕ)
    (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hyA : y ∉ A.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hyA' : y ∈ A'.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hfaces : ∀ (k : ℕ) (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n),
      k ≠ n → W.map θ.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)))
    (hA' : ∀ (k : ℕ) (z : W.obj (op (Henry.SemiSimplexCategory.mk k))),
      z ∈ A'.obj (op (Henry.SemiSimplexCategory.mk k)) →
        z ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)) ∨ ∃ hk : k = n, hk ▸ z = y) :
    anodyne (cylSubMap φ h) := by apply @_root_.HomotopyHypothesis.Approximation.Topological.anodyne_cylSubMap_cell_proof <;> assumption
