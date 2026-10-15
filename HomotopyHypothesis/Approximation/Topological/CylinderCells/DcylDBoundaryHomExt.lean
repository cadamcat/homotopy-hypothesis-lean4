import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Cylinder.BoundaryExtension.BoundaryHomExt.Part1
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderCells.BotBdry
import HomotopyHypothesis.Approximation.Topological.CylinderCells.ElOf
import HomotopyHypothesis.Approximation.Topological.CylinderCells.FaceBdry
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundary
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundaryComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder
import HomotopyHypothesis.Approximation.Topological.NormalForm.NF

/-!
# `dcylDBoundary_hom_ext`

One declaration of `HomotopyHypothesis.Approximation.Topological.CylinderCells`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

variable {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)

end HomotopyHypothesis.Approximation.Topological

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

variable {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)

/-- **The boundary of a cell cylinder is covered by the face cylinders and the bottom** (frozen
helper statement): two maps out of the boundary agreeing on the cylinders over all proper faces
and on the bottom are equal. (Each boundary simplex is bottom-only or lies over a face `[n] ∖ {i}`;
pull it back as in `exists_dcylDBoundary_desc`.) -/
theorem dcylDBoundary_hom_ext {n : ℕ} (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    {Z : SemiSSet.{u}} (g₁ g₂ : dcylDBoundary.{u} (elNF φ (elOf y)).v ⟶ Z)
    (hface : ∀ (k : ℕ) (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n)
      (hk : k ≠ n), (faceBdry φ y θ hk).toSemiSSet ≫ g₁ = (faceBdry φ y θ hk).toSemiSSet ≫ g₂)
    (hbot : botBdry (elNF φ (elOf y)).v ≫ g₁ = botBdry (elNF φ (elOf y)).v ≫ g₂) :
    g₁ = g₂ := by apply (config := {allowSynthFailures := true}) @_root_.HomotopyHypothesis.Cylinder.BoundaryExtension.dcylDBoundary_hom_ext_proof <;> assumption
