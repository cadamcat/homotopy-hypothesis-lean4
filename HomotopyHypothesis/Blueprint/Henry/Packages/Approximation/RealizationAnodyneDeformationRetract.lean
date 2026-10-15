import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Anodyne.AnodyneDeformationRetract

/-!
# `realization_anodyne_deformationRetract`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Approximation`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Henry.Packages

open SemiSSet

/-- **Collapses realize to strong deformation retractions** (the finite case of
`realization_hornCells_deformationRetract`; the horn prism `(Λ^n_k × I) ∪ (Δ^n × ∂I) ⊆ Δ^n × I`
is a retract). For an anodyne `j : A ⟶ B`, `‖j‖` has a retraction `r` with `r ≫ ‖j‖` homotopic
to the identity relative to `‖A‖`. -/
theorem realization_anodyne_deformationRetract {A B : SemiSSet.{u}} (j : A ⟶ B)
    (hj : anodyne j) :
    ∃ r : realization.obj B ⟶ realization.obj A, realization.map j ≫ r = 𝟙 _ ∧
      (r ≫ realization.map j).hom.HomotopicRel (ContinuousMap.id _)
        (Set.range (realization.map j).hom) := by apply @_root_.HomotopyHypothesis.Approximation.Anodyne.realization_anodyne_deformationRetract_proof <;> assumption
