import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.Cellular.EndpointLifting
import HomotopyHypothesis.Horn.DeformationRetraction.HornLifting
import HomotopyHypothesis.Horn.DeformationRetraction.Lifting
/-!
# Deformation retraction of realized relative horn complexes

The horn and horn-prism retractions imply lifting against maps to a point and path endpoint
evaluation. The realization adjunction and transfinite lifting closure extend these properties
from horns to arbitrary relative horn complexes.
-/

universe u

open CategoryTheory Limits
open HomotopyHypothesis.Henry HomotopyHypothesis.Horn.DeformationRetraction

namespace HomotopyHypothesis.Henry.Packages

/-- Realization takes a relative horn complex to a strong deformation retract. -/
theorem realization_hornCells_deformationRetract_proof {A B : SemiSSet.{u}} (j : A ⟶ B)
    (hj : MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} (MorphismProperty.ofHoms (fun p : Σ n : ℕ, Fin (n + 2) =>
        (SemiSSet.horn.{u} (p.1 + 1) p.2).ι))).pushouts j) :
    ∃ r : SemiSSet.realization.obj B ⟶ SemiSSet.realization.obj A,
      SemiSSet.realization.map j ≫ r = 𝟙 _ ∧
        (r ≫ SemiSSet.realization.map j).hom.HomotopicRel (ContinuousMap.id _)
          (Set.range (SemiSSet.realization.map j).hom) := by
  apply deformationRetract_of_lifting
  · intro Z
    exact realization_hornCells_hasLiftingProperty (terminal.from Z)
      (realization_horn_hasLiftingProperty_terminal Z) j hj
  · intro Z
    exact realization_hornCells_hasLiftingProperty (Realization.Cellular.pathEndpoints Z)
      (realization_horn_hasLiftingProperty_endpoints Z) j hj

#print axioms realization_hornCells_deformationRetract_proof

end HomotopyHypothesis.Henry.Packages
