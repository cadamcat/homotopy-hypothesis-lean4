import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.FiniteCategory.UnitPresentation.Limit
import HomotopyHypothesis.FiniteCategory.UnitWeakEquivalence.Presentation
/-!
# The unit of the finite-cell restriction adjunction

Single-cell presentations and compact support imply that the adjunction unit is a
weak equivalence at every cofibrant object of the completion of finite cell complexes.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

/-- The adjunction unit is a weak equivalence at cofibrant objects. -/
theorem finCellRestriction_unit_weakEquivalence_proof
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    {L : Completion.{u} FinCell.{u} ⥤ TopCat.{u}} (adj : L ⊣ topRestriction hι)
    (X : Completion.{u} FinCell.{u})
    (hX : IsCofibrantFor (Completion.cofibrations FinCell.{u}) X) :
    Completion.weakEquivalences FinCell.{u} (adj.unit.app X) :=
  FiniteCategory.UnitPresentation.unit_weakEquivalence_of_singleCellPresentation hι adj
    FiniteCategory.UnitWeakEquivalence.singleCellPresentation X hX

end HomotopyHypothesis.Henry.Packages
