import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.FiniteCategory.Cylinder.Classical
universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.FiniteCategory.CellularRealization

open HomotopyHypothesis.Henry

/-- The inclusion of finite cell complexes is a cellular realization. -/
theorem isCellularRealization_finCellι_proof :
    IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X
    exact X.property
  · intro X Y f hf
    exact hf
  · intro X Y f hf
    exact hf
  · intro I hI
    exact ⟨HomotopyHypothesis.FiniteCategory.Cylinder.finCell_topImage_initial hI⟩
  · intro A B X P i f k j h hi
    let J : FinCell.{u} ⥤ TopCat.{u} := ObjectProperty.ι Top.IsFiniteCellComplex.{u}
    letI : CreatesColimit (span i f) J :=
      HomotopyHypothesis.FiniteCategory.Cylinder.finCell_createsPushout i f hi
    letI : PreservesColimit (span i f) J := inferInstance
    exact h.map J

end HomotopyHypothesis.FiniteCategory.CellularRealization

#print axioms HomotopyHypothesis.FiniteCategory.CellularRealization.isCellularRealization_finCellι_proof
