import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.FiniteCategory.Comparison.AfinFunctorComparison
import HomotopyHypothesis.Adjunction.FrameBoundary.FrameBoundaryAdjoint
import HomotopyHypothesis.FiniteCategory.Lifting.ConditionalPackages
import HomotopyHypothesis.FiniteCategory.Lifting.EndomorphismTheory
import HomotopyHypothesis.FiniteCategory.Lifting.FillerLift
import HomotopyHypothesis.FiniteCategory.Lifting.ModelShapes
/-!
# Realization inputs for pointed lifting

Framed interpretations have boundary adjoints, and representable comparisons extend to exact
functors on finite cellular objects.
-/

universe u

open CategoryTheory HomotopicalAlgebra
open OAI.Grothendieck HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

/-- Every framed interpretation has the required boundary adjoints. -/
theorem boundaryAdjointFamily_proof (C : GlobularTheory.{u}) : BoundaryAdjointFamily C := by
  intro X _ _ _ R F a
  exact Adjunction.FrameBoundary.frameBoundaryAdjointStatement_proof R F a

/-- Every representable comparison of exact finite-cell functors extends with its components. -/
theorem afinFunctorComparisonFamily_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    AfinFunctorComparisonFamily hC := by
  intro Y _ _ _ F G hF hG e
  exact FiniteCategory.Comparison.afinFunctorComparisonStatement_proof hC F G hF hG e

#print axioms boundaryAdjointFamily_proof
#print axioms afinFunctorComparisonFamily_proof

end HomotopyHypothesis.FiniteCategory.Lifting
