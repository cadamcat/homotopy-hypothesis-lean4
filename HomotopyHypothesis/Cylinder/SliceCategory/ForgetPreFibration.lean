import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Cylinder.SliceCategory.ForgetFactorization
import HomotopyHypothesis.Cylinder.SliceCategory.ForgetRetraction
open CategoryTheory HomotopicalAlgebra HomotopyHypothesis.Henry

universe u

namespace HomotopyHypothesis.Cylinder.SliceCategory

/-- The forgetful functor from a homotopy slice is a pre-fibration. -/
theorem sliceForget_isPreFibration {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    (X : C) : IsPreFibration (SliceObj.forget X) := by
  constructor
  · intro A B s hs hsw r₀ hr₀
    exact sliceForget_lift_retraction X s hs hsw r₀ hr₀
  · intro A B f Q i w hi hw hfactor
    exact sliceForget_lift_factorization X f i w hi hw hfactor

#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceForget_isPreFibration

end HomotopyHypothesis.Cylinder.SliceCategory
