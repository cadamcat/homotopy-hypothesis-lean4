import Mathlib.CategoryTheory.Limits.Presheaf
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Anodyne

open HomotopyHypothesis.Henry

/-- Geometric realization preserves pushouts because it is a left Kan extension along Yoneda. -/
theorem realization_isPushout_proof {A B C D : SemiSSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {h : B ⟶ D} {k : C ⟶ D} (H : IsPushout f g h k) :
    IsPushout (SemiSSet.realization.map f) (SemiSSet.realization.map g)
      (SemiSSet.realization.map h) (SemiSSet.realization.map k) := by
  letI : PreservesColimit (span f g) SemiSSet.realization :=
    (Presheaf.preservesColimitsOfSize_leftKanExtension.{u, 0, u, 0, 0, u + 1, 0}
      SemiSSet.toTop.{u}).preservesColimitsOfShape.preservesColimit
  exact H.map SemiSSet.realization

#print axioms realization_isPushout_proof

end HomotopyHypothesis.Approximation.Anodyne
