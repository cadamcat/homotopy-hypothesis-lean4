import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Cylinder.SemisimplicialCategory.WeakEquivalences
/-!
# Assembling the cylinder-category axioms for `C^Δ`

The weak-equivalence part of the cylinder-category structure follows from the generated
pre-cylinder class. The remaining data are the cofibration-category axioms, stability of trivial
cofibrations under pushout, cylinder objects, and retractions of trivial cofibrations.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Cylinder.SemisimplicialCategory

theorem cDelta_isCylinderCategory_of_parts
    (hcof : Henry.IsCofibrationCategory Henry.CDelta.{u})
    (htriv : ∀ {A B X P : Henry.CDelta.{u}} (i : A ⟶ B) (f : A ⟶ X)
      (k : B ⟶ P) (j : X ⟶ P), IsPushout i f k j → cofibrations Henry.CDelta.{u} i →
      weakEquivalences Henry.CDelta.{u} i → weakEquivalences Henry.CDelta.{u} j)
    (hcyl : ∀ {I : Henry.CDelta.{u}} (hI : IsInitial I) (X : Henry.CDelta.{u}),
      Nonempty (Henry.RelativeCylinder (hI.to X)))
    (hretract : ∀ {A B : Henry.CDelta.{u}} (i : A ⟶ B),
      cofibrations Henry.CDelta.{u} i → weakEquivalences Henry.CDelta.{u} i →
      ∃ r : B ⟶ A, i ≫ r = 𝟙 A) : Henry.IsCylinderCategory Henry.CDelta.{u} := by
  have hW := cDelta_weakEquivalences_isWeakEquivalenceClass
  exact {
    toIsCofibrationCategory := hcof
    isomorphisms_le_weakEquivalences := hW.1
    weakEquivalences_isMultiplicative := hW.2.1
    twoOutOfSix := hW.2.2.1
    trivialCofibration_cobaseChange := htriv
    exists_cylinder := hcyl
    exists_retraction := hretract
  }

end HomotopyHypothesis.Cylinder.SemisimplicialCategory
