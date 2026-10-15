import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Localization.CompletionEquivalence.Localization

/-!
# `completionRestriction_isRightAdjoint`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Localization`, in its own module so that it can import the module that proves it.
-/

universe w v₁ u₁ v₂ u₂

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

section Completion

variable {C : Type u₁} [Category.{v₁} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]
  {D : Type u₂} [Category.{v₂} D] [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]

/-- H Prop 2.4.15 (H:1355): restriction between completions along a morphism of cofibration
categories `F : C ⥤ D` between essentially small categories has a left adjoint: the left Kan
extension along `F^op` of a completion presheaf on `C`, followed by the reflection of presheaves on
`D` into the completion (the completion is the full subcategory of presheaves orthogonal to a small
set of maps: `∅ ⟶ y I` for initial `I`, and `y B ⊔_{y A} y X ⟶ y Q` for pushouts along
cofibrations, hence reflective). -/
theorem completionRestriction_isRightAdjoint [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {F : C ⥤ D} (hF : IsCofibrationMorphism F) :
    (Completion.restriction.{w} F hF).IsRightAdjoint := _root_.HomotopyHypothesis.Localization.CompletionEquivalence.completionRestriction_isRightAdjoint_proof ..
