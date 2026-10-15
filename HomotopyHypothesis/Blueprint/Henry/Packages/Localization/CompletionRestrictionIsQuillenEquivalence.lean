import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Localization.CompletionEquivalence.Localization

/-!
# `completionRestriction_isQuillenEquivalence`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Localization`, in its own module so that it can import the module that proves it.
-/

universe w v₁ u₁ v₂ u₂

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

section Completion

variable {C : Type u₁} [Category.{v₁} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]
  {D : Type u₂} [Category.{v₂} D] [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]

/-- H Prop 2.4.16 (H:1367–1430), all three items: for a morphism `F : C ⥤ D` of essentially small
cylinder categories and any left adjoint `L` of the restriction `F^*`, (1) `π_{B/A}(F^* Y) =
π_{F B/F A}(Y)`, so `F^*` preserves fibrations, trivial fibrations and weak equivalences; (2) for
homotopy fully faithful `F` and cofibrant `X`, `π_{B/A}(X) = π_{F B/F A}(L X)`; (3) if `F` is
acyclic, `L ⊣ F^*` is a Quillen equivalence (homotopy surjectivity replaces any cofibration of `D`
by an image of a cofibration of `C` up to weak equivalence, H:1415–1425). -/
theorem completionRestriction_isQuillenEquivalence [IsCylinderCategory C] [IsCylinderCategory D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D] {F : C ⥤ D} (hF : IsCylinderMorphism F)
    (hac : IsAcyclic F) {L : Completion.{w} C ⥤ Completion.{w} D}
    (adj : L ⊣ Completion.restriction.{w} F hF.toIsCofibrationMorphism) :
    IsQuillenEquivalence adj (Completion.cofibrations C) (Completion.fibrations C)
      (Completion.weakEquivalences C) (Completion.cofibrations D) (Completion.fibrations D)
      (Completion.weakEquivalences D) := by apply (config := {allowSynthFailures := true}) @_root_.HomotopyHypothesis.Localization.CompletionEquivalence.completionRestriction_isQuillenEquivalence_proof <;> assumption
