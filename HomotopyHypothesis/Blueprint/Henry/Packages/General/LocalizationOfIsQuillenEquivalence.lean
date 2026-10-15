import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Localization.Quillen.Localization

/-!
# `localization_of_isQuillenEquivalence`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.General`, in its own module so that it can import the module that proves it.
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

section Cylinder

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

end Cylinder

section Acyclic

variable {C : Type u₁} [Category.{v₁} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]
  {D : Type u₂} [Category.{v₂} D] [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]
  {E : Type u₃} [Category.{v₃} E] [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
  {F : Type u₄} [Category.{v₄} F] [CategoryWithCofibrations F] [CategoryWithWeakEquivalences F]

end Acyclic

section Completion

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

end Completion

section SemiModel

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- H:356–364: a Quillen equivalence between semi-model categories induces an equivalence of
homotopy categories. Stated for a right adjoint `R` out of a semi-model category in which every
object is fibrant: `R` sends weak equivalences to weak equivalences (Ken Brown's lemma), and the
induced functor between any localizations is an equivalence. -/
theorem localization_of_isQuillenEquivalence {cofC fibC WC : MorphismProperty C}
    {cofD fibD WD : MorphismProperty D} (hC : IsSemiModelCategory C cofC fibC WC)
    (hD : IsSemiModelCategory D cofD fibD WD) (hfib : ∀ Y : D, IsFibrantFor fibD Y)
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (hQ : IsQuillenEquivalence adj cofC fibC WC cofD fibD WD) :
    WD ≤ WC.inverseImage R ∧
    ∀ {H₁ : Type u₃} {H₂ : Type u₄} [Category.{v₃} H₁] [Category.{v₄} H₂] (L₁ : D ⥤ H₁)
      [L₁.IsLocalization WD] (L₂ : C ⥤ H₂) [L₂.IsLocalization WC] (Φ : H₁ ⥤ H₂),
      (L₁ ⋙ Φ ≅ R ⋙ L₂) → Φ.IsEquivalence := by apply @_root_.HomotopyHypothesis.Localization.Quillen.localization_of_isQuillenEquivalence_proof <;> assumption
