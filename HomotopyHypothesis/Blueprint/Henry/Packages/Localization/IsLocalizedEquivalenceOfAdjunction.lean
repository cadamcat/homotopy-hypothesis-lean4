import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Localization.Adjunction.LocalizationAdjunction

/-!
# `isLocalizedEquivalence_of_adjunction`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Localization`, in its own module so that it can import the module that proves it.
-/

universe w v₁ u₁ v₂ u₂

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

section Completion

variable {C : Type u₁} [Category.{v₁} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]
  {D : Type u₂} [Category.{v₂} D] [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]

end Completion

/-- **Localization equivalence from an adjunction with a homotopical right adjoint.** Let `C` be a
semi-model category in which every object is fibrant, `D` a category with a class `WD`, and
`L ⊣ R` an adjunction with `R : D ⥤ C` such that `WD` is exactly the class of maps sent by `R` to
weak equivalences, and the unit is a weak equivalence at cofibrant objects. Then `R` induces an
equivalence between the localizations. Proof: for a cofibrant replacement `q : Q (R Y) ⟶ R Y` (a
trivial fibration), the adjoint `p : L Q R Y ⟶ Y` satisfies `R p ∘ η = q`, hence lies in `WD`;
`L` sends weak equivalences between cofibrant objects into `WD` (2-out-of-3 for the unit and
reflection by `R`), so `L Q` descends to the localization of `C` (homotopy category of cofibrant
objects); the unit and `p` give the two natural isomorphisms. -/
theorem isLocalizedEquivalence_of_adjunction {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {cof fib W : MorphismProperty C} (hC : IsSemiModelCategory C cof fib W)
    (hfib : ∀ X : C, IsFibrantFor fib X) {WD : MorphismProperty D} {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (hR : WD = W.inverseImage R)
    (hunit : ∀ X : C, IsCofibrantFor cof X → W (adj.unit.app X)) :
    (LocalizerMorphism.ofEq hR).IsLocalizedEquivalence := by apply @_root_.HomotopyHypothesis.Localization.Adjunction.Packages.isLocalizedEquivalence_of_adjunction_proof <;> assumption
