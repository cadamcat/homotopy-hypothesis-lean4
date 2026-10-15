import HomotopyHypothesis.Blueprint.Henry.Packages.Localization.CompletionRestrictionIsRightAdjoint
import HomotopyHypothesis.Blueprint.Henry.Packages.Localization.CompletionRestrictionIsQuillenEquivalence
import HomotopyHypothesis.Blueprint.Henry.Packages.Localization.IsLocalizedEquivalenceOfAdjunction

/-!
# Packages: completions, adjunctions and localizations

Abstract results of H §2.4 and of the homotopy theory of semi-model categories, used to compare
completions of cylinder categories with each other and with spaces:

* the restriction `F^*` between completions along a morphism `F` of cylinder categories has a left
  adjoint `F_!` (H Prop 2.4.15), and for an acyclic `F` the pair `F_! ⊣ F^*` is a Quillen
  equivalence (H Prop 2.4.16(3));
* an adjunction `L ⊣ R` out of a semi-model category in which every object is fibrant, whose right
  adjoint preserves and reflects weak equivalences and whose unit is a weak equivalence at cofibrant
  objects, induces an equivalence of localizations; no model structure on the target is needed.
-/

/-! The declarations of this file that the development uses are in the modules `HomotopyHypothesis.Blueprint.Henry.Packages.Localization.*`, one declaration per module. -/
