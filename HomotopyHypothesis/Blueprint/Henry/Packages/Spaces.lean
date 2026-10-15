import HomotopyHypothesis.Blueprint.Henry.Packages.Spaces.FinCellRestrictionWeakEquivalenceIff
import HomotopyHypothesis.Blueprint.Henry.Packages.Spaces.FinCellRestrictionIsRightAdjoint
import HomotopyHypothesis.Blueprint.Henry.Packages.Spaces.FinCellRestrictionUnitWeakEquivalence

/-!
# Packages: the completion of finite cell complexes and spaces

H Prop 2.4.18 (H:1432–1440), repaired without a model structure on spaces. Let
`R : TopCat ⥤ Completion FinCell`, `Y ↦ Hom(−, Y)`, be the restriction along the inclusion of
finite cell complexes. Then:

* `R` preserves and reflects weak equivalences (relative homotopy classes of `R Y` are relative
  homotopy classes of maps of finite cell complexes into `Y`; compression);
* `R` has a left adjoint (left Kan extension of the inclusion, restricted to the completion);
* the unit of this adjunction is a weak equivalence at cofibrant objects (compact support: a
  cellular object `X = colim X_i` of the completion has `X(d) = colim Top(d, X_i) = Top(d, L X)`).

Together with the semi-model structure of the completion, these give an equivalence between the
localizations (`isLocalizedEquivalence_of_adjunction`).
-/

/-! The declarations of this file that the development uses are in the modules `HomotopyHypothesis.Blueprint.Henry.Packages.Spaces.*`, one declaration per module. -/
