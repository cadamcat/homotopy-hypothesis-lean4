import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
/-!
# Pinching relative subdivision prisms

A relative collapse remains a finite horn-cell composite after identifying the
lateral cylinder with the fixed subcomplex.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

private theorem elementary_anodyne_of_isPushout {A B D E : SemiSSet.{u}}
    {f : A ⟶ B} {g : A ⟶ D} {f' : D ⟶ E} {g' : B ⟶ E}
    (sq : IsPushout g f f' g')
    (hf : (hornInclusions.pushouts ⊔ MorphismProperty.isomorphisms SemiSSet.{u}) f) :
    (hornInclusions.pushouts ⊔ MorphismProperty.isomorphisms SemiSSet.{u}) f' := by
  rcases hf with hf | hf
  · exact Or.inl (MorphismProperty.of_isPushout sq hf)
  · haveI : IsIso f := hf
    exact Or.inr sq.isIso_inl_of_isIso

/-- Finite composites of horn pushouts and isomorphisms are stable under pushout. -/
theorem anodyne_of_isPushout {A B D E : SemiSSet.{u}}
    {f : A ⟶ B} {g : A ⟶ D} {f' : D ⟶ E} {g' : B ⟶ E}
    (sq : IsPushout g f f' g') (hf : anodyne f) : anodyne f' := by
  unfold anodyne at hf ⊢
  induction hf generalizing D E with
  | of f hf =>
    exact .of _ (elementary_anodyne_of_isPushout sq hf)
  | id A =>
    exact .of _ (Or.inr sq.isIso_inl_of_isIso)
  | @comp_of A B C f h hf hh ih =>
    have left := IsPushout.of_hasPushout g f
    have right := sq.of_top' left
    have hi := ih left
    have ht := elementary_anodyne_of_isPushout right hh
    simpa only [IsPushout.inl_desc] using
      MorphismProperty.multiplicativeClosure.comp_of _ _ hi ht

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.anodyne_of_isPushout
