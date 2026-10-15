import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
/-!
# The generated weak equivalences of `C^Δ`

The weak equivalences of `C^Δ` are defined as the intersection of all classes satisfying the
pre-cylinder axioms and containing the face maps between free simplices. This file records the
pre-cylinder axioms inherited by that intersection.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Cylinder.SemisimplicialCategory

abbrev cDeltaAdmissibleWeakClasses : Set (MorphismProperty Henry.CDelta.{u}) :=
  {W | Henry.IsWeakEquivalenceClass Henry.CDelta.{u} (cofibrations Henry.CDelta.{u}) W ∧
    Henry.CDelta.simplexMaps.{u} ≤ W}

theorem cDelta_all_isWeakEquivalenceClass :
    Henry.IsWeakEquivalenceClass Henry.CDelta.{u} (cofibrations Henry.CDelta.{u})
      (⊤ : MorphismProperty Henry.CDelta.{u}) := by
  refine ⟨?_, inferInstance, ?_, ?_⟩
  · intro X Y f hf
    trivial
  · intro A B Z T f g h hfg hgh
    exact ⟨trivial, trivial, trivial, trivial⟩
  · intro A B X P A' B' X' P' i f k j i' f' k' j' vA vB vX φ hP hP' hi hi' hvA hvB hvX
      hivA hivX hik hix
    trivial

theorem cDelta_admissibleWeakClasses_nonempty : cDeltaAdmissibleWeakClasses.Nonempty := by
  exact ⟨⊤, cDelta_all_isWeakEquivalenceClass, le_top⟩

private theorem cDelta_weakEquivalences_eq :
    weakEquivalences Henry.CDelta.{u} = sInf cDeltaAdmissibleWeakClasses := rfl

theorem cDelta_weakEquivalences_isWeakEquivalenceClass :
    Henry.IsWeakEquivalenceClass Henry.CDelta.{u} (cofibrations Henry.CDelta.{u})
      (weakEquivalences Henry.CDelta.{u}) := by
  have hmember : ∀ W ∈ cDeltaAdmissibleWeakClasses,
      Henry.IsWeakEquivalenceClass Henry.CDelta.{u} (cofibrations Henry.CDelta.{u}) W :=
    fun W hW => hW.1
  constructor
  · intro X Y f hf
    rw [cDelta_weakEquivalences_eq]
    rw [MorphismProperty.sInf_iff]
    intro W hW
    exact (hmember W hW).1 f hf
  constructor
  · rw [cDelta_weakEquivalences_eq]
    exact MorphismProperty.IsMultiplicative.sInf (fun W hW => (hmember W hW).2.1)
  constructor
  · intro A B Z T f g h hfg hgh
    rw [cDelta_weakEquivalences_eq] at hfg hgh
    rw [MorphismProperty.sInf_iff] at hfg hgh
    have hWprop : ∀ W ∈ cDeltaAdmissibleWeakClasses,
        W f ∧ W g ∧ W h ∧ W (f ≫ g ≫ h) := by
      intro W hW
      exact (hmember W hW).2.2.1 f g h (hfg W hW) (hgh W hW)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [cDelta_weakEquivalences_eq, MorphismProperty.sInf_iff]
      exact fun W hW => (hWprop W hW).1
    · rw [cDelta_weakEquivalences_eq, MorphismProperty.sInf_iff]
      exact fun W hW => (hWprop W hW).2.1
    · rw [cDelta_weakEquivalences_eq, MorphismProperty.sInf_iff]
      exact fun W hW => (hWprop W hW).2.2.1
    · rw [cDelta_weakEquivalences_eq, MorphismProperty.sInf_iff]
      exact fun W hW => (hWprop W hW).2.2.2
  · intro A B X P A' B' X' P' i f k j i' f' k' j' vA vB vX φ hP hP' hi hi'
      hvA hvB hvX hivA hivX hik hix
    rw [cDelta_weakEquivalences_eq] at hvA hvB hvX ⊢
    rw [MorphismProperty.sInf_iff] at hvA hvB hvX ⊢
    intro W hW
    exact (hmember W hW).2.2.2 i f k j i' f' k' j' vA vB vX φ hP hP' hi hi'
      (hvA W hW) (hvB W hW) (hvX W hW) hivA hivX hik hix

theorem cDelta_simplexMaps_weakEquivalence :
    Henry.CDelta.simplexMaps.{u} ≤ weakEquivalences Henry.CDelta.{u} := by
  intro X Y f hf
  rw [cDelta_weakEquivalences_eq]
  rw [MorphismProperty.sInf_iff]
  exact fun W hW => hW.2 f hf

end HomotopyHypothesis.Cylinder.SemisimplicialCategory
