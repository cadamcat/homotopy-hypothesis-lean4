import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Gluing.PushoutHomotopy.AttachInv
import HomotopyHypothesis.Realization.SemisimplicialComparison.TopFacts
universe u

open CategoryTheory Limits TopCat
open HomotopyHypothesis.Henry HomotopyHypothesis.Realization.SemisimplicialComparison

namespace HomotopyHypothesis.Gluing.FiniteCellular

/-- Cobase change of a homotopy equivalence along a relative finite cell complex. -/
theorem homotopyEquivalence_of_isPushout_cobase
    {A B A' P : TopCat.{u}} (i : A ⟶ B) (v : A ⟶ A')
    (k : B ⟶ P) (j : A' ⟶ P) (h : IsPushout i v k j)
    (hi : Top.relativeFiniteCellComplexes i) (hv : Top.homotopyEquivalences v) :
    Top.homotopyEquivalences k := by
  obtain ⟨w, hvw, hwv⟩ := hv
  let r : P ⟶ pushout j w := pushout.inl j w
  let l : A ⟶ pushout j w := pushout.inr j w
  have h₂ : IsPushout j w r l := IsPushout.of_hasPushout j w
  let s : pushout j w ⟶ pushout l v := pushout.inl l v
  let m : A' ⟶ pushout l v := pushout.inr l v
  have h₃ : IsPushout l v s m := IsPushout.of_hasPushout l v
  have hkr : Top.homotopyEquivalences (k ≫ r) :=
    Gluing.PushoutHomotopy.pushout_homotopyEquivalence_inl_of_homotopic_id
      i hi (v ≫ w) hvw (k ≫ r) l (h.flip.paste_horiz h₂.flip).flip
  have hj : Top.relativeFiniteCellComplexes j :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout h.flip hi
  have hrs : Top.homotopyEquivalences (r ≫ s) :=
    Gluing.PushoutHomotopy.pushout_homotopyEquivalence_inl_of_homotopic_id
      j hj (w ≫ v) hwv (r ≫ s) m (h₂.flip.paste_horiz h₃.flip).flip
  exact (hoeq_twoOutOfSix k r s hkr hrs).1

#print axioms homotopyEquivalence_of_isPushout_cobase

end HomotopyHypothesis.Gluing.FiniteCellular
