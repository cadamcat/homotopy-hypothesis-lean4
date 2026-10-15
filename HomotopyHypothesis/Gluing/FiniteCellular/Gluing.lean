import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Gluing.PushoutHomotopy.Gluing
import HomotopyHypothesis.Realization.SemisimplicialComparison.TopFacts
import HomotopyHypothesis.Gluing.FiniteCellular.Cobase
/-!
# Gluing homotopy equivalences along relative finite cell complexes

The gluing theorem follows by changing the right space by cobase change, then changing the
attaching space by an iterated pushout and applying the gluing theorem under a fixed base.
-/

universe u

open CategoryTheory Limits TopCat
open HomotopyHypothesis.Henry HomotopyHypothesis.Realization.SemisimplicialComparison

namespace HomotopyHypothesis.Henry.Packages

/-- A map of pushout squares along relative finite cell complexes is a homotopy equivalence
when its three components are homotopy equivalences. -/
theorem homotopyEquivalence_of_isPushout_proof
    {A B C P A' B' C' P' : TopCat.{u}} (i : A ⟶ B)
    (f : A ⟶ C) (k : B ⟶ P) (j : C ⟶ P) (i' : A' ⟶ B') (f' : A' ⟶ C') (k' : B' ⟶ P')
    (j' : C' ⟶ P') (vA : A ⟶ A') (vB : B ⟶ B') (vC : C ⟶ C') (φ : P ⟶ P')
    (h : IsPushout i f k j) (h' : IsPushout i' f' k' j') (hi : Top.relativeFiniteCellComplexes i)
    (hi' : Top.relativeFiniteCellComplexes i') (hA : Top.homotopyEquivalences vA)
    (hB : Top.homotopyEquivalences vB) (hC : Top.homotopyEquivalences vC)
    (c₁ : i ≫ vB = vA ≫ i') (c₂ : f ≫ vC = vA ≫ f') (c₃ : k ≫ φ = vB ≫ k')
    (c₄ : j ≫ φ = vC ≫ j') : Top.homotopyEquivalences φ := by
  let D := pushout i vA
  let b : B ⟶ D := pushout.inl i vA
  let a : A' ⟶ D := pushout.inr i vA
  have hd : IsPushout i vA b a := IsPushout.of_hasPushout i vA
  have ha : Top.relativeFiniteCellComplexes a :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hd.flip hi
  have hb : Top.homotopyEquivalences b :=
    Gluing.FiniteCellular.homotopyEquivalence_of_isPushout_cobase i vA b a hd hi hA
  let w : D ⟶ B' := hd.desc vB i' c₁
  have hbw : b ≫ w = vB := hd.inl_desc _ _ _
  have haw : a ≫ w = i' := hd.inr_desc _ _ _
  have hw : Top.homotopyEquivalences w :=
    hoeq_of_comp_left hb (by rw [hbw]; exact hB)
  let Q := pushout a f'
  let d : D ⟶ Q := pushout.inl a f'
  let c : C' ⟶ Q := pushout.inr a f'
  have hq : IsPushout a f' d c := IsPushout.of_hasPushout a f'
  have hwk : a ≫ (w ≫ k') = f' ≫ j' := by
    rw [← Category.assoc, haw]
    exact h'.w
  let q : Q ⟶ P' := hq.desc (w ≫ k') j' hwk
  have hdq : d ≫ q = w ≫ k' := hq.inl_desc _ _ _
  have hcq : c ≫ q = j' := hq.inr_desc _ _ _
  have heq : Top.homotopyEquivalences q :=
    Gluing.PushoutHomotopy.homotopyEquivalence_of_isPushout_under
      a f' d c i' k' j' hq h' ha hi' w hw haw q hdq hcq
  let R := pushout j vC
  let p : P ⟶ R := pushout.inl j vC
  let z : C' ⟶ R := pushout.inr j vC
  have hr : IsPushout j vC p z := IsPushout.of_hasPushout j vC
  have hj : Top.relativeFiniteCellComplexes j :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout h.flip hi
  have hp : Top.homotopyEquivalences p :=
    Gluing.FiniteCellular.homotopyEquivalence_of_isPushout_cobase j vC p z hr hj hC
  have houterR : IsPushout i (f ≫ vC) (k ≫ p) z :=
    (h.flip.paste_horiz hr.flip).flip
  have houterQ : IsPushout i (f ≫ vC) (b ≫ d) c := by
    rw [c₂]
    exact (hd.flip.paste_horiz hq.flip).flip
  let e : R ≅ Q := houterR.isoIsPushout _ _ houterQ
  have hke : (k ≫ p) ≫ e.hom = b ≫ d :=
    IsPushout.inl_isoIsPushout_hom B C' houterR houterQ
  have hze : z ≫ e.hom = c :=
    IsPushout.inr_isoIsPushout_hom B C' houterR houterQ
  have hφ : φ = p ≫ e.hom ≫ q := by
    apply h.hom_ext
    · calc
        k ≫ φ = vB ≫ k' := c₃
        _ = (b ≫ w) ≫ k' := by rw [hbw]
        _ = (b ≫ d) ≫ q := by simp only [Category.assoc, hdq]
        _ = ((k ≫ p) ≫ e.hom) ≫ q := by rw [hke]
        _ = k ≫ (p ≫ e.hom ≫ q) := by simp only [Category.assoc]
    · calc
        j ≫ φ = vC ≫ j' := c₄
        _ = vC ≫ (c ≫ q) := by rw [hcq]
        _ = vC ≫ ((z ≫ e.hom) ≫ q) := by rw [hze]
        _ = (vC ≫ z) ≫ (e.hom ≫ q) := by simp only [Category.assoc]
        _ = (j ≫ p) ≫ (e.hom ≫ q) := by rw [hr.w]
        _ = j ≫ (p ≫ e.hom ≫ q) := by simp only [Category.assoc]
  rw [hφ]
  exact hoeq_comp hp (hoeq_comp (hoeq_of_isIso e.hom) heq)

#print axioms homotopyEquivalence_of_isPushout_proof

end HomotopyHypothesis.Henry.Packages
