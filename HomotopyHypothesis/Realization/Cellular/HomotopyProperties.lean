import HomotopyHypothesis.Blueprint.Henry.Topology
noncomputable section

open CategoryTheory Limits
open HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Realization.Cellular

universe u

private def MapHomotopic {X Y : TopCat.{u}} (f g : X ⟶ Y) : Prop :=
  f.hom.Homotopic g.hom

private theorem ht_refl {X Y : TopCat.{u}} (f : X ⟶ Y) : MapHomotopic f f :=
  ContinuousMap.Homotopic.refl _

private theorem ht_comp {X Y Z : TopCat.{u}} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    (hf : MapHomotopic f f') (hg : MapHomotopic g g') :
    MapHomotopic (f ≫ g) (f' ≫ g') := hg.comp hf

instance homotopyEquivalences_containsIdentities : Top.homotopyEquivalences.{u}.ContainsIdentities where
  id_mem X := ⟨𝟙 X, ContinuousMap.Homotopic.refl _, ContinuousMap.Homotopic.refl _⟩

instance homotopyEquivalences_multiplicative : Top.homotopyEquivalences.{u}.IsMultiplicative where
  comp_mem := by
    intro X Y Z f g hf hg
    obtain ⟨r, hr₁, hr₂⟩ := hf
    obtain ⟨s, hs₁, hs₂⟩ := hg
    refine ⟨s ≫ r, ?_, ?_⟩
    · have h : MapHomotopic ((f ≫ g) ≫ (s ≫ r)) (f ≫ r) := by
        simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
          ht_comp (ht_comp (ht_refl f) hs₁) (ht_refl r)
      exact h.trans hr₁
    · have h : MapHomotopic ((s ≫ r) ≫ (f ≫ g)) (s ≫ g) := by
        simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
          ht_comp (ht_comp (ht_refl s) hr₂) (ht_refl g)
      exact h.trans hs₂

private theorem homotopyEquivalences_of_precomp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Top.homotopyEquivalences f) (hfg : Top.homotopyEquivalences (f ≫ g)) :
    Top.homotopyEquivalences g := by
  obtain ⟨r, hr₁, hr₂⟩ := hf
  obtain ⟨s, hs₁, hs₂⟩ := hfg
  refine ⟨s ≫ f, ?_, ?_⟩
  · have h₁ : MapHomotopic (g ≫ (s ≫ f)) ((r ≫ f) ≫ (g ≫ (s ≫ f))) := by
      simpa only [Category.id_comp] using ht_comp hr₂.symm (ht_refl (g ≫ (s ≫ f)))
    have h₂ : MapHomotopic ((r ≫ f) ≫ (g ≫ (s ≫ f))) (r ≫ f) := by
      simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
        ht_comp (ht_comp (ht_refl r) hs₁) (ht_refl f)
    exact (h₁.trans h₂).trans hr₂
  · simpa only [Category.assoc] using hs₂

private theorem homotopyEquivalences_of_postcomp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : Top.homotopyEquivalences g) (hfg : Top.homotopyEquivalences (f ≫ g)) :
    Top.homotopyEquivalences f := by
  obtain ⟨r, hr₁, hr₂⟩ := hg
  obtain ⟨s, hs₁, hs₂⟩ := hfg
  refine ⟨g ≫ s, ?_, ?_⟩
  · simpa only [Category.assoc] using hs₁
  · have h₁ : MapHomotopic ((g ≫ s) ≫ f) (((g ≫ s) ≫ f) ≫ (g ≫ r)) := by
      simpa only [Category.comp_id] using ht_comp (ht_refl ((g ≫ s) ≫ f)) hr₁.symm
    have h₂ : MapHomotopic (((g ≫ s) ≫ f) ≫ (g ≫ r)) (g ≫ r) := by
      simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
        ht_comp (ht_comp (ht_refl g) hs₂) (ht_refl r)
    exact (h₁.trans h₂).trans hr₁

instance homotopyEquivalences_twoOutOfThree : Top.homotopyEquivalences.{u}.HasTwoOutOfThreeProperty where
  of_precomp := homotopyEquivalences_of_precomp
  of_postcomp := homotopyEquivalences_of_postcomp

end HomotopyHypothesis.Realization.Cellular
