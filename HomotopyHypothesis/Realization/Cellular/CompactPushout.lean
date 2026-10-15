import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
noncomputable section

open CategoryTheory Limits Topology

namespace HomotopyHypothesis.Realization.Cellular

universe u

/-- Two compact subspaces covering a Hausdorff space form a pushout if their common points
are exactly the image of the proposed intersection. -/
theorem compactCover_isPushout {A B C P : TopCat.{u}} [CompactSpace B] [CompactSpace C]
    [T2Space P] (i : A ⟶ B) (j : A ⟶ C) (k : B ⟶ P) (l : C ⟶ P)
    (sq : CommSq i j k l) (hk : Function.Injective k) (hl : Function.Injective l)
    (cover : ∀ p : P, (∃ b, k b = p) ∨ (∃ c, l c = p))
    (cross : ∀ (b : B) (c : C), k b = l c → ∃ a, i a = b ∧ j a = c) :
    IsPushout i j k l := by
  let q : B ⊕ C → P := Sum.elim k l
  have hsurj : Function.Surjective q := by
    intro p
    rcases cover p with ⟨b, hb⟩ | ⟨c, hc⟩
    · exact ⟨Sum.inl b, hb⟩
    · exact ⟨Sum.inr c, hc⟩
  have hq : IsQuotientMap q :=
    IsQuotientMap.of_surjective_continuous hsurj
      (continuous_sum_dom.mpr ⟨k.hom.continuous, l.hom.continuous⟩)
  apply IsPushout.of_isColimit (c := PushoutCocone.mk k l sq.w)
  apply PushoutCocone.isColimitAux'
  intro t
  let v : B ⊕ C → t.pt := Sum.elim t.inl t.inr
  have hcross : ∀ (b : B) (c : C), k b = l c → t.inl b = t.inr c := by
    intro b c h
    obtain ⟨a, rfl, rfl⟩ := cross b c h
    exact ConcreteCategory.congr_hom t.condition a
  have hv : ∀ x y, q x = q y → v x = v y := by
    rintro (b | c) (b' | c') h
    · exact congrArg t.inl (hk h)
    · exact hcross _ _ h
    · exact (hcross _ _ h.symm).symm
    · exact congrArg t.inr (hl h)
  let d : P → t.pt := fun p => v (Classical.choose (hsurj p))
  have hd : ∀ x, d (q x) = v x := fun x =>
    hv _ x (Classical.choose_spec (hsurj (q x)))
  have hc : Continuous d := hq.continuous_iff.mpr (by
    have h : d ∘ q = v := funext hd
    rw [h]
    exact continuous_sum_dom.mpr ⟨t.inl.hom.continuous, t.inr.hom.continuous⟩)
  let dm : P ⟶ t.pt := TopCat.ofHom ⟨d, hc⟩
  refine ⟨dm, ?_, ?_, ?_⟩
  · apply TopCat.ext
    intro b
    exact hd (Sum.inl b)
  · apply TopCat.ext
    intro c
    exact hd (Sum.inr c)
  · intro m hm₁ hm₂
    apply TopCat.ext
    intro p
    obtain ⟨x, rfl⟩ := hsurj p
    cases x with
    | inl b => exact (ConcreteCategory.congr_hom hm₁ b).trans (hd (Sum.inl b)).symm
    | inr c => exact (ConcreteCategory.congr_hom hm₂ c).trans (hd (Sum.inr c)).symm

end HomotopyHypothesis.Realization.Cellular
