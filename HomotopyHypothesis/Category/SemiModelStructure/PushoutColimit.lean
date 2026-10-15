import Mathlib
/-!
# Pushouts of filtered colimits

If `X` is the colimit of a diagram `F` and a map `x : A ⟶ X` factors through `F k₀`, then the
pushout of `m : A ⟶ B` along `x` is the colimit over `Under k₀` of the pushouts of `m` along the
induced maps `A ⟶ F k`.
-/

universe w v u

open CategoryTheory Limits

namespace HomotopyHypothesis.Category.SemiModelStructure

variable {𝒟 : Type u} [Category.{v} 𝒟] [HasPushouts 𝒟]

section

variable {K : Type w} [Category.{w} K] (F : K ⥤ 𝒟) {A B : 𝒟} (m : A ⟶ B) {k₀ : K}
  (x₀ : A ⟶ F.obj k₀)

/-- The diagram `s ↦ F s ⊔_A B` over `Under k₀`. -/
@[simps, reducible]
noncomputable def underPushoutFunctor : Under k₀ ⥤ 𝒟 where
  obj s := pushout (x₀ ≫ F.map s.hom) m
  map {s s'} φ := pushout.desc (F.map φ.right ≫ pushout.inl _ _) (pushout.inr _ _) (by
    rw [← pushout.condition, Category.assoc, ← Category.assoc (F.map s.hom), ← F.map_comp,
      Under.w φ]
    simp only [Category.assoc])
  map_id s := by
    apply pushout.hom_ext
    · simp only [pushout.inl_desc, Under.id_right, F.map_id, Category.id_comp, Category.comp_id]
    · simp only [pushout.inr_desc, Category.comp_id]
  map_comp {s s' s''} φ ψ := by
    apply pushout.hom_ext
    · simp only [pushout.inl_desc, pushout.inl_desc_assoc, Under.comp_right, F.map_comp,
        Category.assoc]
    · simp only [pushout.inr_desc, pushout.inr_desc_assoc]

/-- The inclusion `F s ⟶ F s ⊔_A B`. -/
@[simps]
noncomputable def underPushoutInl : Under.forget k₀ ⋙ F ⟶ underPushoutFunctor F m x₀ where
  app s := pushout.inl _ _
  naturality {s s'} φ := by
    change F.map φ.right ≫ pushout.inl _ _ = pushout.inl _ _ ≫ pushout.desc _ _ _
    rw [pushout.inl_desc]

end

variable {K : Type w} [Category.{w} K] [IsFiltered K] {F : K ⥤ 𝒟} {c : Cocone F}
  (hc : IsColimit c) {A B : 𝒟} (m : A ⟶ B) {k₀ : K} (x₀ : A ⟶ F.obj k₀)
  {X' : 𝒟} (u : c.pt ⟶ X') (d : B ⟶ X') (h : IsPushout (x₀ ≫ c.ι.app k₀) m u d)

include h in
theorem underPushout_leg_w (s : Under k₀) :
    (x₀ ≫ F.map s.hom) ≫ c.ι.app s.right ≫ u = m ≫ d := by
  have := c.w s.hom
  rw [Category.assoc, ← Category.assoc (F.map s.hom), this, ← Category.assoc]
  exact h.w

/-- The cocone over the stage pushouts with apex the pushout `X'`. -/
@[simps, reducible]
noncomputable def underPushoutCocone : Cocone (underPushoutFunctor F m x₀) where
  pt := X'
  ι :=
    { app := fun s => pushout.desc (c.ι.app s.right ≫ u) d (underPushout_leg_w m x₀ u d h s)
      naturality := by
        intro s s' φ
        apply pushout.hom_ext
        · change pushout.inl _ _ ≫ pushout.desc _ _ _ ≫ pushout.desc _ _ _ =
            pushout.inl _ _ ≫ pushout.desc _ _ _ ≫ 𝟙 X'
          rw [pushout.inl_desc_assoc, Category.assoc, pushout.inl_desc, Category.comp_id,
            pushout.inl_desc]
          have := c.w φ.right
          rw [← Category.assoc, this]
        · change pushout.inr _ _ ≫ pushout.desc _ _ _ ≫ pushout.desc _ _ _ =
            pushout.inr _ _ ≫ pushout.desc _ _ _ ≫ 𝟙 X'
          rw [pushout.inr_desc_assoc, pushout.inr_desc, Category.comp_id, pushout.inr_desc] }

/-- The colimit cocone of `F` restricted to `Under k₀`. -/
noncomputable def underIsColimit : IsColimit (c.whisker (Under.forget k₀)) :=
  (Functor.Final.isColimitWhiskerEquiv (Under.forget k₀) c).symm hc

/-- The pushout `X'` is the colimit of the stage pushouts. -/
noncomputable def underPushoutIsColimit : IsColimit (underPushoutCocone m x₀ u d h) := by
  let j₀' : Under k₀ := Under.mk (𝟙 k₀)
  let hc₀ := underIsColimit (k₀ := k₀) hc
  have hfac (T : Cocone (underPushoutFunctor F m x₀)) (s : Under k₀) :
      c.ι.app s.right ≫ hc₀.desc (Cocone.mk T.pt (underPushoutInl F m x₀ ≫ T.ι)) =
        pushout.inl _ _ ≫ T.ι.app s :=
    hc₀.fac (Cocone.mk T.pt (underPushoutInl F m x₀ ≫ T.ι)) s
  have hT (T : Cocone (underPushoutFunctor F m x₀)) (s : Under k₀) :
      pushout.inr (x₀ ≫ F.map j₀'.hom) m ≫ T.ι.app j₀' = pushout.inr _ _ ≫ T.ι.app s := by
    have := T.w (Under.homMk s.hom (by simp [j₀']) : j₀' ⟶ s)
    rw [← this]
    change pushout.inr _ _ ≫ pushout.desc _ _ _ ≫ T.ι.app s = _
    rw [pushout.inr_desc_assoc]
  exact
    { desc := fun T => h.desc (hc₀.desc (Cocone.mk T.pt (underPushoutInl F m x₀ ≫ T.ι)))
        (pushout.inr _ _ ≫ T.ι.app j₀') (by
          have hfac0 : c.ι.app k₀ ≫ hc₀.desc (Cocone.mk T.pt (underPushoutInl F m x₀ ≫ T.ι)) =
              pushout.inl (x₀ ≫ F.map j₀'.hom) m ≫ T.ι.app j₀' := hfac T j₀'
          rw [Category.assoc, hfac0, ← Category.assoc]
          have : x₀ ≫ pushout.inl (x₀ ≫ F.map j₀'.hom) m =
              (x₀ ≫ F.map j₀'.hom) ≫ pushout.inl (x₀ ≫ F.map j₀'.hom) m := by
            simp [j₀']
          rw [this, pushout.condition, Category.assoc])
      fac := fun T s => by
        apply pushout.hom_ext
        · change pushout.inl _ _ ≫ pushout.desc _ _ _ ≫ _ = _
          rw [pushout.inl_desc_assoc, Category.assoc, h.inl_desc, hfac T s]
        · change pushout.inr _ _ ≫ pushout.desc _ _ _ ≫ _ = _
          rw [pushout.inr_desc_assoc, h.inr_desc, hT T s]
      uniq := fun T g hg => by
        apply h.hom_ext
        · rw [h.inl_desc]
          apply hc₀.hom_ext
          intro s
          change c.ι.app s.right ≫ u ≫ g = c.ι.app s.right ≫ _
          rw [hfac T s, ← hg s]
          change _ = pushout.inl _ _ ≫ pushout.desc _ _ _ ≫ g
          rw [pushout.inl_desc_assoc, Category.assoc]
        · rw [h.inr_desc, ← hg j₀']
          change _ = pushout.inr _ _ ≫ pushout.desc _ _ _ ≫ g
          rw [pushout.inr_desc_assoc] }

end HomotopyHypothesis.Category.SemiModelStructure
