import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
noncomputable section

open CategoryTheory Limits HomotopicalAlgebra
open HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Realization.Cellular

universe v u v' u'

variable {D : Type u} [Category.{v} D] [CategoryWithCofibrations D]
    [CategoryWithWeakEquivalences D] [IsCylinderCategory D]

private theorem weak_of_section {A B : D} (s : A ⟶ B) (p : B ⟶ A)
    (h : s ≫ p = 𝟙 A) (hp : weakEquivalences D p) : weakEquivalences D s := by
  have hid : weakEquivalences D (𝟙 A) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences _ (inferInstance : IsIso (𝟙 A))
  exact (IsCylinderCategory.twoOutOfSix s p (𝟙 A)
    (h.symm ▸ hid) (by simpa using hp)).1

/-- Brown's factorization using only the axioms of a cylinder category. -/
theorem cylinder_brown_factorization {X Y : D} (f : X ⟶ Y) :
    ∃ (Z : D) (i : X ⟶ Z) (p : Z ⟶ Y) (s : Y ⟶ Z),
      i ≫ p = f ∧ s ≫ p = 𝟙 Y ∧ cofibrations D i ∧ cofibrations D s ∧
      weakEquivalences D p ∧ weakEquivalences D s := by
  obtain ⟨A, ⟨hA⟩⟩ := IsCofibrationCategory.exists_initial (C := D)
  obtain ⟨cyl⟩ := IsCylinderCategory.exists_cylinder hA X
  haveI := IsCofibrationCategory.isMultiplicative (C := D)
  haveI := IsCofibrationCategory.isStableUnderCobaseChange (C := D)
  haveI := IsCylinderCategory.weakEquivalences_isMultiplicative (C := D)
  have hinitX := IsCofibrationCategory.initial_cofibration hA X
  have hinitY := IsCofibrationCategory.initial_cofibration hA Y
  haveI : HasPushout (hA.to Y) (hA.to X) :=
    IsCofibrationCategory.hasPushout _ _ hinitY
  let Q := pushout (hA.to Y) (hA.to X)
  let jY : Y ⟶ Q := pushout.inl _ _
  let jX : X ⟶ Q := pushout.inr _ _
  have qsq : IsPushout (hA.to Y) (hA.to X) jY jX := IsPushout.of_hasPushout _ _
  have hjY : cofibrations D jY :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout qsq hinitX
  have hjX : cofibrations D jX :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout qsq.flip hinitY
  let a : cyl.P ⟶ Q := cyl.isPushout.desc (f ≫ jY) jX (hA.hom_ext _ _)
  let q : Q ⟶ Y := qsq.desc (𝟙 Y) f (hA.hom_ext _ _)
  have ha₀ : cyl.j₀ ≫ a = f ≫ jY := cyl.isPushout.inl_desc _ _ _
  have ha₁ : cyl.j₁ ≫ a = jX := cyl.isPushout.inr_desc _ _ _
  have hqY : jY ≫ q = 𝟙 Y := qsq.inl_desc _ _ _
  have hqX : jX ≫ q = f := qsq.inr_desc _ _ _
  have haq : a ≫ q = cyl.c ≫ cyl.p ≫ f := by
    apply cyl.isPushout.hom_ext
    · calc
        cyl.j₀ ≫ (a ≫ q) = f := by
          rw [← Category.assoc, ha₀, Category.assoc, hqY, Category.comp_id]
        _ = cyl.j₀ ≫ (cyl.c ≫ cyl.p ≫ f) := by
          simpa only [Category.assoc, Category.id_comp] using
            (congrArg (· ≫ f) cyl.j₀_c_p).symm
    · calc
        cyl.j₁ ≫ (a ≫ q) = f := by rw [← Category.assoc, ha₁, hqX]
        _ = cyl.j₁ ≫ (cyl.c ≫ cyl.p ≫ f) := by
          simpa only [Category.assoc, Category.id_comp] using
            (congrArg (· ≫ f) cyl.j₁_c_p).symm
  haveI : HasPushout cyl.c a := IsCofibrationCategory.hasPushout _ _ cyl.c_mem
  haveI : HasPushout a cyl.c := hasPushout_symmetry _ _
  let Z := pushout a cyl.c
  let k : Q ⟶ Z := pushout.inl _ _
  let l : cyl.I ⟶ Z := pushout.inr _ _
  have zsq : IsPushout a cyl.c k l := IsPushout.of_hasPushout _ _
  have hk : cofibrations D k :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout zsq cyl.c_mem
  let i : X ⟶ Z := jX ≫ k
  let s : Y ⟶ Z := jY ≫ k
  let p : Z ⟶ Y := zsq.desc q (cyl.p ≫ f) haq
  have hi : cofibrations D i := (cofibrations D).comp_mem _ _ hjX hk
  have hs : cofibrations D s := (cofibrations D).comp_mem _ _ hjY hk
  have hip : i ≫ p = f := by
    simp only [i, p, Category.assoc, IsPushout.inl_desc, q, IsPushout.inr_desc]
  have hsp : s ≫ p = 𝟙 Y := by
    simp only [s, p, Category.assoc, IsPushout.inl_desc, q, IsPushout.inl_desc]
  have replace : IsPushout cyl.j₀ f a jY := by
    apply IsPushout.of_isColimit (c := PushoutCocone.mk a jY ha₀)
    apply PushoutCocone.isColimitAux'
    intro t
    let d : Q ⟶ t.pt := qsq.desc t.inr (cyl.j₁ ≫ t.inl) (hA.hom_ext _ _)
    refine ⟨d, ?_, ?_, ?_⟩
    · change a ≫ d = t.inl
      apply cyl.isPushout.hom_ext
      · rw [← Category.assoc, ha₀, Category.assoc]
        dsimp only [d]
        rw [qsq.inl_desc]
        exact t.condition.symm
      · rw [← Category.assoc, ha₁]
        exact qsq.inr_desc _ _ _
    · change jY ≫ d = t.inr
      exact qsq.inl_desc _ _ _
    · intro m hm₁ hm₂
      change Q ⟶ t.pt at m
      change a ≫ m = t.inl at hm₁
      change jY ≫ m = t.inr at hm₂
      apply qsq.hom_ext
      · exact hm₂.trans (qsq.inl_desc _ _ _).symm
      · have hma := congrArg (cyl.j₁ ≫ ·) hm₁
        have hma' : (cyl.j₁ ≫ a) ≫ m = cyl.j₁ ≫ t.inl := by
          simpa only [Category.assoc] using hma
        rw [ha₁] at hma'
        exact hma'.trans (qsq.inr_desc _ _ _).symm
  have ssq : IsPushout (cyl.j₀ ≫ cyl.c) f l s :=
    replace.paste_horiz zsq.flip
  have hcof_j₀ : cofibrations D cyl.j₀ :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout cyl.isPushout hinitX
  have hcof_e₀ : cofibrations D (cyl.j₀ ≫ cyl.c) :=
    (cofibrations D).comp_mem _ _ hcof_j₀ cyl.c_mem
  have hwe : weakEquivalences D (cyl.j₀ ≫ cyl.c) :=
    weak_of_section _ cyl.p (by simpa only [Category.assoc] using cyl.j₀_c_p) cyl.p_mem
  have hws : weakEquivalences D s :=
    IsCylinderCategory.trivialCofibration_cobaseChange _ _ _ _ ssq hcof_e₀ hwe
  have hid : weakEquivalences D (𝟙 Y) := (weakEquivalences D).id_mem _
  have hwp : weakEquivalences D p :=
    (IsCylinderCategory.twoOutOfSix (𝟙 Y) s p
      (by simpa using hws) (hsp.symm ▸ hid)).2.2.1
  exact ⟨Z, i, p, s, hip, hsp, hi, hs, hwp, hws⟩

/-- It suffices to preserve trivial cofibrations to preserve all weak equivalences. -/
theorem cylinder_brown_map {E : Type u'} [Category.{v'} E] (F : D ⥤ E)
    (Q : MorphismProperty E) [Q.HasTwoOutOfThreeProperty] [Q.ContainsIdentities]
    (hF : ∀ ⦃X Y : D⦄ (f : X ⟶ Y), cofibrations D f → weakEquivalences D f → Q (F.map f))
    {X Y : D} (f : X ⟶ Y) (hf : weakEquivalences D f) : Q (F.map f) := by
  obtain ⟨Z, i, p, s, hip, hsp, hi, hs, hp, hws⟩ := cylinder_brown_factorization f
  have hwi : weakEquivalences D i :=
    (IsCylinderCategory.twoOutOfSix i p (𝟙 Y)
      (hip.symm ▸ hf) (by simpa using hp)).1
  have his := hF i hi hwi
  have hss := hF s hs hws
  have hps : Q (F.map p) := Q.of_precomp (F.map s) (F.map p) hss (by
    rw [← F.map_comp, hsp, F.map_id]
    exact Q.id_mem _)
  rw [← hip, F.map_comp]
  exact Q.comp_mem _ _ his hps

end HomotopyHypothesis.Realization.Cellular
