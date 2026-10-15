import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Cylinder.PreCylinderCategory.Basic
import HomotopyHypothesis.Cylinder.PreCylinderCategory.Pushout
namespace HomotopyHypothesis.Cylinder.PreCylinderCategory

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe v u

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]

/-- Brown factorization data for `f : A ⟶ B`: a cofibration `i : A ⟶ P`,
a weak equivalence `p : P ⟶ B` with `i ≫ p = f`, plus a trivial cofibration
section `s : B ⟶ P` of `p`. (H Prop 2.2.1, H:485.) -/
structure BrownFactorization [IsCylinderCategory C] {A B : C} (f : A ⟶ B) where
  P : C
  i : A ⟶ P
  p : P ⟶ B
  s : B ⟶ P
  fac : i ≫ p = f
  sec : s ≫ p = 𝟙 B
  cof_i : cofibrations C i
  we_p : weakEquivalences C p
  cof_s : cofibrations C s
  we_s : weakEquivalences C s

/-- The two inclusions `A ⟶ IA` of a cylinder are trivial cofibrations. -/
theorem cyl_incl_trivial [IsCylinderCategory C] {I A : C} (hI : IsInitial I)
    (cyl : RelativeCylinder (hI.to A)) :
    cofibrations C (cyl.j₀ ≫ cyl.c) ∧ weakEquivalences C (cyl.j₀ ≫ cyl.c) ∧
    cofibrations C (cyl.j₁ ≫ cyl.c) ∧ weakEquivalences C (cyl.j₁ ≫ cyl.c) := by
  haveI := we_twoOutOfThree (C := C)
  have hcofA : cofibrations C (hI.to A) :=
    IsCofibrationCategory.initial_cofibration hI A
  have hj₀ : cofibrations C cyl.j₀ := by
    have := (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      (sq := cyl.isPushout) (hf := hcofA)
    exact this
  have hj₁ : cofibrations C cyl.j₁ := by
    have := (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      (sq := cyl.isPushout.flip) (hf := hcofA)
    exact this
  have hcof_j₀c : cofibrations C (cyl.j₀ ≫ cyl.c) :=
    IsCofibrationCategory.isMultiplicative.toIsStableUnderComposition.comp_mem _ _ hj₀ cyl.c_mem
  have hcof_j₁c : cofibrations C (cyl.j₁ ≫ cyl.c) :=
    IsCofibrationCategory.isMultiplicative.toIsStableUnderComposition.comp_mem _ _ hj₁ cyl.c_mem
  have hwe_j₀c : weakEquivalences C (cyl.j₀ ≫ cyl.c) := by
    have hid : weakEquivalences C (𝟙 A) := we_id A
    have hfac : weakEquivalences C ((cyl.j₀ ≫ cyl.c) ≫ cyl.p) := by
      have : (cyl.j₀ ≫ cyl.c) ≫ cyl.p = 𝟙 A := by
        rw [Category.assoc, cyl.j₀_c_p]
      rw [this]
      exact hid
    exact MorphismProperty.of_postcomp (weakEquivalences C) _ _ cyl.p_mem hfac
  have hwe_j₁c : weakEquivalences C (cyl.j₁ ≫ cyl.c) := by
    have hid : weakEquivalences C (𝟙 A) := we_id A
    have hfac : weakEquivalences C ((cyl.j₁ ≫ cyl.c) ≫ cyl.p) := by
      have : (cyl.j₁ ≫ cyl.c) ≫ cyl.p = 𝟙 A := by
        rw [Category.assoc, cyl.j₁_c_p]
      rw [this]
      exact hid
    exact MorphismProperty.of_postcomp (weakEquivalences C) _ _ cyl.p_mem hfac
  exact ⟨hcof_j₀c, hwe_j₀c, hcof_j₁c, hwe_j₁c⟩

/-- Any map in a cylinder category admits a Brown factorization. -/
theorem brown_factorization [IsCylinderCategory C] {A B : C} (f : A ⟶ B) :
    Nonempty (BrownFactorization (C := C) f) := by
  classical
  haveI := we_twoOutOfThree (C := C)
  obtain ⟨I, ⟨hI⟩⟩ := IsCofibrationCategory.exists_initial (C := C)
  obtain ⟨cylA⟩ := IsCylinderCategory.exists_cylinder (C := C) (hI : IsInitial I) (A)
  obtain ⟨hcof_j₀c, hwe_j₀c, hcof_j₁c, hwe_j₁c⟩ := cyl_incl_trivial (C := C) hI cylA
  have hcofA : cofibrations C (hI.to A) :=
    IsCofibrationCategory.initial_cofibration hI A
  have hcofB : cofibrations C (hI.to B) :=
    IsCofibrationCategory.initial_cofibration hI B
  haveI : HasPushout (hI.to A) (hI.to B) :=
    IsCofibrationCategory.hasPushout _ _ hcofA
  let AB := pushout (hI.to A) (hI.to B)
  let inlAB : A ⟶ AB := pushout.inl _ _
  let inrAB : B ⟶ AB := pushout.inr _ _
  have hAB : IsPushout (hI.to A) (hI.to B) inlAB inrAB :=
    IsPushout.of_hasPushout _ _
  have hagree : (hI.to A) ≫ inlAB = (hI.to A) ≫ (f ≫ inrAB) := by
    have h1 : (hI.to A) ≫ f = hI.to B := hI.hom_ext _ _
    calc (hI.to A) ≫ inlAB
        = (hI.to B) ≫ inrAB := hAB.w
      _ = ((hI.to A) ≫ f) ≫ inrAB := by rw [h1]
      _ = (hI.to A) ≫ (f ≫ inrAB) := by rw [Category.assoc]
  let m₀ : cylA.P ⟶ AB := cylA.isPushout.desc inlAB (f ≫ inrAB) hagree
  have hj₀ : cylA.j₀ ≫ m₀ = inlAB := cylA.isPushout.inl_desc _ _ _
  have hj₁ : cylA.j₁ ≫ m₀ = f ≫ inrAB := cylA.isPushout.inr_desc _ _ _
  haveI : HasPushout cylA.c m₀ := IsCofibrationCategory.hasPushout _ _ cylA.c_mem
  let Pobj := pushout cylA.c m₀
  let inlIA : cylA.I ⟶ Pobj := pushout.inl _ _
  let inrABP : AB ⟶ Pobj := pushout.inr _ _
  have hP : IsPushout cylA.c m₀ inlIA inrABP := IsPushout.of_hasPushout _ _
  let i : A ⟶ Pobj := inlAB ≫ inrABP
  have hagreeAB : (hI.to A) ≫ f = (hI.to B) ≫ 𝟙 B := by
    have : (hI.to A) ≫ f = hI.to B := hI.hom_ext _ _
    rw [this, Category.comp_id]
  let ab_to_B : AB ⟶ B := hAB.desc f (𝟙 B) hagreeAB
  have hinlB : inlAB ≫ ab_to_B = f := hAB.inl_desc _ _ _
  have hinrB : inrAB ≫ ab_to_B = 𝟙 B := hAB.inr_desc _ _ _
  let ia_to_B : cylA.I ⟶ B := cylA.p ≫ f
  have hagreeP : cylA.c ≫ ia_to_B = m₀ ≫ ab_to_B := by
    apply cylA.isPushout.hom_ext
    · have e1 : cylA.j₀ ≫ (cylA.c ≫ ia_to_B) = f := by
        have hj0p : cylA.j₀ ≫ cylA.c ≫ cylA.p = 𝟙 A := cylA.j₀_c_p
        calc cylA.j₀ ≫ (cylA.c ≫ ia_to_B)
            = (cylA.j₀ ≫ cylA.c ≫ cylA.p) ≫ f := by
              simp [ia_to_B, Category.assoc]
          _ = 𝟙 A ≫ f := by rw [hj0p]
          _ = f := Category.id_comp _
      have e2 : cylA.j₀ ≫ (m₀ ≫ ab_to_B) = f := by
        calc cylA.j₀ ≫ (m₀ ≫ ab_to_B)
            = (cylA.j₀ ≫ m₀) ≫ ab_to_B := by rw [Category.assoc]
          _ = inlAB ≫ ab_to_B := by rw [hj₀]
          _ = f := hinlB
      rw [e1, e2]
    · have e1 : cylA.j₁ ≫ (cylA.c ≫ ia_to_B) = f := by
        have hj1p : cylA.j₁ ≫ cylA.c ≫ cylA.p = 𝟙 A := cylA.j₁_c_p
        calc cylA.j₁ ≫ (cylA.c ≫ ia_to_B)
            = (cylA.j₁ ≫ cylA.c ≫ cylA.p) ≫ f := by
              simp [ia_to_B, Category.assoc]
          _ = 𝟙 A ≫ f := by rw [hj1p]
          _ = f := Category.id_comp _
      have e2 : cylA.j₁ ≫ (m₀ ≫ ab_to_B) = f := by
        calc cylA.j₁ ≫ (m₀ ≫ ab_to_B)
            = (cylA.j₁ ≫ m₀) ≫ ab_to_B := by rw [Category.assoc]
          _ = (f ≫ inrAB) ≫ ab_to_B := by rw [hj₁]
          _ = f ≫ (inrAB ≫ ab_to_B) := by rw [← Category.assoc]
          _ = f ≫ 𝟙 B := by rw [hinrB]
          _ = f := Category.comp_id _
      rw [e1, e2]
  let p : Pobj ⟶ B := hP.desc ia_to_B ab_to_B hagreeP
  have hIA : inlIA ≫ p = ia_to_B := hP.inl_desc _ _ _
  have hABP : inrABP ≫ p = ab_to_B := hP.inr_desc _ _ _
  let s : B ⟶ Pobj := inrAB ≫ inrABP
  have hfac : i ≫ p = f := by
    simp only [i]
    rw [Category.assoc, hABP, hinlB]
  have hsec : s ≫ p = 𝟙 B := by
    simp only [s]
    rw [Category.assoc, hABP, hinrB]
  have hcof_inl : cofibrations C inlAB := by
    exact (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      (sq := hAB) (hf := hcofB)
  have hcof_inrAB : cofibrations C inrAB := by
    exact (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      (sq := hAB.flip) (hf := hcofA)
  have hcof_inrABP : cofibrations C inrABP := by
    exact (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      (sq := hP.flip) (hf := cylA.c_mem)
  have hcof_i : cofibrations C i := by
    simp only [i]
    exact IsCofibrationCategory.isMultiplicative.toIsStableUnderComposition.comp_mem
      _ _ hcof_inl hcof_inrABP
  have hcof_s : cofibrations C s := by
    simp only [s]
    exact IsCofibrationCategory.isMultiplicative.toIsStableUnderComposition.comp_mem
      _ _ hcof_inrAB hcof_inrABP
  -- key: s is the pushout of the trivial cofibration j₁≫c along f
  have hcomm_sq : (cylA.j₁ ≫ cylA.c) ≫ inlIA = f ≫ s := by
    calc (cylA.j₁ ≫ cylA.c) ≫ inlIA
        = cylA.j₁ ≫ (cylA.c ≫ inlIA) := Category.assoc _ _ _
      _ = cylA.j₁ ≫ (m₀ ≫ inrABP) := by rw [hP.w]
      _ = (cylA.j₁ ≫ m₀) ≫ inrABP := by rw [← Category.assoc]
      _ = (f ≫ inrAB) ≫ inrABP := by rw [hj₁]
      _ = f ≫ s := by simp [s, Category.assoc]
  have hQ : IsPushout (cylA.j₁ ≫ cylA.c) f inlIA s := by
    apply IsPushout.mk' hcomm_sq
    · -- uniqueness: φ, φ' agree on inlIA and s → equal
      intro T φ φ' hφ hφ'
      apply hP.hom_ext
      · exact hφ
      · apply hAB.hom_ext
        · calc inlAB ≫ (inrABP ≫ φ)
                = (cylA.j₀ ≫ m₀) ≫ (inrABP ≫ φ) := by rw [← hj₀]
              _ = cylA.j₀ ≫ (m₀ ≫ (inrABP ≫ φ)) := by
                  simp only [Category.assoc]
              _ = cylA.j₀ ≫ ((m₀ ≫ inrABP) ≫ φ) := by
                  rw [← Category.assoc m₀ inrABP φ]
              _ = cylA.j₀ ≫ ((cylA.c ≫ inlIA) ≫ φ) := by rw [← hP.w]
              _ = (cylA.j₀ ≫ cylA.c) ≫ (inlIA ≫ φ) := by
                  simp only [Category.assoc]
              _ = (cylA.j₀ ≫ cylA.c) ≫ (inlIA ≫ φ') := by rw [hφ]
              _ = cylA.j₀ ≫ ((cylA.c ≫ inlIA) ≫ φ') := by
                  simp only [← Category.assoc]
              _ = cylA.j₀ ≫ ((m₀ ≫ inrABP) ≫ φ') := by rw [hP.w]
              _ = (cylA.j₀ ≫ m₀) ≫ (inrABP ≫ φ') := by
                  simp only [Category.assoc]
              _ = inlAB ≫ (inrABP ≫ φ') := by rw [hj₀]
        · calc inrAB ≫ (inrABP ≫ φ)
              = (inrAB ≫ inrABP) ≫ φ := by rw [Category.assoc]
            _ = s ≫ φ := rfl
            _ = s ≫ φ' := hφ'
            _ = (inrAB ≫ inrABP) ≫ φ' := rfl
            _ = inrAB ≫ (inrABP ≫ φ') := by rw [← Category.assoc]
    · -- existence: given a, b with (j₁≫c)≫a = f≫b, find l
      intro T a b hab
      let a₀ : A ⟶ T := (cylA.j₀ ≫ cylA.c) ≫ a
      have hABcond : (hI.to A) ≫ a₀ = (hI.to B) ≫ b := by
        have hj : (hI.to A) ≫ cylA.j₀ = (hI.to A) ≫ cylA.j₁ :=
          cylA.isPushout.w
        have hfI : (hI.to A) ≫ f = hI.to B := hI.hom_ext _ _
        -- normalize to expose (hI.to A ≫ j₀) pattern
        have e1 : (hI.to A) ≫ a₀ = (((hI.to A) ≫ cylA.j₀) ≫ cylA.c) ≫ a := by
          simp only [a₀, Category.assoc]
        have e2 : (((hI.to A) ≫ cylA.j₁) ≫ cylA.c) ≫ a
            = (hI.to A) ≫ ((cylA.j₁ ≫ cylA.c) ≫ a) := by
          simp only [Category.assoc]
        calc (hI.to A) ≫ a₀
            = (((hI.to A) ≫ cylA.j₀) ≫ cylA.c) ≫ a := e1
          _ = (((hI.to A) ≫ cylA.j₁) ≫ cylA.c) ≫ a := by rw [hj]
          _ = (hI.to A) ≫ ((cylA.j₁ ≫ cylA.c) ≫ a) := e2
          _ = (hI.to A) ≫ (f ≫ b) := by rw [hab]
          _ = ((hI.to A) ≫ f) ≫ b := by rw [← Category.assoc]
          _ = (hI.to B) ≫ b := by rw [hfI]
      let abW : AB ⟶ T := hAB.desc a₀ b hABcond
      have hab_inl : inlAB ≫ abW = a₀ := hAB.inl_desc _ _ _
      have hab_inr : inrAB ≫ abW = b := hAB.inr_desc _ _ _
      have hPcond : cylA.c ≫ a = m₀ ≫ abW := by
        apply cylA.isPushout.hom_ext
        · have e1 : cylA.j₀ ≫ (cylA.c ≫ a) = a₀ := by
            simp only [a₀, ← Category.assoc]
          have e2 : cylA.j₀ ≫ (m₀ ≫ abW) = a₀ := by
            calc cylA.j₀ ≫ (m₀ ≫ abW)
                = (cylA.j₀ ≫ m₀) ≫ abW := by rw [← Category.assoc]
              _ = inlAB ≫ abW := by rw [hj₀]
              _ = a₀ := hab_inl
          rw [e1, e2]
        · have e1 : cylA.j₁ ≫ (cylA.c ≫ a) = f ≫ b := by
            calc cylA.j₁ ≫ (cylA.c ≫ a)
                = (cylA.j₁ ≫ cylA.c) ≫ a := by rw [← Category.assoc]
              _ = f ≫ b := hab
          have e2 : cylA.j₁ ≫ (m₀ ≫ abW) = f ≫ b := by
            calc cylA.j₁ ≫ (m₀ ≫ abW)
                = (cylA.j₁ ≫ m₀) ≫ abW := by rw [← Category.assoc]
              _ = (f ≫ inrAB) ≫ abW := by rw [hj₁]
              _ = f ≫ (inrAB ≫ abW) := by rw [← Category.assoc]
              _ = f ≫ b := by rw [hab_inr]
          rw [e1, e2]
      refine ⟨hP.desc a abW hPcond, hP.inl_desc _ _ _, ?_⟩
      calc s ≫ hP.desc a abW hPcond
          = (inrAB ≫ inrABP) ≫ hP.desc a abW hPcond := rfl
        _ = inrAB ≫ (inrABP ≫ hP.desc a abW hPcond) := by
            rw [← Category.assoc]
        _ = inrAB ≫ abW := by rw [hP.inr_desc]
        _ = b := hab_inr
  have hwe_s : weakEquivalences C s := by
    have := IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      (cylA.j₁ ≫ cylA.c) f inlIA s hQ hcof_j₁c hwe_j₁c
    exact this
  have hwe_p : weakEquivalences C p := by
    have hid : weakEquivalences C (𝟙 B) := we_id B
    have hsec' : weakEquivalences C (s ≫ p) := by
      rw [hsec]
      exact hid
    exact MorphismProperty.of_precomp (weakEquivalences C) _ _ hwe_s hsec'
  exact ⟨⟨Pobj, i, p, s, hfac, hsec, hcof_i, hwe_p, hcof_s, hwe_s⟩⟩

end HomotopyHypothesis.Cylinder.PreCylinderCategory
