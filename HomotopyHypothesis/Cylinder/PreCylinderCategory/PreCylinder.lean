import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Cylinder.PreCylinderCategory.Basic
import HomotopyHypothesis.Cylinder.PreCylinderCategory.Brown
import HomotopyHypothesis.Cylinder.PreCylinderCategory.CobaseChange
set_option linter.style.haveILetI false

namespace HomotopyHypothesis.Cylinder.PreCylinderCategory

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe v u

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]

/-- H Prop 2.2.12 (H:722), the gluing (cube) lemma: a cylinder category is a pre-cylinder category. -/
theorem isPreCylinderCategory_proof [IsCylinderCategory C] :
    IsPreCylinderCategory C := by
  haveI := we_twoOutOfThree (C := C)
  refine {
    isomorphisms_le_weakEquivalences := IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C)
    weakEquivalences_isMultiplicative := IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)
    twoOutOfSix := IsCylinderCategory.twoOutOfSix (C := C)
    gluing := ?_
  }
  intro A B X P A' B' X' P' i f k j i' f' k' j' vA vB vX φ h h' hi hi' hwe_vA hwe_vB hwe_vX hivB hfv hkφ hjφ

  -- 1. Brown factorization of f : A ⟶ X into cofibration iD and weak equivalence wD
  obtain ⟨bf⟩ := brown_factorization (C := C) f
  let D := bf.P
  let iD : A ⟶ D := bf.i
  let wD : D ⟶ X := bf.p
  have hcof_iD : cofibrations C iD := bf.cof_i
  have hwe_wD : weakEquivalences C wD := bf.we_p
  have hfac : iD ≫ wD = f := bf.fac

  -- 2. D' = pushout iD vA
  haveI : HasPushout iD vA := IsCofibrationCategory.hasPushout _ _ hcof_iD
  let D' := pushout iD vA
  let inD : D ⟶ D' := pushout.inl _ _
  let inA' : A' ⟶ D' := pushout.inr _ _
  let hD' : IsPushout iD vA inD inA' := IsPushout.of_hasPushout _ _
  have hcof_inA' : cofibrations C inA' :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      (sq := hD'.flip) (hf := hcof_iD)
  have hwe_inD : weakEquivalences C inD :=
    weakEquivalence_cobaseChange_proof iD vA inD inA' hD' hcof_iD hwe_vA

  -- 3. Factorization of f' through D'
  have hagree_wD' : iD ≫ (wD ≫ vX) = vA ≫ f' := by
    calc iD ≫ (wD ≫ vX) = (iD ≫ wD) ≫ vX := by rw [← Category.assoc]
      _ = f ≫ vX := by rw [hfac]
      _ = vA ≫ f' := hfv
  let wD' : D' ⟶ X' := hD'.desc (wD ≫ vX) f' hagree_wD'
  have hwD'_inD : inD ≫ wD' = wD ≫ vX := hD'.inl_desc _ _ _
  have hwD'_inA' : inA' ≫ wD' = f' := hD'.inr_desc _ _ _
  have hwe_wDvX : weakEquivalences C (wD ≫ vX) :=
    IsCylinderCategory.weakEquivalences_isMultiplicative.toIsStableUnderComposition.comp_mem
      _ _ hwe_wD hwe_vX
  have hwe_wD' : weakEquivalences C wD' :=
    MorphismProperty.of_precomp (weakEquivalences C) inD wD' hwe_inD (by
      rw [hwD'_inD]
      exact hwe_wDvX)

  -- 4. PD = pushout i iD
  haveI : HasPushout i iD := IsCofibrationCategory.hasPushout _ _ hi
  let PD := pushout i iD
  let inB_PD : B ⟶ PD := pushout.inl _ _
  let inD_PD : D ⟶ PD := pushout.inr _ _
  let hPD : IsPushout i iD inB_PD inD_PD := IsPushout.of_hasPushout _ _
  have hcof_inD_PD : cofibrations C inD_PD :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      (sq := hPD.flip) (hf := hi)
  have hcof_inB_PD : cofibrations C inB_PD :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      (sq := hPD) (hf := hcof_iD)

  -- 5. θ : PD ⟶ P is pushout of wD along inD_PD
  have hagree_θ : i ≫ k = iD ≫ (wD ≫ j) := by
    calc i ≫ k = f ≫ j := h.w
      _ = (iD ≫ wD) ≫ j := by rw [← hfac]
      _ = iD ≫ (wD ≫ j) := by rw [Category.assoc]
  let θ : PD ⟶ P := hPD.desc k (wD ≫ j) hagree_θ
  have hθ_inB : inB_PD ≫ θ = k := hPD.inl_desc _ _ _
  have hθ_inD : inD_PD ≫ θ = wD ≫ j := hPD.inr_desc _ _ _
  have hθ_push : IsPushout wD inD_PD j θ := by
    apply IsPushout.mk' hθ_inD.symm
    · intro T φ₁ φ₂ hφ₁ hφ₂
      apply h.hom_ext
      · calc k ≫ φ₁ = (inB_PD ≫ θ) ≫ φ₁ := by rw [hθ_inB]
          _ = inB_PD ≫ (θ ≫ φ₁) := by rw [Category.assoc]
          _ = inB_PD ≫ (θ ≫ φ₂) := by rw [hφ₂]
          _ = (inB_PD ≫ θ) ≫ φ₂ := by rw [← Category.assoc]
          _ = k ≫ φ₂ := by rw [hθ_inB]
      · exact hφ₁
    · intro T a b hab
      have hagP : i ≫ (inB_PD ≫ b) = f ≫ a := by
        calc i ≫ (inB_PD ≫ b) = (i ≫ inB_PD) ≫ b := by rw [← Category.assoc]
          _ = (iD ≫ inD_PD) ≫ b := by rw [hPD.w]
          _ = iD ≫ (inD_PD ≫ b) := by rw [Category.assoc]
          _ = iD ≫ (wD ≫ a) := by rw [← hab]
          _ = (iD ≫ wD) ≫ a := by rw [← Category.assoc]
          _ = f ≫ a := by rw [hfac]
      let l : P ⟶ T := h.desc (inB_PD ≫ b) a hagP
      have hl_k : k ≫ l = inB_PD ≫ b := h.inl_desc _ _ _
      have hl_j : j ≫ l = a := h.inr_desc _ _ _
      refine ⟨l, hl_j, ?_⟩
      apply hPD.hom_ext
      · calc inB_PD ≫ (θ ≫ l) = (inB_PD ≫ θ) ≫ l := by rw [Category.assoc]
          _ = k ≫ l := by rw [hθ_inB]
          _ = inB_PD ≫ b := hl_k
      · calc inD_PD ≫ (θ ≫ l) = (inD_PD ≫ θ) ≫ l := by rw [Category.assoc]
          _ = (wD ≫ j) ≫ l := by rw [hθ_inD]
          _ = wD ≫ (j ≫ l) := by rw [Category.assoc]
          _ = wD ≫ a := by rw [hl_j]
          _ = inD_PD ≫ b := hab
  have hwe_θ : weakEquivalences C θ :=
    weakEquivalence_cobaseChange_proof inD_PD wD θ j hθ_push.flip hcof_inD_PD hwe_wD

  -- 6. PD' = pushout i' inA'
  haveI : HasPushout i' inA' := IsCofibrationCategory.hasPushout _ _ hi'
  let PD' := pushout i' inA'
  let inB'_PD' : B' ⟶ PD' := pushout.inl _ _
  let inD'_PD' : D' ⟶ PD' := pushout.inr _ _
  let hPD' : IsPushout i' inA' inB'_PD' inD'_PD' := IsPushout.of_hasPushout _ _
  have hcof_inD'_PD' : cofibrations C inD'_PD' :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      (sq := hPD'.flip) (hf := hi')

  -- 7. θ' : PD' ⟶ P' is pushout of wD' along inD'_PD'
  have hagree_θ' : i' ≫ k' = inA' ≫ (wD' ≫ j') := by
    calc i' ≫ k' = f' ≫ j' := h'.w
      _ = (inA' ≫ wD') ≫ j' := by rw [← hwD'_inA']
      _ = inA' ≫ (wD' ≫ j') := by rw [Category.assoc]
  let θ' : PD' ⟶ P' := hPD'.desc k' (wD' ≫ j') hagree_θ'
  have hθ'_inB' : inB'_PD' ≫ θ' = k' := hPD'.inl_desc _ _ _
  have hθ'_inD' : inD'_PD' ≫ θ' = wD' ≫ j' := hPD'.inr_desc _ _ _
  have hθ'_push : IsPushout wD' inD'_PD' j' θ' := by
    apply IsPushout.mk' hθ'_inD'.symm
    · intro T φ₁ φ₂ hφ₁ hφ₂
      apply h'.hom_ext
      · calc k' ≫ φ₁ = (inB'_PD' ≫ θ') ≫ φ₁ := by rw [hθ'_inB']
          _ = inB'_PD' ≫ (θ' ≫ φ₁) := by rw [Category.assoc]
          _ = inB'_PD' ≫ (θ' ≫ φ₂) := by rw [hφ₂]
          _ = (inB'_PD' ≫ θ') ≫ φ₂ := by rw [← Category.assoc]
          _ = k' ≫ φ₂ := by rw [hθ'_inB']
      · exact hφ₁
    · intro T a b hab
      have hagP' : i' ≫ (inB'_PD' ≫ b) = f' ≫ a := by
        calc i' ≫ (inB'_PD' ≫ b) = (i' ≫ inB'_PD') ≫ b := by rw [← Category.assoc]
          _ = (inA' ≫ inD'_PD') ≫ b := by rw [hPD'.w]
          _ = inA' ≫ (inD'_PD' ≫ b) := by rw [Category.assoc]
          _ = inA' ≫ (wD' ≫ a) := by rw [← hab]
          _ = (inA' ≫ wD') ≫ a := by rw [← Category.assoc]
          _ = f' ≫ a := by rw [hwD'_inA']
      let l : P' ⟶ T := h'.desc (inB'_PD' ≫ b) a hagP'
      have hl_k' : k' ≫ l = inB'_PD' ≫ b := h'.inl_desc _ _ _
      have hl_j' : j' ≫ l = a := h'.inr_desc _ _ _
      refine ⟨l, hl_j', ?_⟩
      apply hPD'.hom_ext
      · calc inB'_PD' ≫ (θ' ≫ l) = (inB'_PD' ≫ θ') ≫ l := by rw [Category.assoc]
          _ = k' ≫ l := by rw [hθ'_inB']
          _ = inB'_PD' ≫ b := hl_k'
      · calc inD'_PD' ≫ (θ' ≫ l) = (inD'_PD' ≫ θ') ≫ l := by rw [Category.assoc]
          _ = (wD' ≫ j') ≫ l := by rw [hθ'_inD']
          _ = wD' ≫ (j' ≫ l) := by rw [Category.assoc]
          _ = wD' ≫ a := by rw [hl_j']
          _ = inD'_PD' ≫ b := hab
  have hwe_θ' : weakEquivalences C θ' :=
    weakEquivalence_cobaseChange_proof inD'_PD' wD' θ' j' hθ'_push.flip hcof_inD'_PD' hwe_wD'

  -- 8. ϕ : PD ⟶ PD' is pushout of vB along inB_PD
  have hagree_ϕ : i ≫ (vB ≫ inB'_PD') = iD ≫ (inD ≫ inD'_PD') := by
    calc i ≫ (vB ≫ inB'_PD') = (i ≫ vB) ≫ inB'_PD' := by rw [← Category.assoc]
      _ = (vA ≫ i') ≫ inB'_PD' := by rw [hivB]
      _ = vA ≫ (i' ≫ inB'_PD') := by rw [Category.assoc]
      _ = vA ≫ (inA' ≫ inD'_PD') := by rw [hPD'.w]
      _ = (vA ≫ inA') ≫ inD'_PD' := by rw [← Category.assoc]
      _ = (iD ≫ inD) ≫ inD'_PD' := by rw [hD'.w]
      _ = iD ≫ (inD ≫ inD'_PD') := by rw [Category.assoc]
  let ϕ : PD ⟶ PD' := hPD.desc (vB ≫ inB'_PD') (inD ≫ inD'_PD') hagree_ϕ
  have hϕ_inB : inB_PD ≫ ϕ = vB ≫ inB'_PD' := hPD.inl_desc _ _ _
  have hϕ_inD : inD_PD ≫ ϕ = inD ≫ inD'_PD' := hPD.inr_desc _ _ _
  have hϕ_push : IsPushout vB inB_PD inB'_PD' ϕ := by
    apply IsPushout.mk' hϕ_inB.symm
    · intro T φ₁ φ₂ hφ₁ hφ₂
      apply hPD'.hom_ext
      · exact hφ₁
      · apply hD'.hom_ext
        · calc inD ≫ inD'_PD' ≫ φ₁ = (inD ≫ inD'_PD') ≫ φ₁ := by rw [Category.assoc]
            _ = (inD_PD ≫ ϕ) ≫ φ₁ := by rw [hϕ_inD]
            _ = inD_PD ≫ (ϕ ≫ φ₁) := by rw [Category.assoc]
            _ = inD_PD ≫ (ϕ ≫ φ₂) := by rw [hφ₂]
            _ = (inD_PD ≫ ϕ) ≫ φ₂ := by rw [← Category.assoc]
            _ = (inD ≫ inD'_PD') ≫ φ₂ := by rw [← hϕ_inD]
            _ = inD ≫ inD'_PD' ≫ φ₂ := by rw [Category.assoc]
        · calc inA' ≫ inD'_PD' ≫ φ₁ = (inA' ≫ inD'_PD') ≫ φ₁ := by rw [Category.assoc]
            _ = (i' ≫ inB'_PD') ≫ φ₁ := by rw [hPD'.w]
            _ = i' ≫ (inB'_PD' ≫ φ₁) := by rw [Category.assoc]
            _ = i' ≫ (inB'_PD' ≫ φ₂) := by rw [hφ₁]
            _ = (i' ≫ inB'_PD') ≫ φ₂ := by rw [← Category.assoc]
            _ = (inA' ≫ inD'_PD') ≫ φ₂ := by rw [← hPD'.w]
            _ = inA' ≫ inD'_PD' ≫ φ₂ := by rw [Category.assoc]
    · intro T a b hab
      have hagD' : iD ≫ (inD_PD ≫ b) = vA ≫ (i' ≫ a) := by
        calc iD ≫ (inD_PD ≫ b) = (iD ≫ inD_PD) ≫ b := by rw [← Category.assoc]
          _ = (i ≫ inB_PD) ≫ b := by rw [← hPD.w]
          _ = i ≫ (inB_PD ≫ b) := by rw [Category.assoc]
          _ = i ≫ (vB ≫ a) := by rw [← hab]
          _ = (i ≫ vB) ≫ a := by rw [← Category.assoc]
          _ = (vA ≫ i') ≫ a := by rw [hivB]
          _ = vA ≫ (i' ≫ a) := by rw [Category.assoc]
      let lD' : D' ⟶ T := hD'.desc (inD_PD ≫ b) (i' ≫ a) hagD'
      have hlD'_inD : inD ≫ lD' = inD_PD ≫ b := hD'.inl_desc _ _ _
      have hlD'_inA' : inA' ≫ lD' = i' ≫ a := hD'.inr_desc _ _ _
      have hagPD' : i' ≫ a = inA' ≫ lD' := hlD'_inA'.symm
      let l : PD' ⟶ T := hPD'.desc a lD' hagPD'
      have hl_inB' : inB'_PD' ≫ l = a := hPD'.inl_desc _ _ _
      have hl_inD' : inD'_PD' ≫ l = lD' := hPD'.inr_desc _ _ _
      refine ⟨l, hl_inB', ?_⟩
      apply hPD.hom_ext
      · calc inB_PD ≫ (ϕ ≫ l) = (inB_PD ≫ ϕ) ≫ l := by rw [Category.assoc]
          _ = (vB ≫ inB'_PD') ≫ l := by rw [hϕ_inB]
          _ = vB ≫ (inB'_PD' ≫ l) := by rw [Category.assoc]
          _ = vB ≫ a := by rw [hl_inB']
          _ = inB_PD ≫ b := hab
      · calc inD_PD ≫ (ϕ ≫ l) = (inD_PD ≫ ϕ) ≫ l := by rw [Category.assoc]
          _ = (inD ≫ inD'_PD') ≫ l := by rw [hϕ_inD]
          _ = inD ≫ (inD'_PD' ≫ l) := by rw [Category.assoc]
          _ = inD ≫ lD' := by rw [hl_inD']
          _ = inD_PD ≫ b := hlD'_inD
  have hwe_ϕ : weakEquivalences C ϕ :=
    weakEquivalence_cobaseChange_proof inB_PD vB ϕ inB'_PD' hϕ_push.flip hcof_inB_PD hwe_vB

  -- 9. θ ≫ φ = ϕ ≫ θ'
  have hcomm_square : θ ≫ φ = ϕ ≫ θ' := by
    apply hPD.hom_ext
    · calc inB_PD ≫ (θ ≫ φ) = (inB_PD ≫ θ) ≫ φ := by rw [Category.assoc]
        _ = k ≫ φ := by rw [hθ_inB]
        _ = vB ≫ k' := hkφ
        _ = vB ≫ (inB'_PD' ≫ θ') := by rw [← hθ'_inB']
        _ = (vB ≫ inB'_PD') ≫ θ' := by rw [← Category.assoc]
        _ = (inB_PD ≫ ϕ) ≫ θ' := by rw [← hϕ_inB]
        _ = inB_PD ≫ (ϕ ≫ θ') := by rw [Category.assoc]
    · calc inD_PD ≫ (θ ≫ φ) = (inD_PD ≫ θ) ≫ φ := by rw [Category.assoc]
        _ = (wD ≫ j) ≫ φ := by rw [hθ_inD]
        _ = wD ≫ (j ≫ φ) := by rw [Category.assoc]
        _ = wD ≫ (vX ≫ j') := by rw [hjφ]
        _ = (wD ≫ vX) ≫ j' := by rw [← Category.assoc]
        _ = (inD ≫ wD') ≫ j' := by rw [← hwD'_inD]
        _ = inD ≫ (wD' ≫ j') := by rw [Category.assoc]
        _ = inD ≫ (inD'_PD' ≫ θ') := by rw [← hθ'_inD']
        _ = (inD ≫ inD'_PD') ≫ θ' := by rw [← Category.assoc]
        _ = (inD_PD ≫ ϕ) ≫ θ' := by rw [← hϕ_inD]
        _ = inD_PD ≫ (ϕ ≫ θ') := by rw [Category.assoc]

  -- 10. Conclusion by 2-out-of-3
  have hwe_ϕθ' : weakEquivalences C (ϕ ≫ θ') :=
    IsCylinderCategory.weakEquivalences_isMultiplicative.toIsStableUnderComposition.comp_mem
      _ _ hwe_ϕ hwe_θ'
  have hwe_θφ : weakEquivalences C (θ ≫ φ) := by
    rw [hcomm_square]
    exact hwe_ϕθ'
  exact MorphismProperty.of_precomp (weakEquivalences C) θ φ hwe_θ hwe_θφ

#print axioms isPreCylinderCategory_proof

end HomotopyHypothesis.Cylinder.PreCylinderCategory
