import HomotopyHypothesis.Cylinder.SimplicialCategory.Cofibrations
import HomotopyHypothesis.Cylinder.SimplicialCategory.FreeAlgKan
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexSubfunctors
import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.Classical.FinCellIsCylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.Classical.IsCylinderMorphismToFinCell
import HomotopyHypothesis.Blueprint.Henry.Packages.General.RelHomotopicEquivalence
import HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial.ExistsStandardRealization
import HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial.StandardRealizationIsHomotopyFullyFaithful
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.FinCellHomotopicRelIff
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.RelativeLiftOfHomotopyEquivalence
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Cylinder.SemisimplicialCategory.CylinderAssembly
import HomotopyHypothesis.Cylinder.SemisimplicialCategory.WeakEquivalences
/-!
# The cylinder category structure on `C^Δ`

This file constructs relative cylinders for the cell boundary inclusions `∂Δ_n ⟶ Δ_n` in `CDelta`,
proves the boundary test lifting property and extension of finite factorizations along cofibrations,
and proves that `CDelta` is a cylinder category.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Cylinder.SimplicialCategory

open HomotopyHypothesis.Henry

instance : (cofibrations CDelta.{u}).IsMultiplicative :=
  cDelta_isCofibrationCategory.isMultiplicative

instance : (cofibrations CDelta.{u}).IsStableUnderCobaseChange :=
  cDelta_isCofibrationCategory.isStableUnderCobaseChange

lemma cDelta_weakEquivalence_id (X : CDelta.{u}) :
    weakEquivalences CDelta.{u} (𝟙 X) :=
  Cylinder.SemisimplicialCategory.cDelta_weakEquivalences_isWeakEquivalenceClass.1 _
    (MorphismProperty.isomorphisms.infer_property (𝟙 X))

lemma cDelta_weakEquivalence_comp {X Y Z : CDelta.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : weakEquivalences CDelta.{u} f) (hg : weakEquivalences CDelta.{u} g) :
    weakEquivalences CDelta.{u} (f ≫ g) :=
  Cylinder.SemisimplicialCategory.cDelta_weakEquivalences_isWeakEquivalenceClass.2.1.comp_mem f g hf hg

/-!
## Relative cylinders for the cell boundary inclusions `∂Δ_n ⟶ Δ_n`
-/

/-- The `(n+1)`-th face inclusion `Δ_n ⟶ Δ_{n+1}` in `CDelta`. -/
noncomputable def stdSimplexFaceLastCDelta (n : ℕ) :
    stdSimplexCDelta.{u} n ⟶ stdSimplexCDelta.{u} (n + 1) :=
  stdSimplexToBoundarySucc.{u} n ≫ boundaryCDeltaInclusion.{u} (n + 1)

/-- The `(n+1)`-th horn inclusion `Λ^{n+1}_{n+1} ⟶ Δ_{n+1}` in `CDelta`. -/
noncomputable def hornLastInclusionCDelta (n : ℕ) :
    hornCDelta.{u} n (Fin.last (n + 1)) ⟶ stdSimplexCDelta.{u} (n + 1) :=
  hornLastToBoundarySucc.{u} n ≫ boundaryCDeltaInclusion.{u} (n + 1)

lemma stdSimplexFaceLastCDelta_cofibration (n : ℕ) :
    cofibrations CDelta.{u} (stdSimplexFaceLastCDelta.{u} n) :=
  (cofibrations CDelta.{u}).comp_mem _ _
    (stdSimplexToBoundarySucc_cofibration n)
    (boundaryCDeltaInclusion_cofibration (n + 1))

lemma stdSimplexFaceLastCDelta_weakEquivalence (n : ℕ) :
    weakEquivalences CDelta.{u} (stdSimplexFaceLastCDelta.{u} n) :=
  stdSimplexToBoundarySucc_comp_inclusion_weakEquivalence n

lemma hornLastInclusionCDelta_cofibration (n : ℕ) :
    cofibrations CDelta.{u} (hornLastInclusionCDelta.{u} n) :=
  (cofibrations CDelta.{u}).comp_mem _ _
    (hornLastToBoundarySucc_cofibration n)
    (boundaryCDeltaInclusion_cofibration (n + 1))

lemma hornLastInclusionCDelta_weakEquivalence (n : ℕ) :
    weakEquivalences CDelta.{u} (hornLastInclusionCDelta.{u} n) :=
  hornLastToBoundarySucc_comp_inclusion_weakEquivalence n

lemma boundary_comp_stdSimplexFaceLastCDelta (n : ℕ) :
    boundaryCDeltaInclusion.{u} n ≫ stdSimplexFaceLastCDelta.{u} n =
      boundaryToHornLast.{u} n ≫ hornLastInclusionCDelta.{u} n := by
  dsimp [stdSimplexFaceLastCDelta, hornLastInclusionCDelta]
  rw [← Category.assoc, (isPushout_boundary_horn.{u} n).w, Category.assoc]

/-- Existence of a relative cylinder for `boundaryCDeltaInclusion n : ∂Δ_n ⟶ Δ_n` whose first leg
`j₀ ≫ c : Δ_n ⟶ I` is a trivial cofibration. -/
theorem exists_boundary_relativeCylinder (n : ℕ) :
    ∃ cyl : RelativeCylinder (boundaryCDeltaInclusion.{u} n),
      cofibrations CDelta.{u} (cyl.j₀ ≫ cyl.c) ∧
        weakEquivalences CDelta.{u} (cyl.j₀ ≫ cyl.c) := by
  let I_n := boundaryCDeltaInclusion.{u} n
  let I_succ := boundaryCDeltaInclusion.{u} (n + 1)
  let i_Λ := boundaryToHornLast.{u} n
  let s_bd := stdSimplexToBoundarySucc.{u} n
  let h_bd := hornLastToBoundarySucc.{u} n
  let h_face := stdSimplexFaceLastCDelta.{u} n
  let h_horn := hornLastInclusionCDelta.{u} n
  have hI_n : cofibrations CDelta.{u} I_n := boundaryCDeltaInclusion_cofibration n
  have hI_succ : cofibrations CDelta.{u} I_succ := boundaryCDeltaInclusion_cofibration (n + 1)
  have hi_Λ : cofibrations CDelta.{u} i_Λ := boundaryToHornLast_cofibration n
  have sq_bh : IsPushout I_n i_Λ s_bd h_bd := isPushout_boundary_horn n
  -- Step 1: Pushout M = Δ_n ⊔_{∂Δ_n} Δ_n
  have : HasPushout I_n I_n := cDelta_isCofibrationCategory.hasPushout I_n I_n hI_n
  let M : CDelta.{u} := pushout I_n I_n
  let inl_M : stdSimplexCDelta.{u} n ⟶ M := pushout.inl I_n I_n
  let inr_M : stdSimplexCDelta.{u} n ⟶ M := pushout.inr I_n I_n
  have sqM : IsPushout I_n I_n inl_M inr_M := IsPushout.of_hasPushout I_n I_n
  -- Step 2: Pushout M₁ = Λ^{n+1}_{n+1} ⊔_{∂Δ_n} M
  have : HasPushout i_Λ (I_n ≫ inl_M) :=
    cDelta_isCofibrationCategory.hasPushout i_Λ (I_n ≫ inl_M) hi_Λ
  let M₁ : CDelta.{u} := pushout i_Λ (I_n ≫ inl_M)
  let v_Λ : hornCDelta.{u} n (Fin.last (n + 1)) ⟶ M₁ := pushout.inl i_Λ (I_n ≫ inl_M)
  let c₀ : M ⟶ M₁ := pushout.inr i_Λ (I_n ≫ inl_M)
  have sq₁ : IsPushout i_Λ (I_n ≫ inl_M) v_Λ c₀ := IsPushout.of_hasPushout _ _
  have hc₀ : cofibrations CDelta.{u} c₀ := (cofibrations CDelta.{u}).of_isPushout sq₁.flip hi_Λ
  -- Induced maps u₀, u₁ : ∂Δ_{n+1} ⟶ M₁
  have hu₀_comm : I_n ≫ (inl_M ≫ c₀) = i_Λ ≫ v_Λ := by
    rw [← Category.assoc, sq₁.w]
  let u₀ : boundaryCDelta.{u} (n + 1) ⟶ M₁ := sq_bh.desc (inl_M ≫ c₀) v_Λ hu₀_comm
  have hu₀_s : s_bd ≫ u₀ = inl_M ≫ c₀ := sq_bh.inl_desc _ _ _
  have hu₀_h : h_bd ≫ u₀ = v_Λ := sq_bh.inr_desc _ _ _
  have hu₁_comm : I_n ≫ (inr_M ≫ c₀) = i_Λ ≫ v_Λ := by
    rw [← Category.assoc, ← sqM.w, sq₁.w]
  let u₁ : boundaryCDelta.{u} (n + 1) ⟶ M₁ := sq_bh.desc (inr_M ≫ c₀) v_Λ hu₁_comm
  have hu₁_s : s_bd ≫ u₁ = inr_M ≫ c₀ := sq_bh.inl_desc _ _ _
  have hu₁_h : h_bd ≫ u₁ = v_Λ := sq_bh.inr_desc _ _ _
  -- Step 3: Pushout M₂ = Δ_{n+1} ⊔_{∂Δ_{n+1}} M₁ along u₀
  have : HasPushout I_succ u₀ := cDelta_isCofibrationCategory.hasPushout I_succ u₀ hI_succ
  let M₂ : CDelta.{u} := pushout I_succ u₀
  let w₀ : stdSimplexCDelta.{u} (n + 1) ⟶ M₂ := pushout.inl I_succ u₀
  let c₁ : M₁ ⟶ M₂ := pushout.inr I_succ u₀
  have sq₂ : IsPushout I_succ u₀ w₀ c₁ := IsPushout.of_hasPushout _ _
  have hc₁ : cofibrations CDelta.{u} c₁ := (cofibrations CDelta.{u}).of_isPushout sq₂.flip hI_succ
  -- Step 4: Pushout CM = Δ_{n+1} ⊔_{∂Δ_{n+1}} M₂ along u₁ ≫ c₁
  have : HasPushout I_succ (u₁ ≫ c₁) :=
    cDelta_isCofibrationCategory.hasPushout I_succ (u₁ ≫ c₁) hI_succ
  let CM : CDelta.{u} := pushout I_succ (u₁ ≫ c₁)
  let w₁ : stdSimplexCDelta.{u} (n + 1) ⟶ CM := pushout.inl I_succ (u₁ ≫ c₁)
  let c₂ : M₂ ⟶ CM := pushout.inr I_succ (u₁ ≫ c₁)
  have sq₃ : IsPushout I_succ (u₁ ≫ c₁) w₁ c₂ := IsPushout.of_hasPushout _ _
  have hc₂ : cofibrations CDelta.{u} c₂ := (cofibrations CDelta.{u}).of_isPushout sq₃.flip hI_succ
  let c : M ⟶ CM := c₀ ≫ c₁ ≫ c₂
  have hc : cofibrations CDelta.{u} c :=
    (cofibrations CDelta.{u}).comp_mem _ _ hc₀ ((cofibrations CDelta.{u}).comp_mem _ _ hc₁ hc₂)
  -- Compatibility relations in CM
  have hinl_c : inl_M ≫ c = h_face ≫ (w₀ ≫ c₂) := by
    calc inl_M ≫ c₀ ≫ c₁ ≫ c₂
      _ = (inl_M ≫ c₀) ≫ c₁ ≫ c₂ := (Category.assoc _ _ _).symm
      _ = (s_bd ≫ u₀) ≫ c₁ ≫ c₂ := by rw [hu₀_s]
      _ = s_bd ≫ (u₀ ≫ c₁) ≫ c₂ := by simp only [Category.assoc]
      _ = s_bd ≫ (I_succ ≫ w₀) ≫ c₂ := by rw [sq₂.w]
      _ = h_face ≫ (w₀ ≫ c₂) := by
          simp only [h_face, stdSimplexFaceLastCDelta, s_bd, I_succ, Category.assoc]
  have hinr_c : inr_M ≫ c = h_face ≫ w₁ := by
    calc inr_M ≫ c₀ ≫ c₁ ≫ c₂
      _ = (inr_M ≫ c₀) ≫ c₁ ≫ c₂ := (Category.assoc _ _ _).symm
      _ = (s_bd ≫ u₁) ≫ c₁ ≫ c₂ := by rw [hu₁_s]
      _ = s_bd ≫ (u₁ ≫ c₁) ≫ c₂ := by simp only [Category.assoc]
      _ = s_bd ≫ I_succ ≫ w₁ := by rw [← sq₃.w]
      _ = h_face ≫ w₁ := by
          simp only [h_face, stdSimplexFaceLastCDelta, s_bd, I_succ, Category.assoc]
  have hv_c : v_Λ ≫ c₁ ≫ c₂ = h_horn ≫ (w₀ ≫ c₂) := by
    calc v_Λ ≫ c₁ ≫ c₂
      _ = (h_bd ≫ u₀) ≫ c₁ ≫ c₂ := by rw [hu₀_h]
      _ = h_bd ≫ (u₀ ≫ c₁) ≫ c₂ := by simp only [Category.assoc]
      _ = h_bd ≫ (I_succ ≫ w₀) ≫ c₂ := by rw [sq₂.w]
      _ = h_horn ≫ (w₀ ≫ c₂) := by
          simp only [h_horn, hornLastInclusionCDelta, h_bd, I_succ, Category.assoc]
  have h_horn_w : h_horn ≫ (w₀ ≫ c₂) = h_horn ≫ w₁ := by
    calc h_horn ≫ (w₀ ≫ c₂)
      _ = v_Λ ≫ c₁ ≫ c₂ := hv_c.symm
      _ = (h_bd ≫ u₁) ≫ c₁ ≫ c₂ := by rw [hu₁_h]
      _ = h_bd ≫ (u₁ ≫ c₁) ≫ c₂ := by simp only [Category.assoc]
      _ = h_bd ≫ I_succ ≫ w₁ := by rw [← sq₃.w]
      _ = h_horn ≫ w₁ := by
          simp only [h_horn, hornLastInclusionCDelta, h_bd, I_succ, Category.assoc]
  -- Show CM is the pushout of h_horn and h_horn via (w₀ ≫ c₂) and w₁
  have hcm_ext : ∀ {Z : CDelta.{u}} {g₁ g₂ : CM ⟶ Z},
      (w₀ ≫ c₂) ≫ g₁ = (w₀ ≫ c₂) ≫ g₂ → w₁ ≫ g₁ = w₁ ≫ g₂ → g₁ = g₂ := by
    intro Z g₁ g₂ hg₀ hg₁
    have hm₀ : c₀ ≫ c₁ ≫ c₂ ≫ g₁ = c₀ ≫ c₁ ≫ c₂ ≫ g₂ := by
      apply sqM.hom_ext
      · calc inl_M ≫ (c₀ ≫ c₁ ≫ c₂ ≫ g₁)
          _ = (inl_M ≫ c) ≫ g₁ := (Category.assoc _ _ _).symm
          _ = (h_face ≫ (w₀ ≫ c₂)) ≫ g₁ := by rw [hinl_c]
          _ = h_face ≫ ((w₀ ≫ c₂) ≫ g₁) := Category.assoc _ _ _
          _ = h_face ≫ ((w₀ ≫ c₂) ≫ g₂) := by rw [hg₀]
          _ = (h_face ≫ (w₀ ≫ c₂)) ≫ g₂ := (Category.assoc _ _ _).symm
          _ = (inl_M ≫ c) ≫ g₂ := by rw [← hinl_c]
          _ = inl_M ≫ (c₀ ≫ c₁ ≫ c₂ ≫ g₂) := Category.assoc _ _ _
      · calc inr_M ≫ (c₀ ≫ c₁ ≫ c₂ ≫ g₁)
          _ = (inr_M ≫ c) ≫ g₁ := (Category.assoc _ _ _).symm
          _ = (h_face ≫ w₁) ≫ g₁ := by rw [hinr_c]
          _ = h_face ≫ (w₁ ≫ g₁) := Category.assoc _ _ _
          _ = h_face ≫ (w₁ ≫ g₂) := by rw [hg₁]
          _ = (h_face ≫ w₁) ≫ g₂ := (Category.assoc _ _ _).symm
          _ = (inr_M ≫ c) ≫ g₂ := by rw [← hinr_c]
          _ = inr_M ≫ (c₀ ≫ c₁ ≫ c₂ ≫ g₂) := Category.assoc _ _ _
    have hm₁ : c₁ ≫ c₂ ≫ g₁ = c₁ ≫ c₂ ≫ g₂ := by
      apply sq₁.hom_ext
      · calc v_Λ ≫ (c₁ ≫ c₂ ≫ g₁)
          _ = (v_Λ ≫ c₁ ≫ c₂) ≫ g₁ := (Category.assoc _ _ _).symm
          _ = (h_horn ≫ (w₀ ≫ c₂)) ≫ g₁ := by rw [hv_c]
          _ = h_horn ≫ ((w₀ ≫ c₂) ≫ g₁) := Category.assoc _ _ _
          _ = h_horn ≫ ((w₀ ≫ c₂) ≫ g₂) := by rw [hg₀]
          _ = (h_horn ≫ (w₀ ≫ c₂)) ≫ g₂ := (Category.assoc _ _ _).symm
          _ = (v_Λ ≫ c₁ ≫ c₂) ≫ g₂ := by rw [← hv_c]
          _ = v_Λ ≫ (c₁ ≫ c₂ ≫ g₂) := Category.assoc _ _ _
      · exact hm₀
    have hm₂ : c₂ ≫ g₁ = c₂ ≫ g₂ := by
      apply sq₂.hom_ext
      · simpa only [Category.assoc] using hg₀
      · exact hm₁
    apply sq₃.hom_ext
    · exact hg₁
    · exact hm₂
  have sq_CM : IsPushout h_horn h_horn (w₀ ≫ c₂) w₁ := by
    apply IsPushout.of_isColimit (c := PushoutCocone.mk (w₀ ≫ c₂) w₁ h_horn_w)
    apply PushoutCocone.isColimitAux'
    intro s
    have hm₀_comm : I_n ≫ (h_face ≫ s.inl) = I_n ≫ (h_face ≫ s.inr) := by
      rw [← Category.assoc, ← Category.assoc, boundary_comp_stdSimplexFaceLastCDelta,
        Category.assoc, Category.assoc, s.condition]
    let m₀ : M ⟶ s.pt := sqM.desc (h_face ≫ s.inl) (h_face ≫ s.inr) hm₀_comm
    have hm₀_inl : inl_M ≫ m₀ = h_face ≫ s.inl := sqM.inl_desc _ _ _
    have hm₀_inr : inr_M ≫ m₀ = h_face ≫ s.inr := sqM.inr_desc _ _ _
    have hm₁_comm : i_Λ ≫ (h_horn ≫ s.inl) = (I_n ≫ inl_M) ≫ m₀ := by
      rw [Category.assoc, hm₀_inl, ← Category.assoc, ← boundary_comp_stdSimplexFaceLastCDelta,
        Category.assoc]
    let m₁ : M₁ ⟶ s.pt := sq₁.desc (h_horn ≫ s.inl) m₀ hm₁_comm
    have hm₁_v : v_Λ ≫ m₁ = h_horn ≫ s.inl := sq₁.inl_desc _ _ _
    have hm₁_c₀ : c₀ ≫ m₁ = m₀ := sq₁.inr_desc _ _ _
    have hm₂_comm : I_succ ≫ s.inl = u₀ ≫ m₁ := by
      apply sq_bh.hom_ext
      · calc s_bd ≫ I_succ ≫ s.inl
          _ = h_face ≫ s.inl := (Category.assoc _ _ _).symm
          _ = inl_M ≫ m₀ := hm₀_inl.symm
          _ = inl_M ≫ c₀ ≫ m₁ := by rw [hm₁_c₀]
          _ = (s_bd ≫ u₀) ≫ m₁ := by rw [← Category.assoc, hu₀_s]
          _ = s_bd ≫ u₀ ≫ m₁ := Category.assoc _ _ _
      · calc h_bd ≫ I_succ ≫ s.inl
          _ = h_horn ≫ s.inl := (Category.assoc _ _ _).symm
          _ = v_Λ ≫ m₁ := hm₁_v.symm
          _ = (h_bd ≫ u₀) ≫ m₁ := by rw [hu₀_h]
          _ = h_bd ≫ u₀ ≫ m₁ := Category.assoc _ _ _
    let m₂ : M₂ ⟶ s.pt := sq₂.desc s.inl m₁ hm₂_comm
    have hm₂_w₀ : w₀ ≫ m₂ = s.inl := sq₂.inl_desc _ _ _
    have hm₂_c₁ : c₁ ≫ m₂ = m₁ := sq₂.inr_desc _ _ _
    have hm₃_comm : I_succ ≫ s.inr = (u₁ ≫ c₁) ≫ m₂ := by
      rw [Category.assoc, hm₂_c₁]
      apply sq_bh.hom_ext
      · calc s_bd ≫ I_succ ≫ s.inr
          _ = h_face ≫ s.inr := (Category.assoc _ _ _).symm
          _ = inr_M ≫ m₀ := hm₀_inr.symm
          _ = inr_M ≫ c₀ ≫ m₁ := by rw [hm₁_c₀]
          _ = (s_bd ≫ u₁) ≫ m₁ := by rw [← Category.assoc, hu₁_s]
          _ = s_bd ≫ u₁ ≫ m₁ := Category.assoc _ _ _
      · calc h_bd ≫ I_succ ≫ s.inr
          _ = h_horn ≫ s.inr := (Category.assoc _ _ _).symm
          _ = h_horn ≫ s.inl := s.condition.symm
          _ = v_Λ ≫ m₁ := hm₁_v.symm
          _ = (h_bd ≫ u₁) ≫ m₁ := by rw [hu₁_h]
          _ = h_bd ≫ u₁ ≫ m₁ := Category.assoc _ _ _
    let m₃ : CM ⟶ s.pt := sq₃.desc s.inr m₂ hm₃_comm
    have hm₃_w₁ : w₁ ≫ m₃ = s.inr := sq₃.inl_desc _ _ _
    have hm₃_c₂ : c₂ ≫ m₃ = m₂ := sq₃.inr_desc _ _ _
    have hm₃_w₀ : (w₀ ≫ c₂) ≫ m₃ = s.inl := by
      rw [Category.assoc, hm₃_c₂, hm₂_w₀]
    refine ⟨m₃, hm₃_w₀, hm₃_w₁, ?_⟩
    intro m' hm'₀ hm'₁
    exact hcm_ext (hm'₀.trans hm₃_w₀.symm) (hm'₁.trans hm₃_w₁.symm)
  -- Deduce that w₀ ≫ c₂ and inl_M ≫ c are trivial cofibrations
  have hw₀c₂_we : weakEquivalences CDelta.{u} (w₀ ≫ c₂) :=
    cDelta_trivialCofibration_cobaseChange h_horn h_horn w₁ (w₀ ≫ c₂) sq_CM.flip
      (hornLastInclusionCDelta_cofibration n) (hornLastInclusionCDelta_weakEquivalence n)
  have hinl_M_cof : cofibrations CDelta.{u} inl_M :=
    (cofibrations CDelta.{u}).of_isPushout sqM hI_n
  have hinlc_cof : cofibrations CDelta.{u} (inl_M ≫ c) :=
    (cofibrations CDelta.{u}).comp_mem _ _ hinl_M_cof hc
  have hinlc_we : weakEquivalences CDelta.{u} (inl_M ≫ c) := by
    rw [hinl_c]
    exact cDelta_weakEquivalence_comp _ _ (stdSimplexFaceLastCDelta_weakEquivalence n) hw₀c₂_we
  -- Retraction p_M : CM ⟶ Δ_n
  obtain ⟨r, hr⟩ := cDelta_exists_retraction h_face
    (stdSimplexFaceLastCDelta_cofibration n) (stdSimplexFaceLastCDelta_weakEquivalence n)
  let p_M : CM ⟶ stdSimplexCDelta.{u} n := sq_CM.desc r r rfl
  have hp_w₀ : (w₀ ≫ c₂) ≫ p_M = r := sq_CM.inl_desc _ _ _
  have hp_w₁ : w₁ ≫ p_M = r := sq_CM.inr_desc _ _ _
  have hj₀_cp : inl_M ≫ c ≫ p_M = 𝟙 (stdSimplexCDelta.{u} n) := by
    calc inl_M ≫ c ≫ p_M
      _ = (inl_M ≫ c) ≫ p_M := (Category.assoc _ _ _).symm
      _ = (h_face ≫ (w₀ ≫ c₂)) ≫ p_M := by rw [hinl_c]
      _ = h_face ≫ ((w₀ ≫ c₂) ≫ p_M) := Category.assoc _ _ _
      _ = h_face ≫ r := by rw [hp_w₀]
      _ = 𝟙 _ := hr
  have hj₁_cp : inr_M ≫ c ≫ p_M = 𝟙 (stdSimplexCDelta.{u} n) := by
    calc inr_M ≫ c ≫ p_M
      _ = (inr_M ≫ c) ≫ p_M := (Category.assoc _ _ _).symm
      _ = (h_face ≫ w₁) ≫ p_M := by rw [hinr_c]
      _ = h_face ≫ (w₁ ≫ p_M) := Category.assoc _ _ _
      _ = h_face ≫ r := by rw [hp_w₁]
      _ = 𝟙 _ := hr
  have hp_we : weakEquivalences CDelta.{u} p_M := by
    apply cDelta_weakEquivalence_of_comp_left (inl_M ≫ c) p_M hinlc_we
    rw [Category.assoc, hj₀_cp]
    exact cDelta_weakEquivalence_id _
  exact ⟨{
    P := M
    j₀ := inl_M
    j₁ := inr_M
    isPushout := sqM
    I := CM
    c := c
    p := p_M
    c_mem := hc
    p_mem := hp_we
    j₀_c_p := hj₀_cp
    j₁_c_p := hj₁_cp }, hinlc_cof, hinlc_we⟩

/-!
## Boundary test lifting property in `CDelta`
-/

/-- Given a weak equivalence `p : Z ⟶ X` in `CDelta` and a commutative square from
`boundaryCDeltaInclusion n` to `p`, there is a lift `b : Δ_n ⟶ Z` on the boundary and a relative
homotopy `H : cyl.I ⟶ X` from `b ≫ p` to `x`. -/
theorem cDelta_boundary_test_lift {Z X : CDelta.{u}} (p : Z ⟶ X)
    (hp : weakEquivalences CDelta.{u} p) (n : ℕ)
    (cyl : RelativeCylinder (boundaryCDeltaInclusion.{u} n))
    (a : boundaryCDelta.{u} n ⟶ Z) (x : stdSimplexCDelta.{u} n ⟶ X)
    (hx : a ≫ p = boundaryCDeltaInclusion.{u} n ≫ x) :
    ∃ (b : stdSimplexCDelta.{u} n ⟶ Z) (H : cyl.I ⟶ X),
      boundaryCDeltaInclusion.{u} n ≫ b = a ∧
        (cyl.j₀ ≫ cyl.c) ≫ H = b ≫ p ∧
        (cyl.j₁ ≫ cyl.c) ≫ H = x := by
  let I_n := boundaryCDeltaInclusion.{u} n
  have hI_n : cofibrations CDelta.{u} I_n := boundaryCDeltaInclusion_cofibration n
  obtain ⟨R, hR⟩ := Packages.exists_standardRealization.{u}
  let F : CDelta.{u} ⥤ FinCell.{u} := hR.isCellularRealization.toFinCell
  have hF : IsCylinderMorphism F := Packages.isCylinderMorphism_toFinCell hR.isCellularRealization
  have hFF : IsHomotopyFullyFaithful F := Packages.standardRealization_isHomotopyFullyFaithful hR
  have : IsCylinderCategory FinCell.{u} := Packages.finCell_isCylinderCategory
  have hRI_n : Top.relativeFiniteCellComplexes (R.map I_n) :=
    hR.isCellularRealization.map_cofibration I_n hI_n
  have hRp : Top.homotopyEquivalences (R.map p) :=
    hR.isCellularRealization.map_weakEquivalence p hp
  have hxR : R.map a ≫ R.map p = R.map I_n ≫ R.map x := by
    rw [← R.map_comp, ← R.map_comp, hx]
  obtain ⟨l, hl, hlp⟩ :=
    (Packages.relativeLift_of_homotopyEquivalence (R.map I_n) hRI_n (R.map p) hRp).1
      (R.map a) (R.map x) hxR
  let l_fc : F.obj (stdSimplexCDelta.{u} n) ⟶ F.obj Z := ObjectProperty.homMk l
  have hl_fc : F.map I_n ≫ l_fc = F.map a := by
    apply ObjectProperty.hom_ext
    exact hl
  obtain ⟨b, hb, hrel_b⟩ := hFF I_n hI_n a l_fc hl_fc
  have hrel_bp : RelHomotopic (F.map I_n) (F.map (b ≫ p)) (l_fc ≫ F.map p) := by
    rcases hrel_b with ⟨cyl₁, H₁, hH₁₀, hH₁₁⟩
    refine ⟨cyl₁, H₁ ≫ F.map p, ?_, ?_⟩
    · rw [← Category.assoc, ← Category.assoc, Category.assoc cyl₁.j₀, hH₁₀, F.map_comp]
    · rw [← Category.assoc, ← Category.assoc, Category.assoc cyl₁.j₁, hH₁₁]
  obtain ⟨cyl₂, h₂, hh₂₀, hh₂₁⟩ :=
    (Packages.finCell_homotopicRel_iff (F.map I_n) hRI_n (l ≫ R.map p) (R.map x)).1 hlp
  have hrel_lx : RelHomotopic (F.map I_n) (l_fc ≫ F.map p) (F.map x) := by
    refine ⟨cyl₂, ObjectProperty.homMk h₂, ?_, ?_⟩
    · apply ObjectProperty.hom_ext
      change (cyl₂.j₀ ≫ cyl₂.c).hom ≫ h₂ = l ≫ R.map p
      exact hh₂₀
    · apply ObjectProperty.hom_ext
      change (cyl₂.j₁ ≫ cyl₂.c).hom ≫ h₂ = R.map x
      exact hh₂₁
  have hrel_bpx : RelHomotopic (F.map I_n) (F.map (b ≫ p)) (F.map x) :=
    (Packages.relHomotopic_equivalence (F.map I_n) hRI_n).1.trans hrel_bp hrel_lx
  let Fcyl : RelativeCylinder (F.map I_n) :=
    { P := F.obj cyl.P
      j₀ := F.map cyl.j₀
      j₁ := F.map cyl.j₁
      isPushout := hF.map_isPushout I_n I_n cyl.j₀ cyl.j₁ cyl.isPushout hI_n
      I := F.obj cyl.I
      c := F.map cyl.c
      p := F.map cyl.p
      c_mem := hF.map_cofibration cyl.c cyl.c_mem
      p_mem := hF.map_weakEquivalence cyl.p cyl.p_mem
      j₀_c_p := by rw [← F.map_comp, ← F.map_comp, cyl.j₀_c_p, F.map_id]
      j₁_c_p := by rw [← F.map_comp, ← F.map_comp, cyl.j₁_c_p, F.map_id] }
  obtain ⟨H₀, hH₀₀, hH₀₁⟩ :=
    (Packages.relHomotopic_equivalence (F.map I_n) hRI_n).2 Fcyl
      (F.map (b ≫ p)) (F.map x) hrel_bpx
  have hbx_comm : I_n ≫ (b ≫ p) = I_n ≫ x := by
    rw [← Category.assoc, hb, hx]
  let m_bx : cyl.P ⟶ X := cyl.isPushout.desc (b ≫ p) x hbx_comm
  have hm_bx₀ : cyl.j₀ ≫ m_bx = b ≫ p := cyl.isPushout.inl_desc _ _ _
  have hm_bx₁ : cyl.j₁ ≫ m_bx = x := cyl.isPushout.inr_desc _ _ _
  have hH₀_eq : F.map cyl.c ≫ H₀ = F.map m_bx := by
    apply Fcyl.isPushout.hom_ext
    · calc F.map cyl.j₀ ≫ (F.map cyl.c ≫ H₀)
        _ = F.map (b ≫ p) := hH₀₀
        _ = F.map (cyl.j₀ ≫ m_bx) := by rw [hm_bx₀]
        _ = F.map cyl.j₀ ≫ F.map m_bx := F.map_comp _ _
    · calc F.map cyl.j₁ ≫ (F.map cyl.c ≫ H₀)
        _ = F.map x := hH₀₁
        _ = F.map (cyl.j₁ ≫ m_bx) := by rw [hm_bx₁]
        _ = F.map cyl.j₁ ≫ F.map m_bx := F.map_comp _ _
  obtain ⟨H, hH, -⟩ := hFF cyl.c cyl.c_mem m_bx H₀ hH₀_eq
  refine ⟨b, H, hb, ?_, ?_⟩
  · rw [Category.assoc, hH, hm_bx₀]
  · rw [Category.assoc, hH, hm_bx₁]

/-!
## Pushout pasting for cell cylinder extensions and `ExtendsFiniteFactorization`
-/

/-- The induced map `c' : B ⟶ T` from a cell pushout `B = A ⊔_{∂Δ_n} Δ_n` to the cylinder extension
`T = Z ⊔_{Δ_n} cyl.I` is a cofibration. -/
theorem cDelta_cell_cylinder_cofibration {A B Z T : CDelta.{u}} (n : ℕ)
    (cyl : RelativeCylinder (boundaryCDeltaInclusion.{u} n))
    (a : boundaryCDelta.{u} n ⟶ A) (i : A ⟶ B) (x : stdSimplexCDelta.{u} n ⟶ B)
    (sq : IsPushout a (boundaryCDeltaInclusion.{u} n) i x)
    (c : A ⟶ Z) (hc : cofibrations CDelta.{u} c) (b : stdSimplexCDelta.{u} n ⟶ Z)
    (hb : boundaryCDeltaInclusion.{u} n ≫ b = a ≫ c)
    (t : Z ⟶ T) (d : cyl.I ⟶ T) (st : IsPushout b (cyl.j₀ ≫ cyl.c) t d)
    (c' : B ⟶ T) (hi : i ≫ c' = c ≫ t) (hx : x ≫ c' = (cyl.j₁ ≫ cyl.c) ≫ d) :
    cofibrations CDelta.{u} c' := by
  let I_n := boundaryCDeltaInclusion.{u} n
  have : HasPushout c i := cDelta_isCofibrationCategory.hasPushout c i hc
  let P : CDelta.{u} := pushout c i
  let k : Z ⟶ P := pushout.inl c i
  let l : B ⟶ P := pushout.inr c i
  have sp : IsPushout c i k l := IsPushout.of_hasPushout c i
  have w : I_n ≫ (b ≫ k) = I_n ≫ (x ≫ l) := by
    rw [← Category.assoc, hb, Category.assoc, sp.w, ← Category.assoc, sq.w, Category.assoc]
  let bd : cyl.P ⟶ P := cyl.isPushout.desc (b ≫ k) (x ≫ l) w
  let q : P ⟶ T := sp.desc t c' hi.symm
  have hkq : k ≫ q = t := sp.inl_desc _ _ _
  have hlq : l ≫ q = c' := sp.inr_desc _ _ _
  have hbd₀ : cyl.j₀ ≫ bd = b ≫ k := cyl.isPushout.inl_desc _ _ _
  have hbd₁ : cyl.j₁ ≫ bd = x ≫ l := cyl.isPushout.inr_desc _ _ _
  have wq : bd ≫ q = cyl.c ≫ d := by
    apply cyl.isPushout.hom_ext
    · rw [← Category.assoc, hbd₀, Category.assoc, hkq, st.w, Category.assoc]
    · rw [← Category.assoc, hbd₁, Category.assoc, hlq, hx, Category.assoc]
  have sb : IsPushout bd cyl.c q d := by
    apply IsPushout.of_isColimit (c := PushoutCocone.mk q d wq)
    apply PushoutCocone.isColimitAux'
    intro s
    have ws : b ≫ (k ≫ s.inl) = (cyl.j₀ ≫ cyl.c) ≫ s.inr := by
      have e := congrArg (cyl.j₀ ≫ ·) s.condition
      rw [← Category.assoc, hbd₀] at e
      simpa only [Category.assoc] using e
    have ws' : x ≫ (l ≫ s.inl) = (cyl.j₁ ≫ cyl.c) ≫ s.inr := by
      have e := congrArg (cyl.j₁ ≫ ·) s.condition
      rw [← Category.assoc, hbd₁] at e
      simpa only [Category.assoc] using e
    let r : T ⟶ s.pt := st.desc (k ≫ s.inl) s.inr ws
    have htr : t ≫ r = k ≫ s.inl := st.inl_desc _ _ _
    have hdr : d ≫ r = s.inr := st.inr_desc _ _ _
    have hcr : c' ≫ r = l ≫ s.inl := by
      apply sq.hom_ext
      · calc i ≫ (c' ≫ r)
          _ = c ≫ (t ≫ r) := by rw [← Category.assoc, hi, Category.assoc]
          _ = c ≫ (k ≫ s.inl) := by rw [htr]
          _ = i ≫ (l ≫ s.inl) := by rw [← Category.assoc, sp.w, Category.assoc]
      · calc x ≫ (c' ≫ r)
          _ = (cyl.j₁ ≫ cyl.c) ≫ (d ≫ r) := by rw [← Category.assoc, hx, Category.assoc]
          _ = (cyl.j₁ ≫ cyl.c) ≫ s.inr := by rw [hdr]
          _ = x ≫ (l ≫ s.inl) := ws'.symm
    refine ⟨r, ?_, hdr, ?_⟩
    · change q ≫ r = s.inl
      apply sp.hom_ext
      · rw [← Category.assoc, hkq, htr]
      · rw [← Category.assoc, hlq, hcr]
    · intro m (hm₀ : q ≫ m = s.inl) (hm₁ : d ≫ m = s.inr)
      apply st.hom_ext
      · calc t ≫ m
          _ = (k ≫ q) ≫ m := by rw [hkq]
          _ = k ≫ (q ≫ m) := Category.assoc _ _ _
          _ = k ≫ s.inl := by rw [hm₀]
          _ = t ≫ r := htr.symm
      · exact hm₁.trans hdr.symm
  have hq : cofibrations CDelta.{u} q :=
    (cofibrations CDelta.{u}).of_isPushout sb cyl.c_mem
  have hl : cofibrations CDelta.{u} l :=
    (cofibrations CDelta.{u}).of_isPushout sp.flip hc
  rw [← hlq]
  exact (cofibrations CDelta.{u}).comp_mem _ _ hl hq

/-- A morphism `i : A ⟶ B` in `CDelta` satisfies `ExtendsFiniteFactorization i` if any factorization
of `i ≫ f` through a cofibration `c : A ⟶ Z` and a weak equivalence `p : Z ⟶ X` extends to a
factorization of `f` through a cofibration `c' : B ⟶ T` and a weak equivalence `p' : T ⟶ X` via a
cofibration `t : Z ⟶ T`. -/
def ExtendsFiniteFactorization {A B : CDelta.{u}} (i : A ⟶ B) : Prop :=
  ∀ {Z X : CDelta.{u}} (c : A ⟶ Z), cofibrations CDelta.{u} c →
    ∀ (p : Z ⟶ X), weakEquivalences CDelta.{u} p → ∀ (f : B ⟶ X), c ≫ p = i ≫ f →
      ∃ (T : CDelta.{u}) (c' : B ⟶ T) (t : Z ⟶ T) (p' : T ⟶ X),
        cofibrations CDelta.{u} c' ∧ cofibrations CDelta.{u} t ∧ weakEquivalences CDelta.{u} p' ∧
          i ≫ c' = c ≫ t ∧ c' ≫ p' = f ∧ t ≫ p' = p

lemma extendsFiniteFactorization_id (A : CDelta.{u}) :
    ExtendsFiniteFactorization (𝟙 A) := by
  intro Z X c hc p hp f h
  exact ⟨Z, c, 𝟙 Z, p, hc, (cofibrations CDelta.{u}).id_mem Z, hp,
    by simp, by simpa using h, by simp⟩

lemma extendsFiniteFactorization_iso {A B : CDelta.{u}} (i : A ⟶ B) [IsIso i] :
    ExtendsFiniteFactorization i := by
  intro Z X c hc p hp f h
  have hinv : cofibrations CDelta.{u} (inv i) :=
    cDelta_isCofibrationCategory.isomorphisms_le _ (MorphismProperty.isomorphisms.infer_property _)
  refine ⟨Z, inv i ≫ c, 𝟙 Z, p,
    (cofibrations CDelta.{u}).comp_mem _ _ hinv hc,
    (cofibrations CDelta.{u}).id_mem Z, hp, ?_, ?_, by simp⟩
  · simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, h, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

lemma extendsFiniteFactorization_comp {A B D : CDelta.{u}} (i : A ⟶ B) (j : B ⟶ D)
    (hi : ExtendsFiniteFactorization i) (hj : ExtendsFiniteFactorization j) :
    ExtendsFiniteFactorization (i ≫ j) := by
  intro Z X c hc p hp f h
  obtain ⟨T, c₁, t₁, p₁, hc₁, ht₁, hp₁, hi₁, hc₁p, ht₁p⟩ :=
    hi c hc p hp (j ≫ f) (by simpa only [Category.assoc] using h)
  obtain ⟨U, c₂, t₂, p₂, hc₂, ht₂, hp₂, hi₂, hc₂p, ht₂p⟩ :=
    hj c₁ hc₁ p₁ hp₁ f hc₁p
  refine ⟨U, c₂, t₁ ≫ t₂, p₂, hc₂, (cofibrations CDelta.{u}).comp_mem _ _ ht₁ ht₂,
    hp₂, ?_, hc₂p, ?_⟩
  · rw [Category.assoc, hi₂, ← Category.assoc, hi₁, Category.assoc]
  · rw [Category.assoc, ht₂p, ht₁p]

theorem extendsFiniteFactorization_cell {A B : CDelta.{u}} (n : ℕ)
    (a : boundaryCDelta.{u} n ⟶ A) (i : A ⟶ B) (x : stdSimplexCDelta.{u} n ⟶ B)
    (sq : IsPushout a (boundaryCDeltaInclusion.{u} n) i x) :
    ExtendsFiniteFactorization i := by
  intro Z X c hc p hp f h
  let I_n := boundaryCDeltaInclusion.{u} n
  obtain ⟨cyl, hJ_cof, hJ_we⟩ := exists_boundary_relativeCylinder.{u} n
  let J_n := cyl.j₀ ≫ cyl.c
  let K_n := cyl.j₁ ≫ cyl.c
  have w : (a ≫ c) ≫ p = I_n ≫ (x ≫ f) := by
    rw [Category.assoc, h, ← Category.assoc, sq.w, Category.assoc]
  obtain ⟨b, H, hb, hH₀, hH₁⟩ := cDelta_boundary_test_lift p hp n cyl (a ≫ c) (x ≫ f) w
  have : HasPushout J_n b := cDelta_isCofibrationCategory.hasPushout J_n b hJ_cof
  let T : CDelta.{u} := pushout J_n b
  let d : cyl.I ⟶ T := pushout.inl J_n b
  let t : Z ⟶ T := pushout.inr J_n b
  have st_flip : IsPushout J_n b d t := IsPushout.of_hasPushout J_n b
  have st : IsPushout b J_n t d := st_flip.flip
  have hJK : I_n ≫ J_n = I_n ≫ K_n := by
    dsimp [J_n, K_n]
    rw [← Category.assoc, cyl.isPushout.w, Category.assoc]
  have w' : a ≫ (c ≫ t) = I_n ≫ (K_n ≫ d) := by
    rw [← Category.assoc, ← hb, Category.assoc, st.w, ← Category.assoc, hJK, Category.assoc]
  let c' : B ⟶ T := sq.desc (c ≫ t) (K_n ≫ d) w'
  let p' : T ⟶ X := st.desc p H hH₀.symm
  have hi : i ≫ c' = c ≫ t := sq.inl_desc _ _ _
  have hx : x ≫ c' = K_n ≫ d := sq.inr_desc _ _ _
  have ht : t ≫ p' = p := st.inl_desc _ _ _
  have hd : d ≫ p' = H := st.inr_desc _ _ _
  have ht_cof : cofibrations CDelta.{u} t :=
    (cofibrations CDelta.{u}).of_isPushout st hJ_cof
  have ht_we : weakEquivalences CDelta.{u} t :=
    cDelta_trivialCofibration_cobaseChange J_n b d t st_flip hJ_cof hJ_we
  have hp' : weakEquivalences CDelta.{u} p' :=
    cDelta_weakEquivalence_of_comp_left t p' ht_we (by rwa [ht])
  refine ⟨T, c', t, p',
    cDelta_cell_cylinder_cofibration n cyl a i x sq c hc b hb t d st c' hi hx,
    ht_cof, hp', hi, ?_, ht⟩
  apply sq.hom_ext
  · calc i ≫ (c' ≫ p')
      _ = c ≫ (t ≫ p') := by rw [← Category.assoc, hi, Category.assoc]
      _ = c ≫ p := by rw [ht]
      _ = i ≫ f := h
  · calc x ≫ (c' ≫ p')
      _ = K_n ≫ (d ≫ p') := by rw [← Category.assoc, hx, Category.assoc]
      _ = K_n ≫ H := by rw [hd]
      _ = x ≫ f := hH₁

/-- Every single cell attachment in `CDelta` is a pushout of `boundaryCDeltaInclusion n`. -/
lemma exists_isPushout_of_isCellAttachment_cDelta {A B : CDelta.{u}} (i : A ⟶ B)
    (hi : AlgKan.IsCellAttachment i.hom) :
    ∃ (n : ℕ) (a : boundaryCDelta.{u} n ⟶ A) (x : stdSimplexCDelta.{u} n ⟶ B),
      IsPushout a (boundaryCDeltaInclusion.{u} n) i x := by
  obtain ⟨n, a₀, y₀, hcomm₀, huniq₀⟩ := hi
  let η_bd := freeAlgKanUnit (SemiSSet.boundary.{u} n).toFunctor
  let η_std := freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n))
  obtain ⟨a_alg, ha_alg, -⟩ :=
    freeAlgKan_isFreeOn (SemiSSet.boundary.{u} n).toFunctor A.obj a₀
  obtain ⟨x_alg, hx_alg, -⟩ :=
    freeAlgKan_isFreeOn (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n)) B.obj y₀
  let a : boundaryCDelta.{u} n ⟶ A := ObjectProperty.homMk a_alg
  let x : stdSimplexCDelta.{u} n ⟶ B := ObjectProperty.homMk x_alg
  refine ⟨n, a, x, ?_⟩
  apply isPushout_cDelta_of_algKan
  dsimp [a, x, boundaryCDelta, stdSimplexCDelta, boundaryCDeltaInclusion]
  let i_bd : freeAlgKan (SemiSSet.boundary.{u} n).toFunctor ⟶
      freeAlgKan (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n)) :=
    freeAlgKanMap (SemiSSet.boundary.{u} n).ι
  change IsPushout a_alg i_bd i.hom x_alg
  have hw : a_alg ≫ i.hom = i_bd ≫ x_alg := by
    apply freeAlgKan_hom_ext
    calc η_bd ≫ (a_alg ≫ i.hom).hom
      _ = (η_bd ≫ a_alg.hom) ≫ i.hom.hom := (Category.assoc _ _ _).symm
      _ = a₀ ≫ i.hom.hom := by rw [ha_alg]
      _ = (SemiSSet.boundary.{u} n).ι ≫ y₀ := hcomm₀.symm
      _ = (SemiSSet.boundary.{u} n).ι ≫ (η_std ≫ x_alg.hom) := by rw [hx_alg]
      _ = ((SemiSSet.boundary.{u} n).ι ≫ η_std) ≫ x_alg.hom := (Category.assoc _ _ _).symm
      _ = (η_bd ≫ i_bd.hom) ≫ x_alg.hom := by
          dsimp [i_bd, η_bd, η_std]
          rw [← freeAlgKanUnit_comp_freeAlgKanMap]
      _ = η_bd ≫ (i_bd ≫ x_alg).hom := Category.assoc _ _ _
  apply IsPushout.of_isColimit (c := PushoutCocone.mk i.hom x_alg hw)
  apply PushoutCocone.isColimitAux'
  intro s
  have hz : (SemiSSet.boundary.{u} n).ι ≫ (η_std ≫ s.inr.hom) = a₀ ≫ s.inl.hom := by
    calc (SemiSSet.boundary.{u} n).ι ≫ (η_std ≫ s.inr.hom)
      _ = ((SemiSSet.boundary.{u} n).ι ≫ η_std) ≫ s.inr.hom := (Category.assoc _ _ _).symm
      _ = (η_bd ≫ i_bd.hom) ≫ s.inr.hom := by
          dsimp [i_bd, η_bd, η_std]
          rw [← freeAlgKanUnit_comp_freeAlgKanMap]
      _ = η_bd ≫ (i_bd ≫ s.inr).hom := Category.assoc _ _ _
      _ = η_bd ≫ (a_alg ≫ s.inl).hom := congrArg (fun k => η_bd ≫ k.hom) s.condition.symm
      _ = (η_bd ≫ a_alg.hom) ≫ s.inl.hom := (Category.assoc _ _ _).symm
      _ = a₀ ≫ s.inl.hom := by rw [ha_alg]
  have hex := huniq₀ s.pt s.inl (η_std ≫ s.inr.hom) hz
  let g' : B.obj ⟶ s.pt := hex.choose
  have hg'l : i.hom ≫ g' = s.inl := hex.choose_spec.1.1
  have hg'r : y₀ ≫ g'.hom = η_std ≫ s.inr.hom := hex.choose_spec.1.2
  have hg'uniq : ∀ m : B.obj ⟶ s.pt,
      i.hom ≫ m = s.inl ∧ y₀ ≫ m.hom = η_std ≫ s.inr.hom → m = g' :=
    hex.choose_spec.2
  have hg'r_alg : x_alg ≫ g' = s.inr := by
    apply freeAlgKan_hom_ext
    calc η_std ≫ (x_alg ≫ g').hom
      _ = (η_std ≫ x_alg.hom) ≫ g'.hom := (Category.assoc _ _ _).symm
      _ = y₀ ≫ g'.hom := by rw [hx_alg]
      _ = η_std ≫ s.inr.hom := hg'r
  refine ⟨g', hg'l, hg'r_alg, ?_⟩
  intro m hm₀ (hm₁ : x_alg ≫ m = s.inr)
  apply hg'uniq m ⟨hm₀, ?_⟩
  calc y₀ ≫ m.hom
    _ = (η_std ≫ x_alg.hom) ≫ m.hom := by rw [hx_alg]
    _ = η_std ≫ (x_alg ≫ m).hom := Category.assoc _ _ _
    _ = η_std ≫ s.inr.hom := by rw [hm₁]

theorem cellularMaps_extendsFiniteFactorization {A₀ B₀ : AlgKan.{u}} (j : A₀ ⟶ B₀)
    (hj : AlgKan.cellularMaps j) :
    ∀ (hA₀ : AlgKan.IsFinitelyCellular A₀) (hB₀ : AlgKan.IsFinitelyCellular B₀),
      ExtendsFiniteFactorization (ObjectProperty.homMk j : (⟨A₀, hA₀⟩ : CDelta.{u}) ⟶ ⟨B₀, hB₀⟩) := by
  have base : ∀ {X₀ Y₀ : AlgKan.{u}} (f : X₀ ⟶ Y₀),
      ((show MorphismProperty AlgKan.{u} from fun _ _ k => AlgKan.IsCellAttachment k) ⊔
        MorphismProperty.isomorphisms AlgKan.{u}) f →
      ∀ (hX₀ : AlgKan.IsFinitelyCellular X₀) (hY₀ : AlgKan.IsFinitelyCellular Y₀),
        ExtendsFiniteFactorization
          (ObjectProperty.homMk f : (⟨X₀, hX₀⟩ : CDelta.{u}) ⟶ ⟨Y₀, hY₀⟩) := by
    intro X₀ Y₀ f hf hX₀ hY₀
    rcases hf with hf | hf
    · obtain ⟨n, a, x, sq⟩ :=
        exists_isPushout_of_isCellAttachment_cDelta
          (ObjectProperty.homMk f : (⟨X₀, hX₀⟩ : CDelta.{u}) ⟶ ⟨Y₀, hY₀⟩) hf
      exact extendsFiniteFactorization_cell n a _ x sq
    · have : IsIso f := hf
      have h_iso : IsIso (ObjectProperty.homMk f : (⟨X₀, hX₀⟩ : CDelta.{u}) ⟶ ⟨Y₀, hY₀⟩) :=
        ⟨⟨ObjectProperty.homMk (inv f),
          by apply ObjectProperty.hom_ext; exact IsIso.hom_inv_id f,
          by apply ObjectProperty.hom_ext; exact IsIso.inv_hom_id f⟩⟩
      exact @extendsFiniteFactorization_iso _ _ _ h_iso
  induction hj with
  | of f hf =>
    intro hX₀ hY₀
    exact base f hf hX₀ hY₀
  | id X₀ =>
    intro hX₀ hY₀
    exact extendsFiniteFactorization_id ⟨X₀, hX₀⟩
  | comp_of f g hf hg ih =>
    intro hX₀ hZ₀
    have hY₀ : AlgKan.IsFinitelyCellular _ := isFinitelyCellular_of_cellularMaps hf hX₀
    change ExtendsFiniteFactorization
      ((ObjectProperty.homMk f : (⟨_, hX₀⟩ : CDelta.{u}) ⟶ ⟨_, hY₀⟩) ≫
        (ObjectProperty.homMk g : (⟨_, hY₀⟩ : CDelta.{u}) ⟶ ⟨_, hZ₀⟩))
    exact extendsFiniteFactorization_comp
      (ObjectProperty.homMk f : (⟨_, hX₀⟩ : CDelta.{u}) ⟶ ⟨_, hY₀⟩)
      (ObjectProperty.homMk g : (⟨_, hY₀⟩ : CDelta.{u}) ⟶ ⟨_, hZ₀⟩)
      (ih hX₀ hY₀) (base g hg hY₀ hZ₀)

theorem cDelta_extendsFiniteFactorization {A B : CDelta.{u}} (i : A ⟶ B)
    (hi : cofibrations CDelta.{u} i) :
    ExtendsFiniteFactorization i :=
  cellularMaps_extendsFiniteFactorization i.hom hi A.property B.property

/-- Every object of `CDelta` admits a cylinder object relative to any initial object. -/
theorem cDelta_exists_cylinder {I : CDelta.{u}} (hI : IsInitial I) (X : CDelta.{u}) :
    Nonempty (RelativeCylinder (hI.to X)) := by
  let i : I ⟶ X := hI.to X
  have hi : cofibrations CDelta.{u} i := cDelta_isCofibrationCategory.initial_cofibration hI X
  have : HasPushout i i := cDelta_isCofibrationCategory.hasPushout i i hi
  let P : CDelta.{u} := pushout i i
  let j₀ : X ⟶ P := pushout.inl i i
  let j₁ : X ⟶ P := pushout.inr i i
  have sq : IsPushout i i j₀ j₁ := IsPushout.of_hasPushout i i
  let f : P ⟶ X := sq.desc (𝟙 X) (𝟙 X) rfl
  let iP : I ⟶ P := hI.to P
  have hiP : cofibrations CDelta.{u} iP := cDelta_isCofibrationCategory.initial_cofibration hI P
  have hp : weakEquivalences CDelta.{u} (𝟙 X) := cDelta_weakEquivalence_id X
  obtain ⟨T, c, t, p, hc, -, hwp, -, hcp, -⟩ :=
    cDelta_extendsFiniteFactorization iP hiP i hi (𝟙 X) hp f (hI.hom_ext _ _)
  refine ⟨{
    P := P
    j₀ := j₀
    j₁ := j₁
    isPushout := sq
    I := T
    c := c
    p := p
    c_mem := hc
    p_mem := hwp
    j₀_c_p := by rw [hcp, sq.inl_desc]
    j₁_c_p := by rw [hcp, sq.inr_desc] }⟩

end HomotopyHypothesis.Cylinder.SimplicialCategory

namespace HomotopyHypothesis.Henry.Packages

/-- The category `C^Δ` of finitely cellular algebraic Kan complexes is a cylinder category. -/
theorem cDelta_isCylinderCategory_proof : IsCylinderCategory CDelta.{u} :=
  Cylinder.SemisimplicialCategory.cDelta_isCylinderCategory_of_parts
    Cylinder.SimplicialCategory.cDelta_isCofibrationCategory
    (fun i f k j sq hi hwi =>
      Cylinder.SimplicialCategory.cDelta_trivialCofibration_cobaseChange i f k j sq hi hwi)
    (fun hI X => Cylinder.SimplicialCategory.cDelta_exists_cylinder hI X)
    (fun i hi hwi => Cylinder.SimplicialCategory.cDelta_exists_retraction i hi hwi)

#print axioms HomotopyHypothesis.Henry.Packages.cDelta_isCylinderCategory_proof

end HomotopyHypothesis.Henry.Packages
