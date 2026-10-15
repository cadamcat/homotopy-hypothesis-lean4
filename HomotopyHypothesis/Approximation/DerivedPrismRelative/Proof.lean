import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Cylinder.AnodyneCells.Proofs
import HomotopyHypothesis.Approximation.DerivedPrismRelative.Boundary
import HomotopyHypothesis.Approximation.DerivedPrismRelative.CellAttachment
import HomotopyHypothesis.Approximation.DerivedPrismRelative.RelativeStages
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderCellProof.Part1
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLanToDprism
import HomotopyHypothesis.Approximation.Topological.RelPrismApproximation.Part1
/-!
# Relative anodyne collapse of finite derived cylinders

Attach the missing simplices in increasing dimension. Each relative stage is a pushout of the
relative derived cylinder of a simplex boundary.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismRelative

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological
open HomotopyHypothesis.Cylinder.AnodyneCells

theorem relativeStageMap_refl {W : SemiSSet.{u}} (A : Subfunctor W) :
    relativeStageMap (le_rfl : A ≤ A) = 𝟙 (relativeStage A) := by
  have hid : Subfunctor.homOfLe (le_rfl : A ≤ A) = 𝟙 A.toFunctor := by
    ext i x
    rfl
  apply pushout.hom_ext
  · simp only [relativeStageMap_inl, Category.comp_id]
  · rw [relativeStageMap_inr, hid, dprismLan.map_id, Category.id_comp, Category.comp_id]

theorem relativeStageMap_comp {W : SemiSSet.{u}} {A B C : Subfunctor W}
    (hAB : A ≤ B) (hBC : B ≤ C) :
    relativeStageMap hAB ≫ relativeStageMap hBC = relativeStageMap (hAB.trans hBC) := by
  have hh : Subfunctor.homOfLe hAB ≫ Subfunctor.homOfLe hBC =
      Subfunctor.homOfLe (hAB.trans hBC) := by
    ext i x
    rfl
  apply pushout.hom_ext
  · simp only [relativeStageMap_inl_assoc, relativeStageMap_inl]
  · simp only [relativeStageMap_inr_assoc, relativeStageMap_inr, Category.assoc]
    rw [← Functor.map_comp_assoc, hh]

/-- Each one-simplex relative-stage attachment is anodyne. -/
theorem anodyne_relativeStageMap_cell {W : SemiSSet.{u}} {A B : Subfunctor W}
    (h : A ≤ B) (n : ℕ) (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hyA : y ∉ A.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hyB : y ∈ B.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hfaces : ∀ (k : ℕ)
      (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n),
      k ≠ n → W.map θ.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)))
    (hB : ∀ (k : ℕ) (z : W.obj (op (Henry.SemiSimplexCategory.mk k))),
      z ∈ B.obj (op (Henry.SemiSimplexCategory.mk k)) →
        z ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)) ∨
          ∃ hk : k = n, hk ▸ z = y) :
    anodyne (relativeStageMap h) := by
  let sq := isPushout_cellAttachment y hfaces h hyA hyB hB
  have rsq := relativeStageMap_isPushout h (cellBoundaryMap y hfaces)
    (Henry.SemiSSet.boundary.{u} n).ι (cellSimplexMap y hyB) sq
  exact anodyne_of_isPushout rsq (anodyne_dprismLan_boundary.{u} n)

/-- Relative stages over a finite semi-simplicial set are related by finite anodyne composites. -/
theorem anodyne_relativeStageMap_finite {W : SemiSSet.{u}} (hW : W.IsFinite)
    {A A' : Subfunctor W} (hAA' : A ≤ A') : anodyne (relativeStageMap hAA') := by
  classical
  have hmain : ∀ m : ℕ, ∀ B : Subfunctor W, (hBA' : B ≤ A') →
      (missing W B A').ncard = m → anodyne (relativeStageMap hBA') := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro A hAA' hm
      by_cases hnon : (missing W A A').Nonempty
      · let P : ℕ → Prop := fun n =>
          ∃ y : W.obj (op (Henry.SemiSimplexCategory.mk n)),
            y ∈ A'.obj (op (Henry.SemiSimplexCategory.mk n)) ∧
            y ∉ A.obj (op (Henry.SemiSimplexCategory.mk n))
        have hex : ∃ n, P n := by
          rcases hnon with ⟨⟨n, y⟩, hy⟩
          exact ⟨n, y, hy.1, hy.2⟩
        let n := Nat.find hex
        have hn : P n := Nat.find_spec hex
        have hmin : ∀ k < n, ¬ P k := fun k hk => Nat.find_min hex hk
        obtain ⟨y, hyA', hyA⟩ := hn
        have hfaces : ∀ (k : ℕ)
            (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n),
            k ≠ n → W.map θ.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)) := by
          intro k θ hkn
          have hle : k ≤ n := by
            simpa only [SimplexCategory.len_mk] using
              (@SimplexCategory.len_le_of_mono _ _ θ.1 θ.2)
          have hlt : k < n := lt_of_le_of_ne hle hkn
          have hA'face : W.map θ.op y ∈ A'.obj (op (Henry.SemiSimplexCategory.mk k)) :=
            A'.map θ.op hyA'
          by_contra hnot
          exact hmin k hlt ⟨W.map θ.op y, hA'face, hnot⟩
        let A₁ : Subfunctor W := A ⊔ Subfunctor.ofSection y
        have hAA₁ : A ≤ A₁ := le_sup_left
        have hA₁A' : A₁ ≤ A' :=
          sup_le hAA' ((Subfunctor.ofSection_le_iff y A').2 hyA')
        have hyA₁ : y ∈ A₁.obj (op (Henry.SemiSimplexCategory.mk n)) := by
          change y ∈ A.obj _ ∪ (Subfunctor.ofSection y).obj _
          exact Or.inr (Subfunctor.mem_ofSection_obj y)
        have hA₁spec : ∀ (k : ℕ)
            (z : W.obj (op (Henry.SemiSimplexCategory.mk k))),
            z ∈ A₁.obj (op (Henry.SemiSimplexCategory.mk k)) →
              z ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)) ∨
                ∃ hk : k = n, hk ▸ z = y := by
          intro k z hz
          change z ∈ A.obj _ ∪ (Subfunctor.ofSection y).obj _ at hz
          rcases hz with hzA | hzSec
          · exact Or.inl hzA
          · change ∃ f : op (Henry.SemiSimplexCategory.mk n) ⟶
                op (Henry.SemiSimplexCategory.mk k), W.map f y = z at hzSec
            obtain ⟨f, hf⟩ := hzSec
            let θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n := f.unop
            have hle : k ≤ n := by
              simpa only [SimplexCategory.len_mk] using
                (@SimplexCategory.len_le_of_mono _ _ θ.1 θ.2)
            by_cases hkn : k = n
            · subst k
              have hθ : θ = 𝟙 _ := by
                have hfun :=
                  (SemiSimplexCategory.strictMono θ).eq_id
                have hOrd : θ.1.toOrderHom = OrderHom.id _ :=
                  OrderHom.ext _ _ (by simpa using hfun)
                apply WideSubcategory.hom_ext
                apply SimplexCategory.Hom.ext
                exact hOrd
              have hfId : f = 𝟙 _ := Quiver.Hom.unop_inj hθ
              rw [hfId] at hf
              change W.map (𝟙 (op (Henry.SemiSimplexCategory.mk n))) y = z at hf
              have hmapid : W.map (𝟙 (op (Henry.SemiSimplexCategory.mk n))) = 𝟙 _ :=
                W.map_id _
              rw [hmapid] at hf
              have hyz : y = z := by simpa using hf
              exact Or.inr ⟨rfl, hyz.symm⟩
            · have hlt : k < n := lt_of_le_of_ne hle hkn
              have hface := hfaces k θ hkn
              have hf' : W.map θ.op y = z := by simpa [θ] using hf
              exact Or.inl (by simpa only [← hf'] using hface)
        have hsub : missing W A₁ A' ⊆ missing W A A' := by
          intro p hp
          exact ⟨hp.1, fun hpA => hp.2 (hAA₁ _ hpA)⟩
        have hne : missing W A₁ A' ≠ missing W A A' := by
          intro heq
          have hyOld : (⟨n, y⟩ : Σ k, W.obj (op (Henry.SemiSimplexCategory.mk k))) ∈
              missing W A A' := ⟨hyA', hyA⟩
          have hyNew := heq.symm ▸ hyOld
          exact hyNew.2 hyA₁
        have hstrict : missing W A₁ A' ⊂ missing W A A' :=
          Set.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
        have hdec : (missing W A₁ A').ncard < m := by
          rw [← hm]
          exact Set.ncard_lt_ncard hstrict (missing_finite hW A A')
        have hcell : anodyne (relativeStageMap hAA₁) :=
          anodyne_relativeStageMap_cell hAA₁ n y hyA hyA₁ hfaces hA₁spec
        have hrec : anodyne (relativeStageMap hA₁A') :=
          ih _ hdec A₁ hA₁A' rfl
        rw [← relativeStageMap_comp hAA₁ hA₁A']
        exact anodyne_comp' hcell hrec
      · have hno : ∀ p, p ∉ missing W A A' := fun p hp => hnon ⟨p, hp⟩
        have hEq : A = A' := by
          apply le_antisymm hAA'
          intro i z hz
          cases i with
          | op j =>
            cases j with
            | mk obj =>
              cases obj with
              | mk n =>
                by_contra hnot
                exact hno ⟨n, z⟩ ⟨hz, hnot⟩
        subst A'
        rw [relativeStageMap_refl]
        unfold anodyne
        exact .id _
  exact hmain _ A hAA' rfl

/-- The derived cylinder collapses onto its derived end relative to any finite subset. -/
theorem anodyne_dprismLan_rel_proof (W : SemiSSet.{u}) (J : Subfunctor W)
    (hW : W.IsFinite) :
    anodyne (pushout.desc (sdLanToDprism.app W) (dprismLan.map J.ι)
      (sdLanToDprism.naturality J.ι) :
      pushout (sdLan.map J.ι) (sdLanToDprism.app J.toFunctor) ⟶ dprismLan.obj W) := by
  let T : Subfunctor W := ⊤
  haveI : IsIso T.ι := inferInstance
  haveI : IsIso (sdLan.map T.ι) := inferInstance
  haveI : IsIso (pushout.inr (sdLan.map T.ι) (sdLanToDprism.app T.toFunctor)) :=
    inferInstance
  have htop : IsIso (relativeMap T.ι) :=
    IsIso.of_isIso_fac_left
      (f := pushout.inr (sdLan.map T.ι) (sdLanToDprism.app T.toFunctor))
      (h := dprismLan.map T.ι) (pushout.inr_desc _ _ _)
  have ht : anodyne (relativeMap T.ι) :=
    MorphismProperty.le_multiplicativeClosure _ _ (Or.inr htop)
  have hfac : relativeStageMap (le_top : J ≤ T) ≫ relativeMap T.ι = relativeMap J.ι := by
    apply pushout.hom_ext
    · simp only [relativeStageMap_inl_assoc, relativeMap, pushout.inl_desc]
    · simp only [relativeStageMap_inr_assoc, relativeMap, pushout.inr_desc, Category.assoc]
      rw [← Functor.map_comp, Subfunctor.homOfLe_ι]
  change anodyne (relativeMap J.ι)
  rw [← hfac]
  exact anodyne_comp' (anodyne_relativeStageMap_finite hW (le_top : J ≤ T)) ht

#print axioms anodyne_dprismLan_rel_proof

end HomotopyHypothesis.Approximation.DerivedPrismRelative
