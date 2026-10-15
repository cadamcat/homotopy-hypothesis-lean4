import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Cylinder.BoundaryDescription.BoundaryDesc
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderCells.BotBdry
import HomotopyHypothesis.Approximation.Topological.CylinderCells.ElFaceHom
import HomotopyHypothesis.Approximation.Topological.CylinderCells.ElOf
import HomotopyHypothesis.Approximation.Topological.CylinderCells.FaceBdry
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundary
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundaryComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57
import HomotopyHypothesis.Approximation.Topological.DerivedCylinderMap
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder
import HomotopyHypothesis.Approximation.Topological.NormalForm.NF

/-!
# `HomotopyHypothesis.Cylinder.BoundaryExtension.BoundaryHomExt`, part 1

Lines 15–195 of `HomotopyHypothesis.Cylinder.BoundaryExtension.BoundaryHomExt`, split so that the modules of the development form an acyclic import graph.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Cylinder.BoundaryExtension

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological
open HomotopyHypothesis.Cylinder.BoundaryDescription

variable {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)

theorem dcylDBoundary_hom_ext_proof {n : ℕ}
    (y : W.obj (op (Henry.SemiSimplexCategory.mk n))) {Z : SemiSSet.{u}}
    (g₁ g₂ : dcylDBoundary.{u} (elNF φ (elOf y)).v ⟶ Z)
    (hface : ∀ (k : ℕ) (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n)
      (hk : k ≠ n),
        (faceBdry φ y θ hk).toSemiSSet ≫ g₁ = (faceBdry φ y θ hk).toSemiSSet ≫ g₂)
    (hbot : botBdry (elNF φ (elOf y)).v ≫ g₁ =
      botBdry (elNF φ (elOf y)).v ≫ g₂) :
    g₁ = g₂ := by
  classical
  ext k σ
  let nf := elNF φ (elOf y)
  let v := nf.v
  let w := σ.down.1
  let R := Finset.univ.image w
  have hbdry : (dcylDBoundaryComplex v).S R := by
    simpa [v, w, R, nf] using σ.down.2.2
  have hSymm : uliftYonedaEquiv.symm σ =
      (dcylDBoundaryComplex v).simplexMap w σ.down.2.1 hbdry := by rfl
  apply (Equiv.injective (uliftYonedaEquiv.symm))
  have hYon₁ : uliftYonedaEquiv.symm σ ≫ g₁ =
      uliftYonedaEquiv.symm ((g₁.app k) σ) := by
    simpa using (uliftYonedaEquiv_symm_comp (X := k) σ g₁)
  have hYon₂ : uliftYonedaEquiv.symm σ ≫ g₂ =
      uliftYonedaEquiv.symm ((g₂.app k) σ) := by
    simpa using (uliftYonedaEquiv_symm_comp (X := k) σ g₂)
  change uliftYonedaEquiv.symm ((g₁.app k) σ) =
    uliftYonedaEquiv.symm ((g₂.app k) σ)
  rw [← hYon₁, ← hYon₂]
  by_cases hbotSupport : ∀ a ∈ R, ∃ c, a = DV.bot c
  · let c := botCode w
    have hc : StrictMono c := botCode_strict hbotSupport σ.down.2.1
    have hlist : w = fun j => DV.bot (c j) := by
      funext j
      exact botCode_spec hbotSupport j
    let b : Fin (nf.m + 1) → DV n nf.m := fun c => DV.bot c
    have hb : StrictMono b := by
      intro i j hij
      exact DV.bot_lt_bot.2 hij
    have hbS : (dcylDBoundaryComplex v).S (Finset.univ.image b) := by
      refine ⟨⟨by simp, by simp, by simp, by simp, by simp⟩, Or.inl ?_⟩
      intro a ha
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ha
      exact ⟨i, hi.symm⟩
    let β := vhom c hc
    have hlist' : w = b ∘ β.1.toOrderHom := by
      funext j
      change w j = DV.bot (c j)
      rw [hlist]
    have hcompStrict : StrictMono (b ∘ β.1.toOrderHom) :=
      hb.comp (SemiSimplexCategory.strictMono β)
    have hsubset : Finset.univ.image (b ∘ β.1.toOrderHom) ⊆
        Finset.univ.image b := by
      intro a ha
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha ⊢
      obtain ⟨i, rfl⟩ := ha
      exact ⟨β.1.toOrderHom i, rfl⟩
    have hcompS : (dcylDBoundaryComplex v).S
        (Finset.univ.image (b ∘ β.1.toOrderHom)) :=
      (dcylDBoundaryComplex v).down hsubset hbS
    have hFactor : uliftYonedaEquiv.symm σ =
        Henry.SemiSSet.stdSimplex.map β ≫ botBdry v := by
      rw [hSymm]
      calc
        (dcylDBoundaryComplex v).simplexMap w σ.down.2.1 hbdry =
            (dcylDBoundaryComplex v).simplexMap
              (b ∘ β.1.toOrderHom) hcompStrict hcompS :=
          simplexMap_congr hlist' σ.down.2.1 hbdry hcompStrict hcompS
        _ = Henry.SemiSSet.stdSimplex.map β ≫ botBdry v := by
          simpa [botBdry, b] using (simplexMap_precomp β b hb hbS).symm
    calc
      uliftYonedaEquiv.symm σ ≫ g₁ =
          (Henry.SemiSSet.stdSimplex.map β ≫ botBdry v) ≫ g₁ := by rw [hFactor]
      _ = (Henry.SemiSSet.stdSimplex.map β ≫ botBdry v) ≫ g₂ := by
        calc
          (Henry.SemiSSet.stdSimplex.map β ≫ botBdry v) ≫ g₁ =
              Henry.SemiSSet.stdSimplex.map β ≫ (botBdry v ≫ g₁) := by cat_disch
          _ = Henry.SemiSSet.stdSimplex.map β ≫ (botBdry v ≫ g₂) :=
            congrArg (fun q => Henry.SemiSSet.stdSimplex.map β ≫ q) hbot
          _ = (Henry.SemiSSet.stdSimplex.map β ≫ botBdry v) ≫ g₂ := by cat_disch
      _ = uliftYonedaEquiv.symm σ ≫ g₂ := by rw [← hFactor]
  · have hnot : ¬ ∀ a ∈ R, ∃ c, a = DV.bot c := hbotSupport
    let nf0 := elNF φ (elOf y)
    let v0 := nf0.v
    have hbdry0 : (dcylDBoundaryComplex v0).S R := by
      simpa [v0, v, R, nf0, w] using hbdry
    have hR : (dcylDComplex v0).S R := hbdry0.1
    let F := dcylCarrier R
    have hF : F.Nonempty := dcylCarrier_nonempty_of_not_bottom hR hnot
    have hFcard : F.card ≤ n := dcylCarrier_card_le_of_boundary hbdry0 hnot
    have hθn : faceDim F ≠ n := faceHom_ne F hF hFcard
    let θ := faceHom F hF
    let z := W.map θ.op y
    let iotaF := elι φ (elFaceHom y θ)
    let thetaEmbF : Fin (faceDim F + 1) ↪ Fin (n + 1) := semiEmb θ
    let iotaEmbF : Fin ((elNF φ (elOf z)).m + 1) ↪ Fin (nf0.m + 1) := semiEmb iotaF
    have hThetaEqF : thetaEmbF = (faceEmb F hF).toEmbedding := by
      ext j
      rfl
    have hThetaImgF : Finset.univ.image thetaEmbF = F := by
      rw [hThetaEqF]
      exact faceEmb_image F hF
    have hvF : v0 ∘ thetaEmbF = iotaEmbF ∘ (elNF φ (elOf z)).v := by
      change v0 ∘ θ.1.toOrderHom = iotaF.1.toOrderHom ∘ (elNF φ (elOf z)).v
      exact (elι_spec φ (elFaceHom y θ)).1
    let pullF := pullDV thetaEmbF iotaEmbF
    have hpullF : ∀ j, DV.mapV thetaEmbF iotaEmbF (pullF (w j)) = w j := by
      intro j
      have hjR : w j ∈ R := Finset.mem_image_of_mem _ (Finset.mem_univ j)
      cases h : w j with
      | top i =>
          have hiR : DV.top i ∈ R := by rw [← h]; exact hjR
          have hiF : i ∈ F := mem_dcylCarrier_top hiR
          have hiImg : i ∈ Finset.univ.image thetaEmbF := by rw [hThetaImgF]; exact hiF
          obtain ⟨d, -, hdi⟩ := Finset.mem_image.mp hiImg
          exact mapV_pullDV_top thetaEmbF iotaEmbF ⟨d, hdi⟩
      | mid T =>
          have hTR : DV.mid T ∈ R := by rw [← h]; exact hjR
          have hTF : T ⊆ F := subset_dcylCarrier_mid hTR
          have hTImg : T ⊆ Finset.univ.image thetaEmbF := by rw [hThetaImgF]; exact hTF
          exact mapV_pullDV_mid thetaEmbF iotaEmbF hTImg
      | bot c =>
          have hcR : DV.bot c ∈ R := by rw [← h]; exact hjR
          obtain ⟨T, hTR⟩ := exists_mid_of_bot_nonbottom hR hnot hcR
          obtain ⟨a, ha, hva⟩ := hR.2.2.2.2 c T hcR hTR
          have haF : a ∈ F := subset_dcylCarrier_mid hTR ha
          have haImg : a ∈ Finset.univ.image thetaEmbF := by rw [hThetaImgF]; exact haF
          obtain ⟨d, -, hda⟩ := Finset.mem_image.mp haImg
          have hvd := congrFun hvF d
          have hcImage : ∃ e, iotaEmbF e = c := by
            refine ⟨(elNF φ (elOf z)).v d, ?_⟩
            calc
              iotaEmbF ((elNF φ (elOf z)).v d) = v0 (thetaEmbF d) := hvd.symm
              _ = v0 a := by rw [hda]
              _ = c := hva
          exact mapV_pullDV_bot thetaEmbF iotaEmbF hcImage
    have hlocal := pullSimplex thetaEmbF (semiEmb_strictMono θ) iotaEmbF
      (semiEmb_strictMono iotaF) hvF R hR w rfl σ.down.2.1 pullF hpullF
    let wLocal := pullF ∘ w
    have hfun : (faceBdry φ y θ hθn).f ∘ wLocal = w := by
      funext j
      change DV.mapV thetaEmbF iotaEmbF (pullF (w j)) = w j
      exact hpullF j
    have hlocalStrict : StrictMono ((faceBdry φ y θ hθn).f ∘ wLocal) := by
      intro i j hij
      apply (faceBdry φ y θ hθn).strictMonoOn _ hlocal.2
      · exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      · exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
      · exact hlocal.1 hij
    have hlocalS : (dcylDBoundaryComplex v0).S
        (Finset.univ.image ((faceBdry φ y θ hθn).f ∘ wLocal)) := by
      simpa [Finset.image_image] using
        (faceBdry φ y θ hθn).map_S _ hlocal.2
    have hFactor : uliftYonedaEquiv.symm σ =
        (dcylDComplex (elNF φ (elOf z)).v).simplexMap wLocal hlocal.1 hlocal.2 ≫
          (faceBdry φ y θ hθn).toSemiSSet := by
      rw [hSymm]
      calc
        (dcylDBoundaryComplex v0).simplexMap w σ.down.2.1 hbdry0 =
            (dcylDBoundaryComplex v0).simplexMap
              ((faceBdry φ y θ hθn).f ∘ wLocal) hlocalStrict hlocalS := by
          exact simplexMap_congr hfun.symm σ.down.2.1 hbdry0 hlocalStrict hlocalS
        _ = (dcylDComplex (elNF φ (elOf z)).v).simplexMap wLocal hlocal.1 hlocal.2 ≫
              (faceBdry φ y θ hθn).toSemiSSet := by
          symm
          exact simplexMap_compHom (faceBdry φ y θ hθn) wLocal hlocal.1 hlocal.2
    calc
      uliftYonedaEquiv.symm σ ≫ g₁ =
          ((dcylDComplex (elNF φ (elOf z)).v).simplexMap wLocal hlocal.1 hlocal.2 ≫
            (faceBdry φ y θ hθn).toSemiSSet) ≫ g₁ := by rw [hFactor]
      _ = (dcylDComplex (elNF φ (elOf z)).v).simplexMap wLocal hlocal.1 hlocal.2 ≫
            ((faceBdry φ y θ hθn).toSemiSSet ≫ g₁) := by cat_disch
      _ = (dcylDComplex (elNF φ (elOf z)).v).simplexMap wLocal hlocal.1 hlocal.2 ≫
            ((faceBdry φ y θ hθn).toSemiSSet ≫ g₂) :=
        congrArg (fun q =>
          (dcylDComplex (elNF φ (elOf z)).v).simplexMap wLocal hlocal.1 hlocal.2 ≫ q)
          (hface (faceDim F) θ hθn)
      _ = ((dcylDComplex (elNF φ (elOf z)).v).simplexMap wLocal hlocal.1 hlocal.2 ≫
            (faceBdry φ y θ hθn).toSemiSSet) ≫ g₂ := by cat_disch
      _ = uliftYonedaEquiv.symm σ ≫ g₂ := by rw [← hFactor]
