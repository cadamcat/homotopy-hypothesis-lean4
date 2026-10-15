import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Main.Part1
import HomotopyHypothesis.Blueprint.Henry.Main.Part2
import HomotopyHypothesis.Blueprint.Henry.Packages.Classical.ContractibleSpaceToTopZero
import HomotopyHypothesis.Blueprint.Henry.Packages.Classical.FinCellIsCylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.Classical.HomotopyEquivalenceOfContractibleSpace
import HomotopyHypothesis.Blueprint.Henry.Packages.Classical.IsCylinderMorphismToFinCell
import HomotopyHypothesis.Blueprint.Henry.Packages.General.CompletionIsSemiModelCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.General.IsAcyclicId
import HomotopyHypothesis.Blueprint.Henry.Packages.General.IsAcyclicIffOfIsCylinderCoherator
import HomotopyHypothesis.Blueprint.Henry.Packages.General.IsAcyclicTwoOutOfSix
import HomotopyHypothesis.Blueprint.Henry.Packages.General.LocalizationOfIsQuillenEquivalence
import HomotopyHypothesis.Blueprint.Henry.Packages.General.ToTerminalCatIsLiftingTarget
import HomotopyHypothesis.Blueprint.Henry.Packages.Localization.CompletionRestrictionIsQuillenEquivalence
import HomotopyHypothesis.Blueprint.Henry.Packages.Localization.CompletionRestrictionIsRightAdjoint
import HomotopyHypothesis.Blueprint.Henry.Packages.Localization.IsLocalizedEquivalenceOfAdjunction
import HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial.CDeltaIsCylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial.CDeltaIsCylinderCoherator
import HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial.ExistsFreePoint
import HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial.ExistsStandardRealization
import HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial.StandardRealizationIsAcyclic
import HomotopyHypothesis.Blueprint.Henry.Packages.Spaces.FinCellRestrictionIsRightAdjoint
import HomotopyHypothesis.Blueprint.Henry.Packages.Spaces.FinCellRestrictionUnitWeakEquivalence
import HomotopyHypothesis.Blueprint.Henry.Packages.Spaces.FinCellRestrictionWeakEquivalenceIff
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.FinCellEssentiallySmall
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.IsCellularRealizationFinCellIota
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology

/-!
# `HomotopyHypothesis.Blueprint.Henry.Main`, part 3

Lines 86–231 of `HomotopyHypothesis.Blueprint.Henry.Main`, split so that the modules of the development form an acyclic import graph.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry

section Lemmas

variable {C : Type*} [Category C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
  {D : Type*} [Category D] [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]
  {E : Type*} [Category E] [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]

/-- A cylinder coherator maps to every cylinder category (in its universes), sending the marked
object to any given object (lifting against `D ⥤ *`, H:2045). -/
theorem exists_morphism_of_isCylinderCoherator {𝒜 : Type (u + 1)} [Category.{u} 𝒜]
    [CategoryWithCofibrations 𝒜] [CategoryWithWeakEquivalences 𝒜] {o : 𝒜}
    (h𝒜 : IsCylinderCoherator.{u + 1, u} 𝒜 o) {𝒟 : Type (u + 1)} [Category.{u} 𝒟]
    [CategoryWithCofibrations 𝒟] [CategoryWithWeakEquivalences 𝒟] [IsCylinderCategory 𝒟]
    (d : 𝒟) : ∃ Φ : 𝒜 ⥤ 𝒟, IsCylinderMorphism Φ ∧ Φ.obj o = d := by
  obtain ⟨l, hl, -, hlo⟩ := h𝒜.2 𝒟 TerminalCat.{u} (toTerminalCat 𝒟)
    Packages.toTerminalCat_isLiftingTarget d trivial (toTerminalCat 𝒜)
    toTerminalCat_isCylinderMorphism rfl
  exact ⟨l, hl, hlo⟩

/-- H Prop 4.3.2 (H:2549): a morphism between cylinder coherators preserving the marked objects is
acyclic. -/
theorem isAcyclic_of_isCylinderCoherator {𝒜 : Type (u + 1)} [Category.{u} 𝒜]
    [CategoryWithCofibrations 𝒜] [CategoryWithWeakEquivalences 𝒜] {o : 𝒜}
    (h𝒜 : IsCylinderCoherator.{u + 1, u} 𝒜 o) {ℬ : Type (u + 1)} [Category.{u} ℬ]
    [CategoryWithCofibrations ℬ] [CategoryWithWeakEquivalences ℬ] {b : ℬ}
    (hℬ : IsCylinderCoherator.{u + 1, u} ℬ b) {Φ : 𝒜 ⥤ ℬ} (hΦ : IsCylinderMorphism Φ)
    (hΦo : Φ.obj o = b) : IsAcyclic Φ := by
  have := h𝒜.1
  have := hℬ.1
  obtain ⟨Ψ, hΨ, hΨb⟩ := exists_morphism_of_isCylinderCoherator hℬ o
  have e₁ : (Φ ⋙ Ψ).obj o = o := by simp [hΦo, hΨb]
  have e₂ : (Ψ ⋙ Φ).obj b = b := by simp [hΦo, hΨb]
  have h₁ : IsAcyclic (Φ ⋙ Ψ) :=
    (Packages.isAcyclic_iff_of_isCylinderCoherator h𝒜 (hΦ.comp hΨ) IsCylinderMorphism.id
      (eqToHom e₁) (𝟙 o) (weakEquivalence_of_isIso _)
      (IsCylinderCategory.weakEquivalences_isMultiplicative.toContainsIdentities.id_mem o)).2
      Packages.isAcyclic_id
  have h₂ : IsAcyclic (Ψ ⋙ Φ) :=
    (Packages.isAcyclic_iff_of_isCylinderCoherator hℬ (hΨ.comp hΦ) IsCylinderMorphism.id
      (eqToHom e₂) (𝟙 b) (weakEquivalence_of_isIso _)
      (IsCylinderCategory.weakEquivalences_isMultiplicative.toContainsIdentities.id_mem b)).2
      Packages.isAcyclic_id
  exact (Packages.isAcyclic_twoOutOfSix Φ Ψ Φ hΦ hΨ hΦ h₁ h₂).1

/-- The simplicial anchor (H §5.2): there is a cylinder coherator with an acyclic cellular
realization whose value at the marked object is contractible. -/
theorem exists_acyclic_anchor :
    ∃ (b : CDelta.{u}) (R : CDelta.{u} ⥤ TopCat.{u}) (hR : IsCellularRealization R),
      IsCylinderCoherator.{u + 1, u} CDelta.{u} b ∧ ContractibleSpace (R.obj b) ∧
        IsAcyclic hR.toFinCell := by
  obtain ⟨b, η, hη⟩ := Packages.exists_free_point.{u}
  obtain ⟨R, hR⟩ := Packages.exists_standardRealization.{u}
  obtain ⟨e, -⟩ := hR.simplex
  have := Packages.contractibleSpace_toTop_zero.{u}
  exact ⟨b, R, hR.isCellularRealization, Packages.cDelta_isCylinderCoherator b η hη,
    (TopCat.homeoOfIso (e 0 b η hη)).contractibleSpace,
    Packages.standardRealization_isAcyclic hR⟩

/-- H Prop 2.4.16(3) with H:356–364: for an acyclic cellular realization `G` of an essentially
small cylinder category `𝒜`, restriction `FinCell̃ ⥤ 𝒜̃` along its corestriction to finite cell
complexes preserves weak equivalences and induces an equivalence of localizations. -/
theorem completionRestriction_isLocalizedEquivalence {𝒜 : Type (u + 1)} [Category.{u} 𝒜]
    [CategoryWithCofibrations 𝒜] [CategoryWithWeakEquivalences 𝒜] [IsCylinderCategory 𝒜]
    [EssentiallySmall.{u} 𝒜] {G : 𝒜 ⥤ TopCat.{u}} (hG : IsCellularRealization G)
    (hac : IsAcyclic hG.toFinCell) :
    ∃ h : Completion.weakEquivalences FinCell.{u} ≤
        (Completion.weakEquivalences 𝒜).inverseImage (Completion.restriction.{u} hG.toFinCell
          (Packages.isCylinderMorphism_toFinCell hG).toIsCofibrationMorphism),
      (LocalizerMorphism.mk _ h).IsLocalizedEquivalence := by
  have := Packages.finCell_isCylinderCategory.{u}
  have := Packages.finCell_essentiallySmall.{u}
  have hF := Packages.isCylinderMorphism_toFinCell hG
  obtain ⟨L, ⟨adj⟩⟩ := (Packages.completionRestriction_isRightAdjoint.{u}
    hF.toIsCofibrationMorphism).exists_leftAdjoint
  have hQ := Packages.completionRestriction_isQuillenEquivalence hF hac adj
  have hloc := Packages.localization_of_isQuillenEquivalence
    (Packages.completion_isSemiModelCategory (C := 𝒜)).1
    (Packages.completion_isSemiModelCategory (C := FinCell.{u})).1
    (Packages.completion_isSemiModelCategory (C := FinCell.{u})).2 adj hQ
  refine ⟨hloc.1, ⟨?_⟩⟩
  let Φ : LocalizerMorphism (Completion.weakEquivalences FinCell.{u})
      (Completion.weakEquivalences 𝒜) := ⟨_, hloc.1⟩
  exact hloc.2 _ _ (Φ.localizedFunctor (Completion.weakEquivalences FinCell.{u}).Q
    (Completion.weakEquivalences 𝒜).Q) (Φ.catCommSq _ _).iso.symm

/-- H Prop 2.4.18 (H:1432–1440), repaired without a model structure on spaces: restriction
`TopCat ⥤ FinCell̃` along the inclusion of finite cell complexes preserves and reflects weak
equivalences and induces an equivalence of localizations. -/
theorem finCellRestriction_isLocalizedEquivalence
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u})) :
    ∃ h : Top.weakEquivalences.{u} ≤
        (Completion.weakEquivalences FinCell.{u}).inverseImage (topRestriction hι),
      (LocalizerMorphism.mk _ h).IsLocalizedEquivalence := by
  have := Packages.finCell_isCylinderCategory.{u}
  have := Packages.finCell_essentiallySmall.{u}
  have hR : Top.weakEquivalences.{u} =
      (Completion.weakEquivalences FinCell.{u}).inverseImage (topRestriction hι) := by
    ext X Y f
    exact Packages.finCellRestriction_weakEquivalence_iff hι f
  obtain ⟨L, ⟨adj⟩⟩ := (Packages.finCellRestriction_isRightAdjoint hι).exists_leftAdjoint
  have hC := Packages.completion_isSemiModelCategory (C := FinCell.{u})
  exact ⟨(LocalizerMorphism.ofEq hR).map, Packages.isLocalizedEquivalence_of_adjunction hC.1 hC.2
    adj hR (fun X hX => Packages.finCellRestriction_unit_weakEquivalence hι adj X hX)⟩

end Lemmas

/-- **Henry's comparison with spaces** (H Thm 5.1.2(5), H:2765–2798, with the repairs of
H Props 2.4.18, 4.4.4, 5.2.9 and of the uniqueness claim). Let `𝒜` be an essentially small cylinder
coherator with marked object `o`, and `G : 𝒜 ⥤ TopCat` a cellular realization with `G o`
contractible. Then the fundamental `∞`-groupoid functor `π_∞ = R_G : TopCat ⥤ 𝒜̃` sends weak
homotopy equivalences to weak equivalences of the completion, and the induced functor between
localizations is an equivalence. -/
theorem comparison_with_spaces {𝒜 : Type (u + 1)} [Category.{u} 𝒜] [CategoryWithCofibrations 𝒜]
    [CategoryWithWeakEquivalences 𝒜] [EssentiallySmall.{u} 𝒜] (o : 𝒜)
    (h𝒜 : IsCylinderCoherator.{u + 1, u} 𝒜 o) (G : 𝒜 ⥤ TopCat.{u})
    (hG : IsCellularRealization G) (ho : ContractibleSpace (G.obj o)) :
    Top.weakEquivalences ≤ (Completion.weakEquivalences 𝒜).inverseImage (topRestriction hG) ∧
    ∀ {H₁ : Type*} {H₂ : Type*} [Category H₁] [Category H₂] (L₁ : TopCat.{u} ⥤ H₁)
      [L₁.IsLocalization Top.weakEquivalences] (L₂ : Completion.{u} 𝒜 ⥤ H₂)
      [L₂.IsLocalization (Completion.weakEquivalences 𝒜)] (Φ : H₁ ⥤ H₂),
      (L₁ ⋙ Φ ≅ topRestriction hG ⋙ L₂) → Φ.IsEquivalence := by
  have := h𝒜.1
  have := Packages.cDelta_isCylinderCategory.{u}
  have := Packages.finCell_isCylinderCategory.{u}
  obtain ⟨b, R, hR, hb, hRb, hRac⟩ := exists_acyclic_anchor.{u}
  obtain ⟨Φ, hΦ, hΦo⟩ := exists_morphism_of_isCylinderCoherator h𝒜 b
  have hΦac : IsAcyclic Φ := isAcyclic_of_isCylinderCoherator h𝒜 hb hΦ hΦo
  -- the composite `Φ ⋙ R` is an acyclic cellular realization
  have hR' := Packages.isCylinderMorphism_toFinCell hR
  have hG'' : IsCellularRealization (Φ ⋙ R) := IsCellularRealization.comp hΦ hR
  have hG''ac : IsAcyclic hG''.toFinCell := isAcyclic_comp hΦ hR' hΦac hRac
  -- hence so is `G`, whose value at `o` is weakly equivalent to that of `Φ ⋙ R`
  have hc : ContractibleSpace ((Φ ⋙ R).obj o) := by
    rw [Functor.comp_obj, hΦo]
    exact hRb
  obtain ⟨y⟩ : Nonempty ((Φ ⋙ R).obj o) := inferInstance
  have hGac : IsAcyclic hG.toFinCell := by
    refine (Packages.isAcyclic_iff_of_isCylinderCoherator h𝒜
      (Packages.isCylinderMorphism_toFinCell hG) (Packages.isCylinderMorphism_toFinCell hG'')
      (X := hG''.toFinCell.obj o)
      (ObjectProperty.homMk (TopCat.ofHom (ContinuousMap.const _ y))) (𝟙 _)
      (@Packages.homotopyEquivalence_of_contractibleSpace _ _ ho hc _)
      (weakEquivalence_of_isIso _)).2 hG''ac
  -- an acyclic cellular realization induces an equivalence of localizations with spaces
  obtain ⟨h₁, h₁'⟩ := finCellRestriction_isLocalizedEquivalence Packages.isCellularRealization_finCellι
  obtain ⟨h₂, h₂'⟩ := completionRestriction_isLocalizedEquivalence hG hGac
  let Ψ := (LocalizerMorphism.mk _ h₁).comp (LocalizerMorphism.mk _ h₂)
  have hΨ : Ψ.IsLocalizedEquivalence := inferInstance
  refine ⟨fun X Y f hf => Ψ.map f hf, ?_⟩
  intro H₁ H₂ _ _ L₁ _ L₂ _ Φ' e
  have : CatCommSq Ψ.functor L₁ L₂ Φ' := ⟨e.symm⟩
  exact Ψ.isEquivalence L₁ L₂ Φ'
