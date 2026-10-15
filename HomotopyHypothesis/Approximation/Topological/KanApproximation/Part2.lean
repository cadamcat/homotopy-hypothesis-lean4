import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.KanSimplices.Part1
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.ExistsFoldedMappingCylinder
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.IsKanExtensionOfAnodyne
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.RealizationAnodyneDeformationRetract
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.SharpMkEqOfVertexMap
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.KanApproximation.Part1

/-!
# `HomotopyHypothesis.Approximation.Topological.KanApproximation`, part 2

Lines 81–205 of `HomotopyHypothesis.Approximation.Topological.KanApproximation`, split so that the modules of the development form an acyclic import graph.
-/

universe u

open CategoryTheory Limits

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- **Removing collapses in a Kan target.** A simplicial map from a finite semi-simplicial set into
the realization of a Kan semi-simplicial set, equal on `J` to the realization of `g`, is homotopic
relative to `J` to the realization of a semi-simplicial map extending `g`. Proof: in the folded
relative mapping cylinder (`exists_foldedMappingCylinder`) the identity of `X` extends first over
the prism of `J`, then, folded, over the double prism, then over all of the cylinder
(`isKan_extension_of_anodyne`); compare with the projection `ρ` using that all realized collapses
are strong deformation retractions (`realization_anodyne_deformationRetract`). -/
theorem kan_map_of_simplicial {X W J : SemiSSet.{u}} (hX : X.IsKan) (hW : W.IsFinite)
    (j : J ⟶ W) [Mono j] (g : J ⟶ X) (F : realization.obj W ⟶ realization.obj X)
    (hF : IsSimplicial F) (hjF : realization.map j ≫ F = realization.map g) :
    ∃ ψ : W ⟶ X, j ≫ ψ = g ∧
      (realization.map ψ).hom.HomotopicRel F.hom (Set.range (realization.map j).hom) := by
  obtain ⟨φ, hφ⟩ := hF
  have hφJ : ∀ (n : ℕ) (z : stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ J),
      φ.app (Opposite.op (Henry.SemiSimplexCategory.mk n)) (uliftYonedaEquiv (z ≫ j)) =
        sharpMk id (uliftYonedaEquiv (z ≫ g)) := by
    intro n z
    obtain ⟨m, x, v, h₁, h₂⟩ := hφ n (z ≫ j)
    rw [h₁]
    apply Packages.sharpMk_eq_of_vertexMap
    rw [← h₂, simplexChar_comp, Category.assoc, hjF, ← simplexChar_comp, vertexMap_id,
      Category.id_comp]
  obtain ⟨P₂, P, M, b₂, V, i, a, t, ρ₂, ρ, hb₂, hi, hja, htV, hρ₂, hiρ, haρ⟩ :=
    Packages.exists_foldedMappingCylinder hW j g F φ hφ hφJ
  obtain ⟨h₂, hh₂⟩ := Packages.isKan_extension_of_anodyne hX b₂ hb₂ (𝟙 X)
  obtain ⟨h, hh⟩ := Packages.isKan_extension_of_anodyne hX i hi (V ≫ h₂)
  refine ⟨a ≫ h, ?_, ?_⟩
  · rw [← Category.assoc, hja, Category.assoc, hh, ← Category.assoc, htV, Category.assoc, hh₂,
      Category.comp_id]
  have hr₂ : realization.map b₂ ≫ realization.map h₂ = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, hh₂, CategoryTheory.Functor.map_id]
  have H₂ := retraction_homotopicRel_of_anodyne b₂ hb₂ _ _ hr₂ hρ₂
  let R : Set (realization.obj P) :=
    {p | (realization.map V).hom p ∈ Set.range (realization.map b₂).hom}
  have HP : (realization.map V ≫ realization.map h₂).hom.HomotopicRel
      (realization.map V ≫ ρ₂).hom R := by
    simpa using homotopicRel_comp_right (S' := R) H₂ (realization.map V).hom (fun _ hp => hp)
  obtain ⟨s, hs, Hs⟩ := Packages.realization_anodyne_deformationRetract i hi
  have E₁ := homotopicRel_retraction (realization.map i) s Hs (realization.map h) s hs
  have E₂ := homotopicRel_retraction (realization.map i) s Hs ρ s hs
  have e₁ : realization.map i ≫ realization.map h = realization.map V ≫ realization.map h₂ := by
    rw [← CategoryTheory.Functor.map_comp, hh, CategoryTheory.Functor.map_comp]
  have E₃ : (s ≫ realization.map i ≫ realization.map h).hom.HomotopicRel
      (s ≫ realization.map i ≫ ρ).hom {m | s.hom m ∈ R} := by
    rw [e₁, hiρ]
    simpa using homotopicRel_comp_right (S' := {m | s.hom m ∈ R}) HP s.hom (fun _ hm => hm)
  have hsi : ∀ p, s.hom ((realization.map i).hom p) = p := fun p => by
    simpa using congrArg (fun k => k.hom p) hs
  let S : Set (realization.obj M) := Set.range (realization.map (t ≫ i)).hom
  have hS₁ : S ⊆ Set.range (realization.map i).hom := by
    rintro _ ⟨z, rfl⟩
    exact ⟨(realization.map t).hom z, by simp⟩
  have hS₂ : S ⊆ {m | s.hom m ∈ R} := by
    rintro _ ⟨z, rfl⟩
    refine ⟨(realization.map g).hom z, ?_⟩
    have h₁ := congrArg (fun k => (realization.map k).hom z) htV
    simp only [CategoryTheory.Functor.map_comp, TopCat.hom_comp, ContinuousMap.comp_apply]
      at h₁ ⊢
    rw [hsi]
    exact h₁.symm
  have Hh : (realization.map h).hom.HomotopicRel ρ.hom S :=
    (homotopicRel_mono E₁ hS₁).trans
      ((homotopicRel_mono E₃ hS₂).trans (homotopicRel_mono E₂ hS₁).symm)
  have hSa : ∀ w ∈ Set.range (realization.map j).hom, (realization.map a).hom w ∈ S := by
    rintro _ ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    have := congrArg (fun k => (realization.map k).hom z) hja
    simpa using this.symm
  have := homotopicRel_comp_right Hh (realization.map a).hom hSa
  rw [← haρ]
  simpa using this

end HomotopyHypothesis.Approximation.Topological

namespace HomotopyHypothesis.Henry.Packages

open HomotopyHypothesis.Henry.SemiSSet HomotopyHypothesis.Approximation.Topological

/-- Rourke–Sanderson, Thm. 5.3 for a given approximation; see `kan_exists_of_relPrism`. Inputs:
`exists_foldedMappingCylinder`, `sharpMk_eq_of_vertexMap`, `isKan_extension_of_anodyne`,
`realization_anodyne_deformationRetract`. -/
theorem kan_exists_of_relPrism_proof {X Y : SemiSSet.{u}} (hX : X.IsKan) (J : Subfunctor Y)
    (g : J.toFunctor ⟶ X) (S : RelPrism Y J) (f' : realization.obj S.Y' ⟶ realization.obj X)
    (hf' : IsSimplicial f') (hg : realization.map S.j ≫ f' = realization.map g) :
    ∃ φ : Y ⟶ X, J.ι ≫ φ = g ∧
      (realization.map φ).hom.HomotopicRel (realization.map S.c₁ ≫ S.ρ ≫ f').hom
        (Set.range (realization.map J.ι).hom) := by
  have := S.mono_j
  obtain ⟨ψ, hψJ, hψ⟩ := kan_map_of_simplicial hX S.finite S.j g f' hf' hg
  obtain ⟨Ψ, hΨ⟩ := isKan_extension_of_anodyne hX S.c₀ S.anodyne_c₀ ψ
  refine ⟨S.c₁ ≫ Ψ, ?_, ?_⟩
  · rw [← Category.assoc, ← S.hc, Category.assoc, hΨ, hψJ]
  have h₃ := homotopicRel_of_anodyne S.c₀ S.anodyne_c₀ (realization.map Ψ) S.ρ S.hρ₀
  have hS₁ : ∀ t ∈ Set.range (realization.map J.ι).hom,
      (realization.map S.c₁).hom t ∈ Set.range (realization.map S.c₀).hom := by
    rintro _ ⟨t, rfl⟩
    refine ⟨(realization.map S.j).hom t, ?_⟩
    have := congrArg (fun k => (realization.map k).hom t) S.hc
    simpa using this
  have h₄ := homotopicRel_comp_right h₃ (realization.map S.c₁).hom hS₁
  have e₄ : (realization.map S.c₁ ≫ S.ρ ≫ realization.map S.c₀ ≫ realization.map Ψ) =
      (realization.map S.c₁ ≫ S.ρ) ≫ realization.map ψ := by
    rw [← CategoryTheory.Functor.map_comp, hΨ, Category.assoc]
  have h₄' : (realization.map (S.c₁ ≫ Ψ)).hom.HomotopicRel
      ((realization.map S.c₁ ≫ S.ρ) ≫ realization.map ψ).hom
        (Set.range (realization.map J.ι).hom) := by
    rw [← e₄, CategoryTheory.Functor.map_comp]
    simpa using h₄
  have hS₂ : ∀ t ∈ Set.range (realization.map J.ι).hom,
      (realization.map S.c₁ ≫ S.ρ).hom t ∈ Set.range (realization.map S.j).hom := by
    rintro _ ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    have h₁ := congrArg (fun k => (realization.map k ≫ S.ρ).hom t) S.hc
    have h₂ := congrArg (fun k => (realization.map S.j ≫ k).hom t) S.hρ₀
    simp only [CategoryTheory.Functor.map_comp, Category.assoc, TopCat.hom_comp,
      ContinuousMap.comp_apply] at h₁ h₂
    simp only [TopCat.hom_comp, ContinuousMap.comp_apply]
    rw [← h₁, h₂]
    rfl
  have h₅ := homotopicRel_comp_right hψ (realization.map S.c₁ ≫ S.ρ).hom hS₂
  have h₅' : ((realization.map S.c₁ ≫ S.ρ) ≫ realization.map ψ).hom.HomotopicRel
      (realization.map S.c₁ ≫ S.ρ ≫ f').hom (Set.range (realization.map J.ι).hom) := by
    simpa using h₅
  exact h₄'.trans h₅'
