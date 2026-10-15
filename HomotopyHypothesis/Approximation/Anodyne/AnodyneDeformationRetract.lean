import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.Packages.Classical.RealizationHornCellsDeformationRetract
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Anodyne

open HomotopyHypothesis.Henry
open SemiSSet

private theorem homotopicRel_comp_right {X' X Y : Type*} [TopologicalSpace X']
    [TopologicalSpace X] [TopologicalSpace Y] {f₀ f₁ : C(X, Y)} {S : Set X}
    (h : f₀.HomotopicRel f₁ S) (g : C(X', X)) {S' : Set X'}
    (hS : ∀ x ∈ S', g x ∈ S) : (f₀.comp g).HomotopicRel (f₁.comp g) S' := by
  obtain ⟨F⟩ := h
  exact ⟨{ toHomotopy := F.toHomotopy.comp (ContinuousMap.Homotopy.refl g)
           prop' := fun t x hx => by simpa using F.eq_fst t (hS x hx) }⟩

private theorem homotopicRel_of_subset {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f₀ f₁ : C(X, Y)} {S T : Set X}
    (h : f₀.HomotopicRel f₁ T) (hST : S ⊆ T) : f₀.HomotopicRel f₁ S := by
  obtain ⟨F⟩ := h
  exact ⟨{ toHomotopy := F.toHomotopy
           prop' := fun t x hx => F.prop t x (hST hx) }⟩

private theorem deformationRetract_comp {A B C : TopCat.{u}}
    {f : A ⟶ B} {g : B ⟶ C} (r₁ : B ⟶ A)
    (hr₁ : f ≫ r₁ = 𝟙 A)
    (h₁ : (r₁ ≫ f).hom.HomotopicRel (ContinuousMap.id B) (Set.range f.hom))
    (r₂ : C ⟶ B) (hr₂ : g ≫ r₂ = 𝟙 B)
    (h₂ : (r₂ ≫ g).hom.HomotopicRel (ContinuousMap.id C) (Set.range g.hom)) :
    ∃ r : C ⟶ A, (f ≫ g) ≫ r = 𝟙 A ∧
      (r ≫ (f ≫ g)).hom.HomotopicRel (ContinuousMap.id C)
        (Set.range (f ≫ g).hom) := by
  refine ⟨r₂ ≫ r₁, ?_, ?_⟩
  · calc
      (f ≫ g) ≫ (r₂ ≫ r₁) = f ≫ (g ≫ r₂) ≫ r₁ := by simp [Category.assoc]
      _ = f ≫ 𝟙 B ≫ r₁ := by rw [hr₂]
      _ = 𝟙 A := by simp [hr₁]
  · let S := Set.range (f ≫ g).hom
    have hS : ∀ x ∈ S, r₂.hom x ∈ Set.range f.hom := by
      rintro x ⟨a, rfl⟩
      refine ⟨a, ?_⟩
      have heval := congrArg (fun q : B ⟶ B => q.hom (f.hom a)) hr₂
      simpa using heval.symm
    have hFirstRaw :=
      (homotopicRel_comp_right h₁ r₂.hom hS).comp_continuousMap g.hom
    have hFirst : (r₂ ≫ r₁ ≫ f ≫ g).hom.HomotopicRel
        (r₂ ≫ g).hom S := by
      simpa [Category.assoc] using hFirstRaw
    have hSecondSubset : S ⊆ Set.range g.hom := by
      rintro x ⟨a, rfl⟩
      exact ⟨f.hom a, by simp⟩
    have hSecond := homotopicRel_of_subset h₂ hSecondSubset
    exact hFirst.trans hSecond

private def hornCells : MorphismProperty SemiSSet.{u} :=
  (MorphismProperty.coproducts.{u} hornInclusions).pushouts

private theorem hornPushouts_le_hornCells :
    hornInclusions.pushouts ≤ MorphismProperty.transfiniteCompositions.{u} hornCells := by
  exact (MorphismProperty.pushouts_monotone (MorphismProperty.le_coproducts hornInclusions)).trans
    (MorphismProperty.le_transfiniteCompositions hornCells)

private theorem generator_deformationRetract {A B : SemiSSet.{u}} (j : A ⟶ B)
    (hj : (hornInclusions.pushouts ⊔ MorphismProperty.isomorphisms SemiSSet.{u}) j) :
    ∃ r : realization.obj B ⟶ realization.obj A, realization.map j ≫ r = 𝟙 _ ∧
      (r ≫ realization.map j).hom.HomotopicRel (ContinuousMap.id _)
        (Set.range (realization.map j).hom) := by
  rcases hj with hj | hj
  · exact HomotopyHypothesis.Henry.Packages.realization_hornCells_deformationRetract j
      (hornPushouts_le_hornCells j hj)
  · letI : IsIso j := hj
    refine ⟨realization.map (inv j), ?_, ?_⟩
    · simp
    · have h : realization.map (inv j) ≫ realization.map j = 𝟙 _ := by simp
      rw [h]
      exact ContinuousMap.HomotopicRel.refl _

theorem realization_anodyne_deformationRetract_proof {A B : SemiSSet.{u}} (j : A ⟶ B)
    (hj : anodyne j) :
    ∃ r : realization.obj B ⟶ realization.obj A, realization.map j ≫ r = 𝟙 _ ∧
      (r ≫ realization.map j).hom.HomotopicRel (ContinuousMap.id _)
        (Set.range (realization.map j).hom) := by
  let G : MorphismProperty SemiSSet.{u} :=
    hornInclusions.pushouts ⊔ MorphismProperty.isomorphisms SemiSSet.{u}
  change G.multiplicativeClosure j at hj
  induction hj with
  | of f hf => exact generator_deformationRetract f hf
  | id X =>
      refine ⟨𝟙 _, by simp, ?_⟩
      simpa using ContinuousMap.HomotopicRel.refl (ContinuousMap.id _)
  | comp_of f g hf hg ih =>
      obtain ⟨r₁, hr₁, h₁⟩ := ih
      obtain ⟨r₂, hr₂, h₂⟩ := generator_deformationRetract g hg
      simpa only [Functor.map_comp] using deformationRetract_comp r₁ hr₁ h₁ r₂ hr₂ h₂

#print axioms realization_anodyne_deformationRetract_proof

end HomotopyHypothesis.Approximation.Anodyne
