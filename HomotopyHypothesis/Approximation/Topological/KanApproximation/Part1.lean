import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.RealizationAnodyneDeformationRetract
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial

/-!
# `HomotopyHypothesis.Approximation.Topological.KanApproximation`, part 1

Lines 23–80 of `HomotopyHypothesis.Approximation.Topological.KanApproximation`, split so that the modules of the development form an acyclic import graph.
-/

universe u

open CategoryTheory Limits

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- If `s` is a retraction of `i` with `s ≫ i` homotopic to the identity relative to the image of
`i`, then every map `Φ` out of the target of `i` is homotopic relative to that image to
`ρ ≫ i ≫ Φ`, for any retraction `ρ` of `i`. -/
theorem homotopicRel_retraction {A B T : TopCat.{u}} (i : A ⟶ B) (s : B ⟶ A)
    (H : (s ≫ i).hom.HomotopicRel (ContinuousMap.id B) (Set.range i.hom)) (Φ : B ⟶ T)
    (ρ : B ⟶ A) (hρ : i ≫ ρ = 𝟙 A) :
    Φ.hom.HomotopicRel (ρ ≫ i ≫ Φ).hom (Set.range i.hom) := by
  have h₁ : Φ.hom.HomotopicRel (s ≫ i ≫ Φ).hom (Set.range i.hom) := by
    have := H.symm.comp_continuousMap Φ.hom
    simpa using this
  have h₂ : ρ.hom.HomotopicRel s.hom (Set.range i.hom) := by
    have := H.symm.comp_continuousMap ρ.hom
    have e' : ρ.hom.comp (s ≫ i).hom = s.hom := by
      rw [← TopCat.hom_comp, Category.assoc, hρ, Category.comp_id]
    rwa [ContinuousMap.comp_id, e'] at this
  have h₃ := h₂.comp_continuousMap (i ≫ Φ).hom
  have h₃' : (ρ ≫ i ≫ Φ).hom.HomotopicRel (s ≫ i ≫ Φ).hom (Set.range i.hom) := by
    simpa using h₃
  exact h₁.trans h₃'.symm

/-- Two retractions of the realization of an anodyne map are homotopic relative to its image. -/
theorem retraction_homotopicRel_of_anodyne {A B : SemiSSet.{u}} (b : A ⟶ B) (hb : anodyne b)
    (ρ₁ ρ₂ : realization.obj B ⟶ realization.obj A) (h₁ : realization.map b ≫ ρ₁ = 𝟙 _)
    (h₂ : realization.map b ≫ ρ₂ = 𝟙 _) :
    ρ₁.hom.HomotopicRel ρ₂.hom (Set.range (realization.map b).hom) := by
  obtain ⟨s, -, H⟩ := Packages.realization_anodyne_deformationRetract b hb
  have := homotopicRel_retraction (realization.map b) s H ρ₁ ρ₂ h₂
  rwa [h₁, Category.comp_id] at this

/-- Every map out of the realization of the target of an anodyne map `c` is homotopic, relative to
the image of `‖c‖`, to its composite with any retraction of `‖c‖`. -/
theorem homotopicRel_of_anodyne {A B : SemiSSet.{u}} (c : A ⟶ B) (hc : anodyne c)
    {T : TopCat.{u}} (Φ : realization.obj B ⟶ T) (ρ : realization.obj B ⟶ realization.obj A)
    (hρ : realization.map c ≫ ρ = 𝟙 _) :
    Φ.hom.HomotopicRel (ρ ≫ realization.map c ≫ Φ).hom (Set.range (realization.map c).hom) := by
  obtain ⟨s, -, H⟩ := Packages.realization_anodyne_deformationRetract c hc
  exact homotopicRel_retraction (realization.map c) s H Φ ρ hρ

/-- Shrinking the fixed set of a relative homotopy. -/
theorem homotopicRel_mono {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f₀ f₁ : C(X, Y)} {S S' : Set X} (h : f₀.HomotopicRel f₁ S) (hS : S' ⊆ S) :
    f₀.HomotopicRel f₁ S' :=
  h.map fun F => ⟨F.toHomotopy, fun t x hx => F.prop' t x (hS hx)⟩

theorem simplexChar_comp {Y Z : SemiSSet.{u}} {n : ℕ}
    (y : stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ Y) (f : Y ⟶ Z) :
    simplexChar (y ≫ f) = simplexChar y ≫ realization.map f := by
  unfold simplexChar
  rw [CategoryTheory.Functor.map_comp]
  exact (Category.assoc _ _ _).symm

theorem vertexMap_id {n : ℕ} : vertexMap.{u} (id : Fin (n + 1) → Fin (n + 1)) = 𝟙 _ := by
  ext x
  obtain ⟨x⟩ := x
  change ULift.up (Convexity.StdSimplex.map (R := ℝ) id x) = ULift.up x
  rw [Convexity.StdSimplex.map_id]
