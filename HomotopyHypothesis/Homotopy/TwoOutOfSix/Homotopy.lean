import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.CylinderCategoryTheory.Proofs
import HomotopyHypothesis.Cylinder.PreCylinderCategory.Acyclic
import HomotopyHypothesis.Category.SemiModelStructure.CylinderFacts
/-!
# The homotopy relation in a cylinder category

The homotopy relation `Homotopic` of a cylinder category is an equivalence relation compatible
with composition, it is preserved by morphisms of cylinder categories, and weak equivalences are
exactly the maps with a homotopy inverse. These are the facts about the homotopy category
`hC = C / ≃` (H:560–720) used below, phrased without forming the quotient category.
-/

universe v₁ u₁ v₂ u₂

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Homotopy.TwoOutOfSix

section Homotopy

variable {C : Type u₁} [Category.{v₁} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]

theorem initial_cofibration [IsCylinderCategory C] {O : C} (hO : IsInitial O) (X : C) :
    cofibrations C (hO.to X) :=
  IsCofibrationCategory.initial_cofibration hO X

theorem we_id [IsCylinderCategory C] (X : C) : weakEquivalences C (𝟙 X) :=
  IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 X)
    (MorphismProperty.isomorphisms.infer_property (𝟙 X))

theorem we_comp [IsCylinderCategory C] {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : weakEquivalences C f) (hg : weakEquivalences C g) : weakEquivalences C (f ≫ g) :=
  (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).comp_mem f g hf hg

/-- If `f ≫ g` and `g` are weak equivalences, so is `f`. -/
theorem we_of_comp_right [IsCylinderCategory C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : weakEquivalences C g) (hfg : weakEquivalences C (f ≫ g)) : weakEquivalences C f :=
  (IsCylinderCategory.twoOutOfSix (C := C) f g (𝟙 Z) hfg (by simpa using hg)).1

/-- If `f` and `f ≫ g` are weak equivalences, so is `g`. -/
theorem we_of_comp_left [IsCylinderCategory C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : weakEquivalences C f) (hfg : weakEquivalences C (f ≫ g)) : weakEquivalences C g :=
  (IsCylinderCategory.twoOutOfSix (C := C) (𝟙 X) f g (by simpa using hf) hfg).2.2.1

/-- A homotopy may be witnessed relative to any initial object. -/
theorem homotopic_normalize [IsCylinderCategory C] {X Y : C} {f g : X ⟶ Y}
    (h : Homotopic f g) {O : C} (hO : IsInitial O) : RelHomotopic (hO.to X) f g := by
  obtain ⟨O', hO', hrel⟩ := h
  have hsq : hO.to X ≫ 𝟙 X = hO.to O' ≫ hO'.to X := hO.hom_ext _ _
  simpa using Category.SemiModelStructure.relHomotopic_precomp (hO'.to X) (hO.to X) (hO.to O') (𝟙 X) hsq
    (initial_cofibration hO X) hrel

theorem homotopic_refl [IsCylinderCategory C] {X Y : C} (f : X ⟶ Y) : Homotopic f f := by
  obtain ⟨O, ⟨hO⟩⟩ := IsCofibrationCategory.exists_initial (C := C)
  exact ⟨O, hO,
    (_root_.HomotopyHypothesis.CylinderCategoryTheory.relHomotopic_equivalence_proof _ (initial_cofibration hO X)).1.refl f⟩

theorem homotopic_symm [IsCylinderCategory C] {X Y : C} {f g : X ⟶ Y} (h : Homotopic f g) :
    Homotopic g f := by
  obtain ⟨O, hO, hrel⟩ := h
  exact ⟨O, hO,
    (_root_.HomotopyHypothesis.CylinderCategoryTheory.relHomotopic_equivalence_proof _ (initial_cofibration hO X)).1.symm hrel⟩

theorem homotopic_trans [IsCylinderCategory C] {X Y : C} {f g k : X ⟶ Y} (h₁ : Homotopic f g)
    (h₂ : Homotopic g k) : Homotopic f k := by
  obtain ⟨O, hO, hrel⟩ := h₁
  exact ⟨O, hO, (_root_.HomotopyHypothesis.CylinderCategoryTheory.relHomotopic_equivalence_proof _
    (initial_cofibration hO X)).1.trans hrel (homotopic_normalize h₂ hO)⟩

theorem homotopic_postcomp {X Y Z : C} {f g : X ⟶ Y} (h : Homotopic f g) (u : Y ⟶ Z) :
    Homotopic (f ≫ u) (g ≫ u) := by
  obtain ⟨O, hO, cyl, H, h₀, h₁⟩ := h
  refine ⟨O, hO, cyl, H ≫ u, ?_, ?_⟩
  · simpa [Category.assoc] using congrArg (fun k => k ≫ u) h₀
  · simpa [Category.assoc] using congrArg (fun k => k ≫ u) h₁

theorem homotopic_precomp [IsCylinderCategory C] {X Y Z : C} {f g : Y ⟶ Z}
    (h : Homotopic f g) (v : X ⟶ Y) : Homotopic (v ≫ f) (v ≫ g) := by
  obtain ⟨O, hO, hrel⟩ := h
  have hsq : hO.to X ≫ v = 𝟙 O ≫ hO.to Y := hO.hom_ext _ _
  exact ⟨O, hO, Category.SemiModelStructure.relHomotopic_precomp (hO.to Y) (hO.to X) (𝟙 O) v hsq
    (initial_cofibration hO X) hrel⟩

theorem homotopic_comp [IsCylinderCategory C] {X Y Z : C} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    (hf : Homotopic f f') (hg : Homotopic g g') : Homotopic (f ≫ g) (f' ≫ g') :=
  homotopic_trans (homotopic_postcomp hf g) (homotopic_precomp hg f')

/-- A weak equivalence has a homotopy inverse, which is again a weak equivalence. -/
theorem exists_homotopyInverse [IsCylinderCategory C] {X Y : C} (w : X ⟶ Y)
    (hw : weakEquivalences C w) :
    ∃ e : Y ⟶ X, weakEquivalences C e ∧ Homotopic (w ≫ e) (𝟙 X) ∧ Homotopic (e ≫ w) (𝟙 Y) := by
  obtain ⟨e, h₁, h₂⟩ := (_root_.HomotopyHypothesis.CylinderCategoryTheory.weakEquivalence_iff_proof w).mp hw
  exact ⟨e, (_root_.HomotopyHypothesis.CylinderCategoryTheory.weakEquivalence_iff_proof e).mpr ⟨w, h₂, h₁⟩, h₁, h₂⟩

/-- A map homotopic to a weak equivalence is a weak equivalence. -/
theorem we_of_homotopic [IsCylinderCategory C] {X Y : C} {f g : X ⟶ Y} (h : Homotopic f g)
    (hg : weakEquivalences C g) : weakEquivalences C f := by
  obtain ⟨e, -, h₁, h₂⟩ := exists_homotopyInverse g hg
  exact (_root_.HomotopyHypothesis.CylinderCategoryTheory.weakEquivalence_iff_proof f).mpr
    ⟨e, homotopic_trans (homotopic_postcomp h e) h₁,
      homotopic_trans (homotopic_precomp h e) h₂⟩

end Homotopy

section Morphism

variable {C : Type u₁} [Category.{v₁} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]
  {D : Type u₂} [Category.{v₂} D] [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]

omit [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [CategoryWithCofibrations D]
  [CategoryWithWeakEquivalences D] in
/-- The image of a map out of an initial object under a morphism of cylinder categories. -/
theorem map_initial_to (F : C ⥤ D) {O : C} (hO : IsInitial O) (hFO : IsInitial (F.obj O))
    (X : C) : F.map (hO.to X) = hFO.to (F.obj X) :=
  hFO.hom_ext _ _

/-- Morphisms of cylinder categories preserve the homotopy relation. -/
theorem homotopic_map [IsCylinderCategory C] (F : C ⥤ D) (hF : IsCylinderMorphism F)
    {X Y : C} {f g : X ⟶ Y} (h : Homotopic f g) : Homotopic (F.map f) (F.map g) := by
  obtain ⟨O, hO, hrel⟩ := h
  obtain ⟨hFO⟩ := hF.map_initial hO
  have h' := Cylinder.PreCylinderCategory.relHomotopic_map F hF (initial_cofibration hO X) hrel
  rw [map_initial_to F hO hFO X] at h'
  exact ⟨F.obj O, hFO, h'⟩

end Morphism

end HomotopyHypothesis.Homotopy.TwoOutOfSix
