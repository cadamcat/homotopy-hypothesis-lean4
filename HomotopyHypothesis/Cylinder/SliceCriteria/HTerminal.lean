import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.CylinderCategoryTheory.Proofs
import HomotopyHypothesis.Cylinder.SliceCriteria.HomotopyFacts
open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe v u v' u'

namespace HomotopyHypothesis.Cylinder.SliceCriteria

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [IsCylinderCategory C]

theorem isHTerminal_nonempty_hom {X : C} (hX : IsHTerminal X) (A : C) :
    Nonempty (A ⟶ X) := by
  obtain ⟨O, hOne⟩ := IsCofibrationCategory.exists_initial (C := C)
  obtain ⟨hO⟩ := hOne
  obtain ⟨a, _⟩ := hX (hO.to A) (IsCofibrationCategory.initial_cofibration hO A) (hO.to X)
  exact ⟨a⟩

/-- Any two maps into an h-terminal object are homotopic. -/
theorem isHTerminal_homotopic {X : C} (hX : IsHTerminal X) {A : C} (f g : A ⟶ X) :
    Homotopic f g := by
  obtain ⟨O, hOne⟩ := IsCofibrationCategory.exists_initial (C := C)
  obtain ⟨hO⟩ := hOne
  obtain ⟨cyl⟩ := IsCylinderCategory.exists_cylinder hO A
  let d : cyl.P ⟶ X := cyl.isPushout.desc f g (hO.hom_ext _ _)
  obtain ⟨H, hH⟩ := hX cyl.c cyl.c_mem d
  refine ⟨O, hO, cyl, H, ?_, ?_⟩
  · rw [hH]
    exact cyl.isPushout.inl_desc _ _ _
  · rw [hH]
    exact cyl.isPushout.inr_desc _ _ _

/-- Existence and uniqueness up to homotopy of maps into an object imply h-terminality. -/
theorem isHTerminal_of_homotopy_unique (X : C) (hex : ∀ A : C, Nonempty (A ⟶ X))
    (huniq : ∀ (A : C) (f g : A ⟶ X), Homotopic f g) : IsHTerminal X := by
  intro A B i hi a
  obtain ⟨b⟩ := hex B
  exact cofibration_extension_of_homotopic i hi a b (huniq A (i ≫ b) a)

variable {D : Type u'} [Category.{v'} D] [CategoryWithCofibrations D]
  [CategoryWithWeakEquivalences D] [IsCylinderCategory D]

/-- An acyclic exact functor preserves h-terminal objects. -/
theorem isHTerminal_map_of_isAcyclic {F : C ⥤ D} (hF : IsCylinderMorphism F)
    (hac : IsAcyclic F) {U : C} (hU : IsHTerminal U) : IsHTerminal (F.obj U) := by
  obtain ⟨J, hJne⟩ := IsCofibrationCategory.exists_initial (C := C)
  obtain ⟨hJ⟩ := hJne
  obtain ⟨hFJ⟩ := hF.map_initial hJ
  have hrepr : ∀ (V : C) (f : F.obj V ⟶ F.obj U),
      ∃ f' : V ⟶ U, Homotopic (F.map f') f := by
    intro V f
    obtain ⟨f', _, hrel⟩ := hac.2 (hJ.to V)
      (IsCofibrationCategory.initial_cofibration hJ V) (hJ.to U) f (hFJ.hom_ext _ _)
    have heq : F.map (hJ.to V) = hFJ.to (F.obj V) := hFJ.hom_ext _ _
    exact ⟨f', F.obj J, hFJ, heq ▸ hrel⟩
  refine isHTerminal_of_homotopy_unique (F.obj U) ?_ ?_
  · intro A
    obtain ⟨V, w, _⟩ := hac.1 A
    obtain ⟨f⟩ := isHTerminal_nonempty_hom hU V
    exact ⟨w ≫ F.map f⟩
  · intro A f g
    obtain ⟨V, w, hw⟩ := hac.1 A
    obtain ⟨v, hwv, _⟩ := (_root_.HomotopyHypothesis.CylinderCategoryTheory.weakEquivalence_iff_proof w).mp hw
    obtain ⟨f', hff'⟩ := hrepr V (v ≫ f)
    obtain ⟨g', hgg'⟩ := hrepr V (v ≫ g)
    have hmid : Homotopic (v ≫ f) (v ≫ g) :=
      homotopic_trans (homotopic_symm hff')
        (homotopic_trans (homotopic_map hF (isHTerminal_homotopic hU f' g')) hgg')
    have hpre : Homotopic ((w ≫ v) ≫ f) ((w ≫ v) ≫ g) := by
      simpa only [Category.assoc] using homotopic_precomp hmid w
    have hleft : Homotopic ((w ≫ v) ≫ f) f := by
      simpa only [Category.id_comp] using homotopic_postcomp hwv f
    have hright : Homotopic ((w ≫ v) ≫ g) g := by
      simpa only [Category.id_comp] using homotopic_postcomp hwv g
    exact homotopic_trans (homotopic_symm hleft) (homotopic_trans hpre hright)

#print axioms isHTerminal_map_of_isAcyclic

end HomotopyHypothesis.Cylinder.SliceCriteria
