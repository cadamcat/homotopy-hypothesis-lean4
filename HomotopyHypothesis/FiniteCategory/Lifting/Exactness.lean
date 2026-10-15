import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.FiniteCategory.Lifting.Strictification
/-!+# Exactness of strictified liftings

Natural isomorphisms preserve morphisms of cofibration and cylinder categories.
Consequently the strictification of a pointed lifting is again a cylinder morphism.
-/

universe v u v₁ u₁ v₂ u₂

open CategoryTheory Limits HomotopicalAlgebra
open HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

section Exactness

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]

/-- Transport membership in a multiplicative morphism property across a natural isomorphism. -/
theorem map_mem_of_natIso (P : MorphismProperty D) (hP : P.IsMultiplicative)
    (hIso : MorphismProperty.isomorphisms D ≤ P) {F G : C ⥤ D} (e : F ≅ G)
    {A B : C} (f : A ⟶ B) (hf : P (F.map f)) : P (G.map f) := by
  have hmap : G.map f = (e.app A).inv ≫ F.map f ≫ (e.app B).hom := by
    rw [← cancel_epi (e.app A).hom]
    simpa [Category.assoc] using (e.hom.naturality f).symm
  rw [hmap]
  exact hP.comp_mem _ _ (hIso _ inferInstance)
    (hP.comp_mem _ _ hf (hIso _ inferInstance))

variable [CategoryWithCofibrations C] [CategoryWithCofibrations D]

/-- A functor naturally isomorphic to a cofibration morphism is a cofibration morphism. -/
theorem isCofibrationMorphism_of_natIso [IsCofibrationCategory D]
    {F G : C ⥤ D} (e : F ≅ G) (hF : IsCofibrationMorphism F) :
    IsCofibrationMorphism G where
  map_cofibration {A B} f hf := map_mem_of_natIso _
    (IsCofibrationCategory.isMultiplicative (C := D))
    (IsCofibrationCategory.isomorphisms_le (C := D)) e f (hF.map_cofibration f hf)
  map_initial {I} hI := by
    obtain ⟨hFI⟩ := hF.map_initial hI
    exact ⟨hFI.ofIso (e.app _)⟩
  map_isPushout {A B X P} i f k j h hi :=
    (hF.map_isPushout i f k j h hi).of_iso (e.app _) (e.app _) (e.app _) (e.app _)
      (e.hom.naturality i) (e.hom.naturality f) (e.hom.naturality k) (e.hom.naturality j)

variable [CategoryWithWeakEquivalences C] [CategoryWithWeakEquivalences D]

/-- A functor naturally isomorphic to a cylinder morphism is a cylinder morphism. -/
theorem isCylinderMorphism_of_natIso [IsCylinderCategory D]
    {F G : C ⥤ D} (e : F ≅ G) (hF : IsCylinderMorphism F) : IsCylinderMorphism G where
  toIsCofibrationMorphism := isCofibrationMorphism_of_natIso e hF.toIsCofibrationMorphism
  map_weakEquivalence {A B} f hf := map_mem_of_natIso _
    (IsCylinderCategory.weakEquivalences_isMultiplicative (C := D))
    (IsCylinderCategory.isomorphisms_le_weakEquivalences (C := D)) e f
    (hF.map_weakEquivalence f hf)

end Exactness

section Strictification

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]
  {X : Type u₁} [Category.{v₁} X] [CategoryWithCofibrations X]
  [CategoryWithWeakEquivalences X] [IsCylinderCategory X]
  {Y : Type u₂} [Category.{v₂} Y]

/-- Strictify a pointed cylinder-morphism lifting up to natural isomorphism. -/
theorem strictify_pointed_cylinder {p : X ⥤ Y} (hp : IsIsofibration p)
    (L : C ⥤ X) (hL : IsCylinderMorphism L) (h : C ⥤ Y) (α : L ⋙ p ≅ h)
    (o : C) (x : X) (hx : h.obj o = p.obj x) (a : L.obj o ≅ x)
    (ha : p.map a.hom = (α.app o).hom ≫ eqToHom hx) :
    ∃ l : C ⥤ X, IsCylinderMorphism l ∧ l ⋙ p = h ∧ l.obj o = x := by
  obtain ⟨l, β, hlp, hlo⟩ := strictify_pointed hp L h α o x hx a ha
  exact ⟨l, isCylinderMorphism_of_natIso β hL, hlp, hlo⟩

end Strictification

#print axioms isCylinderMorphism_of_natIso
#print axioms strictify_pointed_cylinder

end HomotopyHypothesis.FiniteCategory.Lifting
