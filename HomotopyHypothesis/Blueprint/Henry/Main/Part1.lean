import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.General.IsAcyclicTwoOutOfSix
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology

/-!
# `HomotopyHypothesis.Blueprint.Henry.Main`, part 1

Lines 40–77 of `HomotopyHypothesis.Blueprint.Henry.Main`, split so that the modules of the development form an acyclic import graph.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry

section Lemmas

variable {C : Type*} [Category C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
  {D : Type*} [Category D] [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]
  {E : Type*} [Category E] [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]

theorem IsCylinderMorphism.id : IsCylinderMorphism (𝟭 C) where
  map_cofibration _ _ _ hf := hf
  map_initial _ hI := ⟨hI⟩
  map_isPushout _ _ _ _ _ _ _ _ h _ := h
  map_weakEquivalence _ _ _ hf := hf

theorem IsCylinderMorphism.comp {F : C ⥤ D} {G : D ⥤ E} (hF : IsCylinderMorphism F)
    (hG : IsCylinderMorphism G) : IsCylinderMorphism (F ⋙ G) where
  map_cofibration _ _ f hf := hG.map_cofibration _ (hF.map_cofibration f hf)
  map_initial _ hI := by
    obtain ⟨h⟩ := hF.map_initial hI
    exact hG.map_initial h
  map_isPushout _ _ _ _ i f k j h hi :=
    hG.map_isPushout _ _ _ _ (hF.map_isPushout i f k j h hi) (hF.map_cofibration i hi)
  map_weakEquivalence _ _ f hf := hG.map_weakEquivalence _ (hF.map_weakEquivalence f hf)

theorem IsCellularRealization.comp {F : C ⥤ D} {G : D ⥤ TopCat.{u}} (hF : IsCylinderMorphism F)
    (hG : IsCellularRealization G) : IsCellularRealization (F ⋙ G) where
  obj_mem _ := hG.obj_mem _
  map_cofibration _ _ f hf := hG.map_cofibration _ (hF.map_cofibration f hf)
  map_weakEquivalence _ _ f hf := hG.map_weakEquivalence _ (hF.map_weakEquivalence f hf)
  map_initial _ hI := by
    obtain ⟨h⟩ := hF.map_initial hI
    exact hG.map_initial h
  map_isPushout _ _ _ _ i f k j h hi :=
    hG.map_isPushout _ _ _ _ (hF.map_isPushout i f k j h hi) (hF.map_cofibration i hi)

theorem weakEquivalence_of_isIso [IsCylinderCategory C] {X Y : C} (f : X ⟶ Y) [IsIso f] :
    weakEquivalences C f :=
  IsCylinderCategory.isomorphisms_le_weakEquivalences _ (inferInstanceAs (IsIso f))

theorem isAcyclic_comp [IsCylinderCategory C] [IsCylinderCategory D] [IsCylinderCategory E]
    {F : C ⥤ D} {G : D ⥤ E} (hF : IsCylinderMorphism F) (hG : IsCylinderMorphism G)
    (hF' : IsAcyclic F) (hG' : IsAcyclic G) : IsAcyclic (F ⋙ G) := by
  have := (Packages.isAcyclic_twoOutOfSix F (𝟭 D) G hF IsCylinderMorphism.id hG
    (by rwa [Functor.comp_id]) (by rwa [Functor.id_comp])).2.2.2
  rwa [Functor.id_comp] at this
