import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.CylinderCategoryTheory.Proofs
import HomotopyHypothesis.Cylinder.PreCylinderCategory.PreCylinder
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace HomotopyHypothesis.Cylinder.PreCylinderCategory

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

variable {C : Type u₁} [Category.{v₁} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
  {D : Type u₂} [Category.{v₂} D] [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]
  {E : Type u₃} [Category.{v₃} E] [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
  {F : Type u₄} [Category.{v₄} F] [CategoryWithCofibrations F] [CategoryWithWeakEquivalences F]

/-- If a composite functor `F ⋙ G` is homotopy surjective, then `G` is homotopy surjective. -/
lemma isHomotopySurjective_of_comp_right
    (F : C ⥤ D) (G : D ⥤ E) (hFG : IsHomotopySurjective (F ⋙ G)) :
    IsHomotopySurjective G := by
  intro Y
  obtain ⟨X, w, hw⟩ := hFG Y
  exact ⟨F.obj X, w, hw⟩

/-- If `F` and `G` are homotopy surjective and `G` preserves weak equivalences,
their composite `F ⋙ G` is homotopy surjective. -/
lemma isHomotopySurjective_comp [IsCylinderCategory E]
    (F : C ⥤ D) (G : D ⥤ E)
    (hG_we : ∀ ⦃X Y : D⦄ (w : X ⟶ Y), weakEquivalences D w → weakEquivalences E (G.map w))
    (hF : IsHomotopySurjective F) (hG : IsHomotopySurjective G) :
    IsHomotopySurjective (F ⋙ G) := by
  intro Z
  obtain ⟨Y, w₁, hw₁⟩ := hG Z
  obtain ⟨X, w₂, hw₂⟩ := hF Y
  refine ⟨X, w₁ ≫ G.map w₂, ?_⟩
  exact (IsCylinderCategory.weakEquivalences_isMultiplicative (C := E)).comp_mem
    _ _ hw₁ (hG_we w₂ hw₂)

/-- Functorial pushforward of a relative cylinder along a cylinder morphism. -/
def RelativeCylinder.map (G : C ⥤ D) (hG : IsCylinderMorphism G)
    {A B : C} {i : A ⟶ B} (hi : cofibrations C i)
    (cyl : RelativeCylinder i) : RelativeCylinder (G.map i) where
  P := G.obj cyl.P
  j₀ := G.map cyl.j₀
  j₁ := G.map cyl.j₁
  isPushout := hG.map_isPushout i i cyl.j₀ cyl.j₁ cyl.isPushout hi
  I := G.obj cyl.I
  c := G.map cyl.c
  p := G.map cyl.p
  c_mem := hG.map_cofibration cyl.c cyl.c_mem
  p_mem := hG.map_weakEquivalence cyl.p cyl.p_mem
  j₀_c_p := by
    rw [← G.map_comp, ← G.map_comp, cyl.j₀_c_p, G.map_id]
  j₁_c_p := by
    rw [← G.map_comp, ← G.map_comp, cyl.j₁_c_p, G.map_id]

/-- A cylinder morphism preserves relative homotopies. -/
lemma relHomotopic_map (G : C ⥤ D) (hG : IsCylinderMorphism G)
    {A B X : C} {i : A ⟶ B} (hi : cofibrations C i)
    {u v : B ⟶ X} (h : RelHomotopic i u v) :
    RelHomotopic (G.map i) (G.map u) (G.map v) := by
  obtain ⟨cyl, H, h₀, h₁⟩ := h
  let cyl' := RelativeCylinder.map G hG hi cyl
  change RelHomotopic (G.map i) (G.map u) (G.map v)
  refine ⟨cyl', G.map H, ?_, ?_⟩
  · change G.map cyl.j₀ ≫ G.map cyl.c ≫ G.map H = G.map u
    rw [← G.map_comp, ← G.map_comp, h₀]
  · change G.map cyl.j₁ ≫ G.map cyl.c ≫ G.map H = G.map v
    rw [← G.map_comp, ← G.map_comp, h₁]

/-- If `F` and `G` are homotopy fully faithful cylinder morphisms,
their composite `F ⋙ G` is homotopy fully faithful. -/
lemma isHomotopyFullyFaithful_comp [IsCylinderCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (hF : IsCylinderMorphism F) (hG : IsCylinderMorphism G)
    (hF_ff : IsHomotopyFullyFaithful F) (hG_ff : IsHomotopyFullyFaithful G) :
    IsHomotopyFullyFaithful (F ⋙ G) := by
  intro A B X i hi x v hsq
  have hFi_cof : cofibrations D (F.map i) := hF.map_cofibration i hi
  obtain ⟨w, hw_comm, hw_rel⟩ := hG_ff (F.map i) hFi_cof (F.map x) v (by simpa using hsq)
  obtain ⟨v', hv'_comm, hv'_rel⟩ := hF_ff i hi x w hw_comm
  have hGw_rel : RelHomotopic (G.map (F.map i)) (G.map (F.map v')) (G.map w) :=
    relHomotopic_map G hG hFi_cof hv'_rel
  have hGFi_cof : cofibrations E ((F ⋙ G).map i) :=
    hG.map_cofibration (F.map i) hFi_cof
  have heqv := (_root_.HomotopyHypothesis.CylinderCategoryTheory.relHomotopic_equivalence_proof
    (X := (F ⋙ G).obj X) ((F ⋙ G).map i) hGFi_cof).1
  refine ⟨v', hv'_comm, heqv.trans hGw_rel hw_rel⟩

/-- Composition of acyclic cylinder morphisms is acyclic. -/
theorem isAcyclic_comp [IsCylinderCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (hF : IsCylinderMorphism F) (hG : IsCylinderMorphism G)
    (hFac : IsAcyclic F) (hGac : IsAcyclic G) :
    IsAcyclic (F ⋙ G) :=
  ⟨isHomotopySurjective_comp F G (fun _ _ w hw => hG.map_weakEquivalence w hw) hFac.1 hGac.1,
   isHomotopyFullyFaithful_comp F G hF hG hFac.2 hGac.2⟩

/-- `f ⋙ g ⋙ h` is homotopy surjective from `hfg` and `hgh`. -/
lemma isHomotopySurjective_three [IsCylinderCategory F]
    (f : C ⥤ D) (g : D ⥤ E) (h : E ⥤ F) (hh : IsCylinderMorphism h)
    (hfg : IsHomotopySurjective (f ⋙ g)) (hgh : IsHomotopySurjective (g ⋙ h)) :
    IsHomotopySurjective (f ⋙ g ⋙ h) := by
  intro W
  obtain ⟨Y, w₁, hw₁⟩ := hgh W
  obtain ⟨X, w₂, hw₂⟩ := hfg (g.obj Y)
  refine ⟨X, w₁ ≫ h.map w₂, ?_⟩
  exact (IsCylinderCategory.weakEquivalences_isMultiplicative (C := F)).comp_mem
    _ _ hw₁ (hh.map_weakEquivalence w₂ hw₂)

#print axioms isHomotopySurjective_of_comp_right
#print axioms isHomotopySurjective_comp
#print axioms RelativeCylinder.map
#print axioms relHomotopic_map
#print axioms isHomotopyFullyFaithful_comp
#print axioms isAcyclic_comp
#print axioms isHomotopySurjective_three

end HomotopyHypothesis.Cylinder.PreCylinderCategory
