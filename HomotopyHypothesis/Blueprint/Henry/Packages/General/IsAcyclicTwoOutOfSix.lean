import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Homotopy.TwoOutOfSix.TwoOutOfSix

/-!
# `isAcyclic_twoOutOfSix`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.General`, in its own module so that it can import the module that proves it.
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

section Cylinder

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

end Cylinder

section Acyclic

variable {C : Type u₁} [Category.{v₁} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]
  {D : Type u₂} [Category.{v₂} D] [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]
  {E : Type u₃} [Category.{v₃} E] [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
  {F : Type u₄} [Category.{v₄} F] [CategoryWithCofibrations F] [CategoryWithWeakEquivalences F]

/-- H Prop 2.3.6 (H:970): acyclic morphisms of cylinder categories satisfy 2-out-of-6. Proof via
H Prop 2.3.4 (H:879): a morphism is acyclic iff it induces an equivalence of homotopy categories
(H Lemma 2.3.2, Cor 2.3.3, and Props 2.2.10–2.2.11). -/
theorem isAcyclic_twoOutOfSix [IsCylinderCategory C] [IsCylinderCategory D] [IsCylinderCategory E]
    [IsCylinderCategory F] (f : C ⥤ D) (g : D ⥤ E) (h : E ⥤ F) (hf : IsCylinderMorphism f)
    (hg : IsCylinderMorphism g) (hh : IsCylinderMorphism h) (hfg : IsAcyclic (f ⋙ g))
    (hgh : IsAcyclic (g ⋙ h)) :
    IsAcyclic f ∧ IsAcyclic g ∧ IsAcyclic h ∧ IsAcyclic (f ⋙ g ⋙ h) := by apply (config := {allowSynthFailures := true}) @_root_.HomotopyHypothesis.Homotopy.TwoOutOfSix.isAcyclic_twoOutOfSix_proof <;> assumption
