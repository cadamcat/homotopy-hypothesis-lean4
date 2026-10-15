import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Category.SemiModelStructure.Main

/-!
# `completion_isSemiModelCategory`

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

end Acyclic

section Completion

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

/-- H Thm 2.4.14 (H:1351), assembling H 2.4.2–2.4.13 (H:997–1347): the completion of an
essentially small cylinder category is a semi-model category in which every object is fibrant
(small object argument for the factorizations; weak equivalences via the `π`-sets of H:1144). -/
theorem completion_isSemiModelCategory [IsCylinderCategory C] [EssentiallySmall.{w} C] :
    IsSemiModelCategory (Completion.{w} C) (Completion.cofibrations C) (Completion.fibrations C)
      (Completion.weakEquivalences C) ∧
    ∀ X : Completion.{w} C, IsFibrantFor (Completion.fibrations C) X := _root_.HomotopyHypothesis.Henry.Packages.completion_isSemiModelCategory_proof ..
