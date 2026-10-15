import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.CylinderCategoryTheory.Proofs

/-!
# `isAcyclic_id`

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

/-- The identity of a cylinder category is acyclic (H Def 2.3.1, H:786; needs relative cylinders,
H Cor 2.2.3). -/
theorem isAcyclic_id [IsCylinderCategory C] : IsAcyclic (𝟭 C) := _root_.HomotopyHypothesis.CylinderCategoryTheory.isAcyclic_id_proof ..
