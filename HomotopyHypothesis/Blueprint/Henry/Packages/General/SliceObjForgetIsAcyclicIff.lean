import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Cylinder.SliceCriteria.Proofs.Part1

/-!
# `sliceObj_forget_isAcyclic_iff`

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

end Completion

section SemiModel

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

end SemiModel

section Fibrations

variable {C : Type (u + 1)} [Category.{u} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]

/-- H Prop 4.4.4 (H:2682), second item, with the repair of the omitted homotopy surjectivity
(factor `Y ⊔ X ⟶ X` as `Y ⊔ X ↪ Y_f ⥲ X`): the forgetful morphism `C^X ⥤ C` is acyclic iff `X`
is h-terminal. -/
theorem sliceObj_forget_isAcyclic_iff [IsCylinderCategory C] (X : C) :
    IsAcyclic (SliceObj.forget X) ↔ IsHTerminal X := _root_.HomotopyHypothesis.Henry.Packages.sliceObj_forget_isAcyclic_iff_proof ..
