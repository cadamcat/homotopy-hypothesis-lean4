import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Cylinder.PathObjects.Pathobj

/-!
# `pathObj_isLiftingTarget`

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

/-- H:1532 (products) and H 4.2.8 (H:2498–2532): the path category `C^eq` is a cylinder
category, its projection `C^eq ⥤ C × C` is a pre-fibration between cylinder categories, and its two
legs `C^eq ⥤ C` are acyclic. The pre-fibration property is the Reedy argument of H Props 4.2.3,
4.2.5, 4.2.7 (H:2391–2494) for the directed category `l → c ← r`; acyclicity of the legs: the
inclusion of a minimal object `F_* ⟶ R_eq` is a trivial cofibration (H:2521). -/
theorem pathObj_isLiftingTarget [IsCylinderCategory C] :
    IsLiftingTarget false (PathObj C) (C × C) (PathObj.proj C) ∧
      IsAcyclic (PathObj.left C) ∧ IsAcyclic (PathObj.right C) := _root_.HomotopyHypothesis.Cylinder.PathObjects.pathObj_isLiftingTarget_proof ..
