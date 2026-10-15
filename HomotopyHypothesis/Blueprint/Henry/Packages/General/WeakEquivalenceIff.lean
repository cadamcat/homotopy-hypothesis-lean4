import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.CylinderCategoryTheory.Proofs

/-!
# `weakEquivalence_iff`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.General`, in its own module so that it can import the module that proves it.
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

section Cylinder

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

/-- H Prop 2.2.10 (H:693) and Prop 2.2.11 (H:708): the weak equivalences of a cylinder category are
exactly the homotopy equivalences (this is where 2-out-of-6 is used). -/
theorem weakEquivalence_iff [IsCylinderCategory C] {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C f ↔ ∃ g : Y ⟶ X, Homotopic (f ≫ g) (𝟙 X) ∧ Homotopic (g ≫ f) (𝟙 Y) :=
  _root_.HomotopyHypothesis.CylinderCategoryTheory.weakEquivalence_iff_proof ..
