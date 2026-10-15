import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Cylinder.PreCylinderCategory.PreCylinder

/-!
# `isPreCylinderCategory`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.General`, in its own module so that it can import the module that proves it.
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

section Cylinder

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

/-- H Prop 2.2.12 (H:722), the gluing (cube) lemma: a cylinder category is a pre-cylinder
category. Inputs: Brown factorization (H Prop 2.2.1, H:485), H Cor 2.2.2 (H:497) with the repair of
item (3) (pushout of a weak equivalence along a cofibration, via `w♯` and Ken Brown's argument in
the coslice `C(A)`). -/
theorem isPreCylinderCategory [IsCylinderCategory C] : IsPreCylinderCategory C := _root_.HomotopyHypothesis.Cylinder.PreCylinderCategory.isPreCylinderCategory_proof ..
