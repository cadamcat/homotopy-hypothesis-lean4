import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Cylinder.PathObjects.Pathobj

/-!
# `isAcyclic_iff_of_isCylinderCoherator`

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

/-- H Prop 4.3.2 (H:2549) and the uniqueness claim of H Thm 5.1.2(5) (H:2789), as repaired: two
morphisms `G G'` from a cylinder coherator to a cylinder category whose values at the marked object
are joined by weak equivalences are simultaneously acyclic. Proof: factor `G o ⊔ G' o ⟶ X` to get an
object of `D^eq` over `(G o, G' o)`, lift `(G, G') : C ⥤ D × D` along the pre-fibration
`D^eq ⥤ D × D`, and conclude by 2-out-of-3 for acyclic morphisms (H:2560–2565). -/
theorem isAcyclic_iff_of_isCylinderCoherator {o : C} (hC : IsCylinderCoherator.{u + 1, u} C o)
    {D : Type (u + 1)} [Category.{u} D] [CategoryWithCofibrations D]
    [CategoryWithWeakEquivalences D] [IsCylinderCategory D] {G G' : C ⥤ D}
    (hG : IsCylinderMorphism G) (hG' : IsCylinderMorphism G') {X : D} (w : G.obj o ⟶ X)
    (w' : G'.obj o ⟶ X) (hw : weakEquivalences D w) (hw' : weakEquivalences D w') :
    IsAcyclic G ↔ IsAcyclic G' := by apply (config := {allowSynthFailures := true}) @_root_.HomotopyHypothesis.Cylinder.PathObjects.isAcyclic_iff_of_isCylinderCoherator_proof <;> assumption
