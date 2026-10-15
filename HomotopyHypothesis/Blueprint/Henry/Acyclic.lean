import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
/-!
# Acyclic morphisms of cylinder categories

Homotopy surjective, homotopy fully faithful and acyclic morphisms (H:786, Def 2.3.1). By
H Prop 2.3.4 a morphism is acyclic exactly when it induces an equivalence of homotopy categories.
-/

universe v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
  {D : Type u'} [Category.{v'} D] [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]

/-- `F` is homotopy surjective (H:788) if every object of `D` admits a weak equivalence to an object
in the image of `F`. -/
def IsHomotopySurjective (F : C ⥤ D) : Prop :=
  ∀ Y : D, ∃ (X : C) (w : Y ⟶ F.obj X), weakEquivalences D w

/-- `F` is homotopy fully faithful (H:790): for every cofibration `i : A ↪ B` and `x : A ⟶ X` in
`C`, every extension `v : F B ⟶ F X` of `F x` along `F i` is homotopic relative to `F A` to the
image of an extension of `x` along `i`. -/
def IsHomotopyFullyFaithful (F : C ⥤ D) : Prop :=
  ∀ ⦃A B X : C⦄ (i : A ⟶ B), cofibrations C i → ∀ (x : A ⟶ X) (v : F.obj B ⟶ F.obj X),
    F.map i ≫ v = F.map x →
    ∃ v' : B ⟶ X, i ≫ v' = x ∧ RelHomotopic (F.map i) (F.map v') v

/-- An acyclic morphism (H:811): homotopy surjective and homotopy fully faithful. -/
def IsAcyclic (F : C ⥤ D) : Prop :=
  IsHomotopySurjective F ∧ IsHomotopyFullyFaithful F

end HomotopyHypothesis.Henry
