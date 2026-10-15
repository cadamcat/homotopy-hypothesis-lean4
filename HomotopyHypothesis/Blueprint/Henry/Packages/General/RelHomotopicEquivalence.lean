import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.CylinderCategoryTheory.Proofs

/-!
# `relHomotopic_equivalence`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.General`, in its own module so that it can import the module that proves it.
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

section Cylinder

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

/-- H Prop 2.2.8 (H:587), items (1)–(2): relative homotopy along a cofibration is an equivalence
relation, and it can be witnessed on any given relative cylinder. Uses H Cor 2.2.3 (coslices
`C(A)` are cylinder categories, H:518) and H Lemma 2.2.6 (H:540). -/
theorem relHomotopic_equivalence [IsCylinderCategory C] {A B X : C} (i : A ⟶ B)
    (hi : cofibrations C i) :
    Equivalence (RelHomotopic (X := X) i) ∧
      ∀ (cyl : RelativeCylinder i) (f g : B ⟶ X), RelHomotopic i f g →
        ∃ H : cyl.I ⟶ X, cyl.j₀ ≫ cyl.c ≫ H = f ∧ cyl.j₁ ≫ cyl.c ≫ H = g := by apply @_root_.HomotopyHypothesis.CylinderCategoryTheory.relHomotopic_equivalence_proof <;> assumption
