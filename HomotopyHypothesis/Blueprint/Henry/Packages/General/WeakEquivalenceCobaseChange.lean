import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Cylinder.PreCylinderCategory.CobaseChange

/-!
# `weakEquivalence_cobaseChange`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.General`, in its own module so that it can import the module that proves it.
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

section Cylinder

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

/-- H Cor 2.2.2(3) (H:497–516), repaired: the pushout of a weak equivalence `f` along a cofibration
`i` is a weak equivalence. Henry's proof uses that a pushout of a retract of a trivial cofibration is
a retract of one, which fails since the section of Brown's factorization is not under `A`; the
repair writes the pushout through `P = IA ⊔_{A} A'` and applies Ken Brown's lemma in `C(A)`
(H Cor 2.2.3, H:518). -/
theorem weakEquivalence_cobaseChange [IsCylinderCategory C] {A B X P : C} (i : A ⟶ B)
    (f : A ⟶ X) (k : B ⟶ P) (j : X ⟶ P) (h : IsPushout i f k j) (hi : cofibrations C i)
    (hf : weakEquivalences C f) : weakEquivalences C k := by apply (config := {allowSynthFailures := true}) @_root_.HomotopyHypothesis.Cylinder.PreCylinderCategory.weakEquivalence_cobaseChange_proof <;> assumption
