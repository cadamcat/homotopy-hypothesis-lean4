import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Anodyne.AnodyneExtension

/-!
# `isKan_extension_of_anodyne`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Approximation`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Henry.Packages

open SemiSSet

/-- **Extension along collapses** (Rourke–Sanderson, Prop. 5.2). A semi-simplicial set satisfying
the Kan condition extends maps along anodyne maps (pushouts of horn inclusions, inductively). -/
theorem isKan_extension_of_anodyne {X : SemiSSet.{u}} (hX : X.IsKan) {A B : SemiSSet.{u}}
    (j : A ⟶ B) (hj : anodyne j) (a : A ⟶ X) : ∃ b : B ⟶ X, j ≫ b = a := by apply @_root_.HomotopyHypothesis.Approximation.Anodyne.isKan_extension_of_anodyne_proof <;> assumption
