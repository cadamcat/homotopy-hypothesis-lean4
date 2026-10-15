import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Anodyne.RealizationPushout

/-!
# `realization_isPushout`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Approximation`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Henry.Packages

open SemiSSet

/-- The realization of semi-simplicial sets preserves pushouts (it is a left adjoint, the left
Kan extension along the Yoneda embedding). -/
theorem realization_isPushout {A B C D : SemiSSet.{u}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D}
    {k : C ⟶ D} (H : IsPushout f g h k) :
    IsPushout (realization.map f) (realization.map g) (realization.map h) (realization.map k) :=
  by apply @_root_.HomotopyHypothesis.Approximation.Anodyne.realization_isPushout_proof <;> assumption
