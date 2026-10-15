import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Category.CylinderCorollary.TwoOutOfSix

/-!
# `weakEquivalence_twoOutOfSix`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **2-out-of-6** for weak equivalences of models (gap review B §1.1(b): `π₀` and change of base
point, OA:01:276, then 2-out-of-3). -/
theorem weakEquivalence_twoOutOfSix {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    TwoOutOfSix C.Model (W hC) := _root_.HomotopyHypothesis.Blueprint.Packages.weakEquivalence_twoOutOfSix_proof ..
