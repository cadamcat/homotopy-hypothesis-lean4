import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Realization.Functor.PiAdjoint

/-!
# `pi_isRightAdjoint`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **Geometric realization.** `Π_R` has a left adjoint `|−|_R` (the left Kan extension of the
realization along the Yoneda embedding `C ⥤ C.Model`, which exists since `TopCat` is cocomplete
and `C` is small). -/
theorem pi_isRightAdjoint {C : GlobularTheory.{u}} (R : OAIRealization C) :
    R.Pi.IsRightAdjoint := _root_.HomotopyHypothesis.Realization.Functor.pi_isRightAdjoint_proof ..
