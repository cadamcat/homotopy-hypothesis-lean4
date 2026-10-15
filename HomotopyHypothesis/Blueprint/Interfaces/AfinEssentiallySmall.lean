import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.FiniteCategory.Subcategory.AfinEssentiallySmall

/-!
# `afin_essentiallySmall`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- `A_fin` is essentially small: a finitely cellular model is determined up to isomorphism by
finitely many attaching data, each an element of a boundary set of size `u`. -/
theorem afin_essentiallySmall {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    EssentiallySmall.{u} (Afin C hC) := _root_.HomotopyHypothesis.FiniteCategory.Subcategory.afin_essentiallySmall_proof ..
