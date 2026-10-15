import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.FiniteCategory.Subcategory.AfinMapInitial

/-!
# `afin_ι_map_initial`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- The inclusion `A_fin ⥤ C.Model` sends initial objects to initial models (the initial model is
finitely cellular). -/
theorem afin_ι_map_initial {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    ∀ ⦃I : Afin C hC⦄, IsInitial I → Nonempty (IsInitial ((Afin.ι hC).obj I)) := _root_.HomotopyHypothesis.FiniteCategory.Subcategory.afin_ι_map_initial_proof ..
