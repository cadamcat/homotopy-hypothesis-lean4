import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Blueprint.Interfaces.CellularRealization
import HomotopyHypothesis.Blueprint.Interfaces.Restriction
import HomotopyHypothesis.FiniteCategory.Subcategory.TopRestrictionIso

/-!
# `topRestriction_iso`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **Henry's `π_∞` of the restricted realization is `Π_R`** (gap review B §2(a)):
`Hom(L A, X) ≅ Hom(A, Π_R X)` naturally in `A ∈ A_fin` and `X`. -/
theorem topRestriction_iso {C : GlobularTheory.{u}} (hC : C.IsCoherator) (R : OAIRealization C)
    (L : C.Model ⥤ TopCat.{u}) (adj : L ⊣ R.Pi) :
    Nonempty (topRestriction (cellularRealization hC R L adj) ≅ R.Pi ⋙ restriction hC) := by apply @_root_.HomotopyHypothesis.FiniteCategory.Subcategory.topRestriction_iso_proof <;> assumption
