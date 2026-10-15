import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Interfaces.Disk0
import HomotopyHypothesis.Realization.Functor.Disk0

/-!
# `contractible_disk0`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- `|D₀|_R` is a point (`L` sends the representable `D₀` to `R(D₀) ≅ 𝔻 0`). -/
theorem contractible_disk0 {C : GlobularTheory.{u}} (hC : C.IsCoherator) (R : OAIRealization C)
    (L : C.Model ⥤ TopCat.{u}) (adj : L ⊣ R.Pi) :
    ContractibleSpace ((Afin.ι hC ⋙ L).obj (disk0 hC)) := by apply @_root_.HomotopyHypothesis.Realization.Functor.contractible_disk0_proof <;> assumption
