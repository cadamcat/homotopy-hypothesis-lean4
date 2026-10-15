import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Realization.Cellular.Main

/-!
# `cellularRealization`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **An Ara realization restricted to `A_fin` is a cellular realization** (gap review B §2(a)).
For a left adjoint `L` of `Π_R`: `L` sends `I j` to `∂𝔻 j ⟶ 𝔻 j` up to isomorphism (two
hemispheres glued along the equator), hence finitely cellular models to finite cell complexes and
finite boundary-cell maps to relative finite cell complexes; it preserves initial objects and
pushouts as a left adjoint; and it sends `J j` to the hemisphere inclusion `𝔻 j ⟶ 𝔻 (j+1)`, so by
Cor. 4.1 (trivial cofibrations with cofibrant domain are retracts of relative `J`-cell maps) and
Brown's factorization in `A_fin` it sends weak equivalences to homotopy equivalences. -/
theorem cellularRealization {C : GlobularTheory.{u}} (hC : C.IsCoherator) (R : OAIRealization C)
    (L : C.Model ⥤ TopCat.{u}) (adj : L ⊣ R.Pi) :
    IsCellularRealization (Afin.ι hC ⋙ L) := by apply @_root_.HomotopyHypothesis.Blueprint.Packages.cellularRealization_proof <;> assumption
