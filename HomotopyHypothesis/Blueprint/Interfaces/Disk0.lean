import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Interfaces.DiskFinitelyCellular

/-!
# `disk0`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- The marked object `D₀` of `A_fin`. -/
abbrev disk0 {C : GlobularTheory.{u}} (hC : C.IsCoherator) : Afin C hC :=
  Afin.disk0 hC (disk_finitelyCellular C 0)
