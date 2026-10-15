import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Interfaces.Disk0
import HomotopyHypothesis.Cylinder.FiniteCellCategory.DiskZero

/-!
# `disk0_isHTerminal`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **`D₀` is h-terminal** (OA:04:205–210, from Prop. `shape-contractible`, OA:02:183: `D₀ → 1` is
`I`-injective, so every map to `D₀` extends along every finite boundary-cell map). -/
theorem disk0_isHTerminal {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    IsHTerminal (disk0 hC) := _root_.HomotopyHypothesis.Blueprint.Packages.disk0_isHTerminal_proof ..
