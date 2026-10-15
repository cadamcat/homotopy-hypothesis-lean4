import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Interfaces.Disk0
import HomotopyHypothesis.FiniteCategory.Lifting.Proofs

/-!
# `afin_isCofibrantAt`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **Relative cofibrancy of `F_* ⟶ A_fin`** (H:3091–3108, Prop. 5.3.7, first part; with H:2050,
Def. 4.1.3). -/
theorem afin_isCofibrantAt {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    IsCofibrantAt.{u + 1, u} (Afin C hC) (disk0 hC) := by apply @_root_.HomotopyHypothesis.Blueprint.Packages.afin_isCofibrantAt_proof <;> assumption
