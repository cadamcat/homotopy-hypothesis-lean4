import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Interfaces.Disk0
import HomotopyHypothesis.Assembly.Theorem.Assembly

/-!
# `afin_isCylinderCoherator`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **`A_fin` is a cylinder coherator** (H:3143–3177, Cor. 5.3.12; OA:04:198–226). To be proved
from `afin_isCylinderCategory`, `disk0_isHTerminal`, `afin_isCofibrantAt` and
`afin_liftsAtHTerminal` through the general reduction of Henry Lemma 5.3.11 / Cor. 5.3.12
(sections of `A^{o} ⟶ A`, H:2682 Prop. 4.4.4). -/
theorem afin_isCylinderCoherator {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    IsCylinderCoherator.{u + 1, u} (Afin C hC) (disk0 hC) := _root_.HomotopyHypothesis.Assembly.Theorem.afin_isCylinderCoherator_proof ..
