import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Interfaces.Disk0
import HomotopyHypothesis.FiniteCategory.Lifting.Proofs

/-!
# `afin_liftsAtHTerminal`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **Lifting along the free construction** (H:3114–3126, Lemma 5.3.9, with gap review A's
clarification on composite units): morphisms out of `A_fin` lift along pre-fibrations at
h-terminal objects, by induction along the cellular presentation of the coherator. -/
theorem afin_liftsAtHTerminal {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    LiftsAtHTerminal.{u + 1, u} (Afin C hC) (disk0 hC) := by apply @_root_.HomotopyHypothesis.Blueprint.Packages.afin_liftsAtHTerminal_proof <;> assumption
