import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Realization.Functor.Realization

/-!
# `exists_realization`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **Realizations exist** (A:819, Prop. `coh_weak_init`; A:683, contractibility of `Top`).
Topological globular sums of standard globes are contractible; hence every admissible pair of maps
`Dⁿ ⇉ |S|` extends over `Dⁿ⁺¹`, and a realization is built along the cellular presentation of the
coherator, using the universal property of each free extension and of the colimit. -/
theorem exists_realization (C : GlobularTheory.{u}) (hC : C.IsCoherator) :
    Nonempty (OAIRealization C) := by apply @_root_.HomotopyHypothesis.Realization.Functor.exists_realization_proof <;> assumption
