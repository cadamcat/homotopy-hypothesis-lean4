import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map

/-!
# `map_comp`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

theorem map_comp {m : ℕ} (t : Fin (k + 1) → Fin (l + 1)) (t' : Fin (l + 1) → Fin (m + 1)) :
    map (t' ∘ t) = map t' ∘ map t := by
  funext a
  cases a <;> simp [map, Finset.image_image]
