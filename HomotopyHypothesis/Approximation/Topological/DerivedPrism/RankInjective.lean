import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Code
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.CodeInjective
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Rank

/-!
# `rank_injective`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrism`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

namespace PV

variable {k : ℕ}

theorem rank_injective : Function.Injective (rank : PV k → ℕ ×ₗ ℕ ×ₗ ℕ) := by
  intro a b h
  cases a <;> cases b <;> simp_all [rank, Fin.ext_iff]
  exact DV.code_injective h.2
