import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Code
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.CodeInjective
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Rank

/-!
# `rank_injective`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedCylinder`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

namespace DV

variable {n m : ℕ}

theorem rank_injective : Function.Injective (rank : DV n m → ℕ ×ₗ ℕ ×ₗ ℕ) := by
  intro a b h
  cases a <;> cases b <;> simp_all [rank, Fin.ext_iff]
  exact code_injective h.2
