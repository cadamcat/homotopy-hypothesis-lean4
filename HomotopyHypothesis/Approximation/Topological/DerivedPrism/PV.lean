import HomotopyHypothesis.Approximation.Topological.CylinderGlue

/-!
# `PV`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrism`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- Vertices of the derived cylinder over `Δ_k`. -/
inductive PV (k : ℕ) where
  | top (i : Fin (k + 1))
  | mid (S : Finset (Fin (k + 1)))
