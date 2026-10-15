import HomotopyHypothesis.Approximation.Topological.Complex

/-!
# `DV`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedCylinder`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- Vertices of the derived double cylinder over `Δ_n` with bottom `Δ_m`. -/
inductive DV (n m : ℕ) where
  | top (i : Fin (n + 1))
  | mid (S : Finset (Fin (n + 1)))
  | bot (c : Fin (m + 1))
