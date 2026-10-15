import HomotopyHypothesis.Approximation.Topological.Complex

/-!
# `code`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedCylinder`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

namespace DV

variable {n m : ℕ}

/-- An injective code of a face of `Δ_n` (its binary expansion). -/
def code (S : Finset (Fin (n + 1))) : ℕ := Finset.equivBitIndices.symm (S.map Fin.valEmbedding)
