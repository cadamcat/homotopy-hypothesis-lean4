import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV

/-!
# `dprismComplex`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrism`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

namespace PV

variable {k : ℕ}

end PV

open PV

/-- The derived cylinder over `Δ_k`, as an ordered simplicial complex. -/
def dprismComplex (k : ℕ) : Complex (PV k) where
  S A := (∀ S, mid S ∈ A → S.Nonempty) ∧
    (∀ S S', mid S ∈ A → mid S' ∈ A → S ⊆ S' ∨ S' ⊆ S) ∧
    (∀ i S, top i ∈ A → mid S ∈ A → i ∈ S)
  down _ _ hAB hB :=
    ⟨fun S h => hB.1 S (hAB h), fun S S' h h' => hB.2.1 S S' (hAB h) (hAB h'),
      fun i S h h' => hB.2.2 i S (hAB h) (hAB h')⟩
