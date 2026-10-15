import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV

/-!
# `dprismBdryComplex`

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

/-- The derived end `Δ_k'` together with the derived cylinders over the proper faces of `Δ_k`. -/
def dprismBdryComplex (k : ℕ) : Complex (PV k) where
  S A := (dprismComplex k).S A ∧
    ((∀ i, top i ∉ A) ∨ ∃ i : Fin (k + 1), top i ∉ A ∧ ∀ S, mid S ∈ A → i ∉ S)
  down A B hAB hB := by
    refine ⟨(dprismComplex k).down hAB hB.1, ?_⟩
    rcases hB.2 with h | ⟨i, hi, h⟩
    · exact Or.inl fun i h' => h i (hAB h')
    · exact Or.inr ⟨i, fun h' => hi (hAB h'), fun S hS => h S (hAB hS)⟩
