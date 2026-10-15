import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57

/-!
# `dcylDBoundaryComplex`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedCylinder`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

namespace DV

variable {n m : ℕ}

end DV

open DV

/-- The boundary of the derived double cylinder: the bottom `Δ_m` and the cylinders over the
proper faces `[n] ∖ {i}`. -/
def dcylDBoundaryComplex {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) : Complex (DV n m) where
  S A := (dcylDComplex v).S A ∧
    ((∀ a ∈ A, ∃ c, a = bot c) ∨
      ∃ i : Fin (n + 1), top i ∉ A ∧ ∀ S, mid S ∈ A → i ∉ S)
  down A B hAB hB := by
    refine ⟨(dcylDComplex v).down hAB hB.1, ?_⟩
    rcases hB.2 with h | ⟨i, hi, h⟩
    · exact Or.inl fun a ha => h a (hAB ha)
    · exact Or.inr ⟨i, fun h' => hi (hAB h'), fun S hS => h S (hAB hS)⟩
