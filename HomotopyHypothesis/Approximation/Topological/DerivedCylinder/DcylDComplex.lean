import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57

/-!
# `dcylDComplex`

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

/-- The derived double cylinder of a vertex map `v : [n] ⟶ [m]`, as an ordered simplicial
complex. -/
def dcylDComplex {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) : Complex (DV n m) where
  S A := (∀ S, mid S ∈ A → S.Nonempty) ∧
    (∀ S S', mid S ∈ A → mid S' ∈ A → S ⊆ S' ∨ S' ⊆ S) ∧
    (∀ i c, top i ∈ A → bot c ∈ A → False) ∧
    (∀ i S, top i ∈ A → mid S ∈ A → i ∈ S) ∧
    (∀ c S, bot c ∈ A → mid S ∈ A → ∃ k ∈ S, v k = c)
  down _ _ hAB hB :=
    ⟨fun S h => hB.1 S (hAB h), fun S S' h h' => hB.2.1 S S' (hAB h) (hAB h'),
      fun i c h h' => hB.2.2.1 i c (hAB h) (hAB h'),
      fun i S h h' => hB.2.2.2.1 i S (hAB h) (hAB h'),
      fun c S h h' => hB.2.2.2.2 c S (hAB h) (hAB h')⟩
