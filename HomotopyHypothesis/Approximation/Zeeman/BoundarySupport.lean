import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.SimplexSupport
/-!
# Strict dimension decrease on the boundary

A simplex point with a zero coordinate factors through a face of strictly
smaller dimension. An everywhere-nonzero representative cannot surject
onto the missing coordinate.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A boundary point has a nonzero-weight representative in a proper face. -/
theorem exists_nonzero_proper_face {n : ℕ} (t : StdSimplex ℝ (Fin (n + 1)))
    (hz : ∃ i, t.weights i = 0) :
    ∃ (m : ℕ) (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n)
      (p : StdSimplex ℝ (Fin (m + 1))),
      m < n ∧ StdSimplex.map θ.hom.toOrderHom p = t ∧ ∀ i, p.weights i ≠ 0 := by
  obtain ⟨m, θ, p, hp, hnonzero⟩ := exists_nonzero_face t
  have hinj := SimplexCategory.mono_iff_injective.mp θ.property
  have hsurj : ¬ Function.Surjective θ.hom.toOrderHom := by
    intro h
    obtain ⟨i, hi⟩ := hz
    obtain ⟨j, hj⟩ := h i
    apply hnonzero j
    exact (Finsupp.mapDomain_apply_of_injective hinj p.weights j).symm.trans
      ((congrArg (fun r : StdSimplex ℝ (Fin (n + 1)) =>
        r.weights (θ.hom.toOrderHom j)) hp).trans
          ((congrArg t.weights hj).trans hi))
  have hc := Fintype.card_lt_of_injective_not_surjective θ.hom.toOrderHom hinj hsurj
  simp only [Fintype.card_fin] at hc
  exact ⟨m, θ, p, by omega, hp, hnonzero⟩

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_nonzero_proper_face
